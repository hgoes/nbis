module TypeDesc where

import Foreign
import LLVM.FFI.Type as FFI
import LLVM.FFI.OOP as FFI
import LLVM.FFI.StringRef as FFI

data TypeDesc
     = VoidType
     | HalfType
     | FloatType
     | DoubleType
     | X86_FP80Type
     | FP128Type
     | PPC_FP128Type
     | X86_MMXType
     | LabelType
     | MetadataType
     | IntegerType Integer
     | FunctionType TypeDesc [TypeDesc] Bool
     | StructType (Either String [TypeDesc])
     | ArrayType Integer TypeDesc
     | PointerType TypeDesc
     | VectorType Integer TypeDesc
     deriving (Eq,Ord,Show)

reifyType :: Ptr Type -> IO TypeDesc
reifyType tp
  = mkCheck
    [(isVoidType,return VoidType)
    ,(isHalfType,return HalfType)
    ,(isFloatType,return FloatType)
    ,(isDoubleType,return DoubleType)
    ,(isX86_FP80Type,return X86_FP80Type)
    ,(isFP128Type,return FP128Type)
    ,(isPPC_FP128Type,return PPC_FP128Type)
    ,(isX86_MMXType,return X86_MMXType)
    ,(isLabelType,return LabelType)
    ,(isMetadataType,return MetadataType)
    ,(const True,
      mkSwitch
      [do
          case castDown tp of
            Nothing -> return Nothing
            Just itp' -> do
              w <- getBitWidth itp'
              return $ Just $ IntegerType w
      ,do
          case castDown tp of
            Nothing -> return Nothing
            Just ftp' -> do
              var <- functionTypeIsVarArg ftp'
              rtp <- functionTypeGetReturnType ftp' >>= reifyType
              sz <- functionTypeGetNumParams ftp'
              tps <- mapM (\i -> functionTypeGetParamType ftp' i >>= reifyType) [0..(sz-1)]
              return $ Just $ FunctionType rtp tps var
      ,do
          case castDown tp of
            Nothing -> return Nothing
            Just stp' -> do
              hasN <- structTypeHasName stp'
              if hasN
                then (do
                         name <- structTypeGetName stp'
                         name' <- stringRefData name
                         return $ Just $ StructType (Left name'))
                else (do
                         sz <- structTypeGetNumElements stp'
                         tps <- mapM (\i -> structTypeGetElementType stp' i >>= reifyType) [0..(sz-1)]
                         return $ Just $ StructType (Right tps))
      ,do
          case castDown tp of
            Nothing -> return Nothing
            Just atp' -> do
              sz <- arrayTypeGetNumElements atp'
              eltp <- sequentialTypeGetElementType atp' >>= reifyType
              return $ Just $ ArrayType sz eltp
      ,do
          case castDown tp of
            Nothing -> return Nothing
            Just ptp' -> do
              eltp <- sequentialTypeGetElementType (ptp'::Ptr PointerType) >>= reifyType
              return $ Just $ PointerType eltp
      ,do
          case castDown tp of
            Nothing -> return Nothing
            Just vtp' -> do
              eltp <- sequentialTypeGetElementType vtp' >>= reifyType
              sz <- vectorTypeGetNumElements vtp'
              return $ Just $ VectorType sz eltp
      ])
    ]
  where
    mkCheck :: [(Ptr Type -> Bool,IO a)] -> IO a
    mkCheck ((chk,act):rest) 
      = if chk tp 
        then act
        else mkCheck rest
    mkSwitch :: [IO (Maybe a)] -> IO a
    mkSwitch (act:acts) = do
      res <- act
      case res of
        Just r -> return r
        Nothing -> mkSwitch acts
    mkSwitch [] = do
      typeDump tp
      error "Unknown type"