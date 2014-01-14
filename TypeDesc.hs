{-# LANGUAGE CPP #-}
module TypeDesc where

import Foreign
import LLVM.FFI.Type as FFI
import LLVM.FFI.OOP as FFI
import LLVM.FFI.StringRef as FFI
import Data.List as List
import Data.Map as Map

data TypeDesc
     = VoidType
#if HS_LLVM_VERSION >= 301
     | HalfType
#endif
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
#if HS_LLVM_VERSION >= 301
    ,(isHalfType,return HalfType)
#endif
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

indexType :: Map String [TypeDesc] 
             -> TypeDesc -> [Either Integer a] -> TypeDesc
indexType _ tp [] = tp
indexType structs (PointerType tp) (_:idx) = indexType' tp idx
  where
    indexType' tp [] = tp
    indexType' (StructType descr) (Left i:is)
      = let tps = case descr of
              Left name -> case Map.lookup name structs of
                Just res -> res
              Right res -> res
        in indexType' (List.genericIndex tps i) is
    indexType' (ArrayType _ tp) (_:is)
      = indexType' tp is
indexType _ tp idx = error $ "Can't index type "++show tp

typeWidth :: Integer -> Map String [TypeDesc] -> TypeDesc -> Integer
typeWidth _ _ (IntegerType w)
  | w `mod` 8 == 0 = w `div` 8
  | otherwise = error $ "typeWidth called for "++show w
typeWidth pw _ (PointerType _) = pw
typeWidth pw structs (ArrayType n tp) = n*(typeWidth pw structs tp)
typeWidth pw structs (StructType (Right tps)) = sum (fmap (typeWidth pw structs) tps)
typeWidth pw structs (StructType (Left name)) = case Map.lookup name structs of
  Just tps -> sum (fmap (typeWidth pw structs) tps)
typeWidth _ _ tp = error $ "No typeWidth for "++show tp

bitWidth :: Integer -> Map String [TypeDesc] -> TypeDesc -> Integer
bitWidth _ _ (IntegerType w) = w
bitWidth pw _ (PointerType _) = pw
bitWidth pw structs (ArrayType n tp) = n*(bitWidth pw structs tp)
bitWidth pw structs (StructType (Right tps)) = sum (fmap (bitWidth pw structs) tps)
bitWidth pw structs (StructType (Left name)) = case Map.lookup name structs of
  Just tps -> sum (fmap (bitWidth pw structs) tps)
bitWidth _ _ tp = error $ "No bitWidth for "++show tp

bitWidth' :: TypeDesc -> Integer
bitWidth' = bitWidth
            (error "bitWidth' is not implemented for pointer types")
            (error "bitWidth' is not implemented for struct types")
