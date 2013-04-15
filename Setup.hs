module Main where

import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PackageIndex
import Distribution.InstalledPackageInfo
import Distribution.PackageDescription hiding (description)

import Text.Regex

adaptHooks :: UserHooks -> UserHooks
adaptHooks hooks = hooks { confHook = \pd flags -> do
                              lbi <- confHook hooks pd flags
                              let [(_,[llvm_pkg])] = lookupPackageName (installedPkgs lbi)
                                                     (PackageName "bindings-llvm")
                                  vers_regex = mkRegex "%LLVM_VERSION=(.*)%"
                                  Just [vstr] = matchRegex vers_regex (description llvm_pkg)
                                  version = read vstr
                                  lbi' = adaptLocalBuildInfo version lbi
                              return lbi'
                         }

adaptLocalBuildInfo :: Version -> LocalBuildInfo -> LocalBuildInfo
adaptLocalBuildInfo llvm_v lbi
  = lbi { localPkgDescr = (localPkgDescr lbi)
                          { executables = fmap (\exe -> exe { buildInfo = adaptBuildInfo llvm_v (buildInfo exe)
                                                            }) (executables $ localPkgDescr lbi)
                          }
        }

adaptBuildInfo :: Version -> BuildInfo -> BuildInfo
adaptBuildInfo llvm_v bi = bi { cppOptions = ["-DHS_LLVM_VERSION="++versionToDefine llvm_v]++
                                             cppOptions bi
                              }

versionToDefine :: Version -> String
versionToDefine v = branch (versionBranch v)
  where
    branch (x:xs) = show x ++ (concat $ 
                               fmap (\x' -> if x'<10
                                            then "0"++show x'
                                            else show x'
                                    ) xs)

main = defaultMainWithHooks $ adaptHooks simpleUserHooks