module Main where

import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PackageIndex
import Distribution.InstalledPackageInfo as IPI
import Distribution.PackageDescription as PD hiding (description)

import Text.Regex

adaptHooks :: UserHooks -> UserHooks
adaptHooks hooks = hooks { confHook = \pd flags -> do
                              lbi <- confHook hooks pd flags
                              let [(_,[llvm_pkg])] = lookupPackageName (installedPkgs lbi)
                                                     (PackageName "bindings-llvm")
                                  vers_regex = mkRegex "%LLVM_VERSION=(.*)%"
                                  Just [vstr] = matchRegex vers_regex (description llvm_pkg)
                                  version = read vstr
                                  lbi' = adaptLocalBuildInfo version (IPI.ldOptions llvm_pkg) lbi
                              return lbi'
                         }

adaptLocalBuildInfo :: Version -> [String] -> LocalBuildInfo -> LocalBuildInfo
adaptLocalBuildInfo llvm_v ldopts lbi
  = lbi { localPkgDescr = (localPkgDescr lbi)
                          { executables = fmap (\exe -> exe { buildInfo = adaptBuildInfo llvm_v ldopts (buildInfo exe)
                                                            }) (executables $ localPkgDescr lbi)
                          }
        }

adaptBuildInfo :: Version -> [String] -> BuildInfo -> BuildInfo
adaptBuildInfo llvm_v ld_opts bi = bi { cppOptions = ["-DHS_LLVM_VERSION="++versionToDefine llvm_v]++
                                                     cppOptions bi
                                      , PD.ldOptions = ld_opts++(PD.ldOptions bi)
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