{-# LANGUAGE TemplateHaskell #-}

module Bears.TH where

import Control.Monad (replicateM)
import Language.Haskell.TH

deriveRow :: Name -> Q [Dec]
deriveRow name = do
    info <- reify name
    case info of
        TyConI (DataD _ typeName typeVarBinders _ [con] _) -> do
            let (conName, numFields) = case con of
                    NormalC conName fields -> (conName, length fields)
                    RecC    conName fields -> (conName, length fields)
                    InfixC  _ conName _    -> (conName, 2            )

            let typeVars = do
                    typeVarBinder <- typeVarBinders
                    let typeVar = case typeVarBinder of
                            PlainTV  typeVar   -> typeVar
                            KindedTV typeVar _ -> typeVar
                    return typeVar

            let nullaryDefinition methodName =
                    let rs = replicate numFields (VarE methodName)
                        definition =
                            ValD
                                (VarP methodName)
                                (NormalB (foldl AppE (ConE conName) rs))
                                []

                    in  definition

            x <- newName "n"
            let liftDefinition methodName =
                    let rs = replicate numFields (AppE (VarE methodName) (VarE x))
                        definition =
                            FunD
                                methodName
                                [ Clause
                                    [ VarP x
                                    ]
                                    (NormalB (foldl AppE (ConE conName) rs))
                                    []
                                ]
                    in  definition

            xs <- replicateM numFields (newName "x")
            let unaryDefinition methodName =
                    let rs = do
                            x <- xs
                            let method = VarE methodName
                            return (AppE method (VarE x))
                        definition =
                            FunD
                                methodName
                                [ Clause
                                    [ ConP conName (map VarP xs)
                                    ]
                                    (NormalB (foldl AppE (ConE conName) rs))
                                    []
                                ]
                    in  definition

            xsL <- replicateM numFields (newName "xL")
            xsR <- replicateM numFields (newName "xR")
            let binaryDefinition methodName =
                    let rs = do
                            (xL, xR) <- zip xsL xsR
                            let method = VarE methodName
                            return (AppE (AppE method (VarE xL)) (VarE xR))
                        definition =
                            FunD
                                methodName
                                [ Clause
                                    [ ConP conName (map VarP xsL)
                                    , ConP conName (map VarP xsR)
                                    ]
                                    (NormalB (foldl AppE (ConE conName) rs))
                                    []
                                ]
                    in  definition

            let makeInstance className definitions =
                    let c = ConT className
                        constraints = do
                            typeVar <- typeVars
                            return (AppT c (VarT typeVar))
                        typeVars' = map VarT typeVars
                        instanceHead =
                            AppT c (foldl AppT (ConT typeName) typeVars')
                    in  InstanceD Nothing constraints instanceHead definitions

            let app e1 e2 = AppE (AppE (VarE '(<*>)) e1) e2
            return
                [ makeInstance ''Monoid
                    [ nullaryDefinition 'mempty
                    , binaryDefinition 'mappend
                    ]
                , makeInstance ''Num
                    [ liftDefinition 'fromInteger
                    , unaryDefinition 'abs
                    , unaryDefinition 'negate
                    , unaryDefinition 'signum
                    , binaryDefinition '(+)
                    , binaryDefinition '(*)
                    , binaryDefinition '(-)
                    ]
                , makeInstance ''Fractional
                    [ liftDefinition 'fromRational
                    , unaryDefinition 'recip
                    , binaryDefinition '(/)
                    ]
                , makeInstance ''Floating
                    [ nullaryDefinition 'pi
                    , unaryDefinition 'exp
                    , unaryDefinition 'log
                    , unaryDefinition 'sqrt
                    , unaryDefinition 'sin
                    , unaryDefinition 'cos
                    , unaryDefinition 'tan
                    , unaryDefinition 'asin
                    , unaryDefinition 'acos
                    , unaryDefinition 'atan
                    , unaryDefinition 'sinh
                    , unaryDefinition 'cosh
                    , unaryDefinition 'tanh
                    , unaryDefinition 'asinh
                    , unaryDefinition 'acosh
                    , unaryDefinition 'atanh
                    , binaryDefinition '(**)
                    , binaryDefinition 'logBase
                    ]
                , FunD
                    (mkName ("transpose" ++ nameBase typeName))
                    [ Clause
                        [ ConP conName (map VarP xs)
                        ]
                        (NormalB
                            (foldl app (AppE (VarE 'pure) (ConE conName)) (map VarE xs))
                        )
                        []
                    ]
                ]
        _ -> return []
