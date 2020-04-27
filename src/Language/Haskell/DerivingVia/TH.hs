{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Haskell.DerivingVia.TH (deriveViaMany) where

import Control.Applicative
import Control.Monad
import Data.Coerce
import Data.Data

import Language.Haskell.TH as TH

deriveViaMany :: TypeQ -> Q [Dec]
deriveViaMany spec = do
  -- Check for language extensions
  let requiredExts = [ScopedTypeVariables, TypeApplications, InstanceSigs]
  missingExt <- or <$> traverse isExtMissing requiredExts
  when missingExt $ fail $
    "Missing language extensions, aborting. The required extensions are:\n  " <> show requiredExts

  -- Parse input, call worker
  spec >>= \case
    ForallT vars ctx ((decompTyApp -> Just (ConT cls1, args1)) :-> (decompTyApp -> Just (ConT cls2, args2)))
      | cls1 == cls2
      -> mkDerivedInstVia vars ctx cls1 args1 args2
    ((decompTyApp -> Just (ConT cls1, args1)) :-> (decompTyApp -> Just (ConT cls2, args2)))
      | cls1 == cls2
      -> mkDerivedInstVia [] [] cls1 args1 args2
    _ -> fail $ unlines
      [ "deriveViaMany: incorrect deriving specification!"
      , "it should look like this:"
      , "  forall <vars>. <context> => <head of instance to re-use> -> <head of instance to derive>"
      , "or if there are no type variables and the context is empty, you may simplify to:"
      , "  <head of instance to re-use> -> <head of instance to derive>"
      ]
  where
    isExtMissing :: Extension -> Q Bool
    isExtMissing ext = do
      enabled <- isExtEnabled ext
      unless enabled $ reportError $
        "The language extension " <> show ext <> " is required for the spliced code to work properly.\n"
        <> "Make sure it is enabled."
      pure (not enabled)


pattern (:->) :: Type -> Type -> Type
pattern a :-> b = AppT (AppT ArrowT a) b

decompTyApp :: Type -> Maybe (Type, [Type])
decompTyApp = fmap (fmap reverse) . go
  where
    go (AppT f x) = case go f of
      Just (f', xs) -> Just (f', x : xs)
      Nothing -> Just (f, [x])
    go _ = Nothing

mkDerivedInstVia :: [TyVarBndr] -> [Type] -> Name -> [Type] -> [Type] -> Q [Dec]
mkDerivedInstVia tyvars cxt tcName viaTypes targetTypes = do
  ClassI (ClassD _ _ classTyvars _ members) _ <- reify tcName
  when (length classTyvars /= length viaTypes) $ fail
    "mkDerivedInstVia: number of typeclass parameters for target class does not match number of parameters in via instance"
  when (length classTyvars /= length targetTypes) $ fail
    "mkDerivedInstVia: number of typeclass parameters for target class does not match number of parameters in desired instance"

  coerceFun <- [| coerce |]

  let
    env = zip (tyvarName <$> classTyvars) targetTypes
    mkViaDecl (SigD name (ForallT memberTyvars cxt tysig)) =
      [ SigD name (ForallT memberTyvars (substTyvars env <$> cxt) (substTyvars env tysig))
      , ValD (VarP name) (NormalB (coerceFun `AppE` mkVisibleTyApp (VarE name) (viaTypes ++ map (VarT . tyvarName) memberTyvars))) []
      ]
    mkViaDecl (SigD name tysig) =
      [ ValD (VarP name) (NormalB (coerceFun `AppE` mkVisibleTyApp (VarE name) viaTypes)) []
      ]
    mkViaDecl _ = []
  
  pure [InstanceD Nothing cxt (mkAppliedType (ConT tcName) targetTypes) (concatMap mkViaDecl members)]

mkCoercibleConstraint :: (Type, Type) -> Q Type
mkCoercibleConstraint (f, t) = [t| Coercible $(pure f) $(pure t) |]

mkAppliedType :: Type -> [Type] -> Type
mkAppliedType = foldl AppT

substTyvars :: [(Name, Type)] -> Type -> Type
substTyvars env = gmapT go
  where
    go :: forall t. Data t => t -> t
    go subterm
      | Just Refl <- eqT @t @Type
      = case subterm of
          VarT nm
            | Just ty <- lookup nm env
            -> ty
          InfixT x op y
            | Just ty <- lookup op env
            -> mkAppliedType ty [x,y]
          _ -> gmapT go subterm
      | otherwise = subterm

tyvarName :: TyVarBndr -> Name
tyvarName (PlainTV nm) = nm
tyvarName (KindedTV nm _) = nm

mkVisibleTyApp :: Exp -> [Type] -> Exp
mkVisibleTyApp = foldl AppTypeE