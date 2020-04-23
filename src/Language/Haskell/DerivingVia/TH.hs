module Language.Haskell.DerivingVia.TH (deriveViaMany) where

import Control.Applicative
import Control.Monad

import Language.Haskell.TH as TH

deriveViaMany :: Name -> [(TypeQ, TypeQ)] -> Q [Dec]
deriveViaMany tcName qpairs = do
  when (null qpairs) $
    fail $ "deriveViaMany: type mapping must be non-empty"
  pairs <- traverse (\(f, t) -> liftA2 (,) f t) qpairs
  info <- reify tcName
  case info of
    ClassI (ClassD cxt name tyvars fundeps members) _iistances ->
      pure <$> mkDerivedInstVia cxt name tyvars fundeps members pairs
    _ -> fail $ "deriveViaMany: expected a typeclass, but " <> show tcName <> " does not refer to a (visible) type class."

mkDerivedInstVia :: Cxt -> Name -> [TyVarBndr] -> [FunDep] -> [Dec] -> [(Type, Type)] -> Q Dec
mkDerivedInstVia cxt name tyvars fundep members pairs = fail "mkDerivedInstVia: TODO"