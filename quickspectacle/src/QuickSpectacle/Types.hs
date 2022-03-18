{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module QuickSpectacle.Types where
import Data.Dynamic
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Map as Map
import GHC.Base (Any)
import Application.TermSearch.Type (TypeSkeleton(..))

import Data.Typeable
import Data.Char (toLower)
import Data.Text (Text)
import qualified Data.Text as T

-- Types supported by ECTA
newtype A = A Any deriving Typeable
newtype B = B Any deriving Typeable
newtype C = C Any deriving Typeable
newtype D = D Any deriving Typeable
newtype Acc = Acc Any deriving Typeable


typeRepToTypeSkeleton :: TypeRep -> TypeSkeleton
typeRepToTypeSkeleton tr
     | [] <- tra,
       ltc <- map toLower tcn,
       ltc `elem` ["a", "b", "c","d", "acc"]
       = TVar (T.pack ltc)
     | tcn == "->",
       [arg,ret] <- args
     = TFun arg ret
     | otherwise = TCons (T.pack tcn) args
  where (tc, tra) = splitTyConApp tr
        tcn = tyConName tc
        args = map typeRepToTypeSkeleton tra


type Sig = Map Text Dynamic


con :: Typeable a => Text -> a -> Sig
con name fun = Map.singleton name (toDyn fun)

