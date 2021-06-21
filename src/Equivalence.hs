module Equivalence (
    eclasses
  ) where


import Control.Monad ( (=<<) )
import Data.Equivalence.Monad (runEquivM, equate, desc, classes)

-----------------------------------------------------------

-- | Given a list of unordered equivalence pairs, return the eclasses.
--   Equivalently: Given unordered pairs of a relation, return the reflexive symmetric transitive closure
eclasses :: (Ord a) => [(a, a)] -> [[a]]
eclasses eqs = runEquivM (:[]) (++) $ do
  mapM (\(x, y) -> equate x y) eqs
  mapM desc =<< classes
