{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

module CacheProfilingSpec ( spec ) where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Test.QuickCheck.Monadic

import Data.ECTA
import TermSearch

import Test.Generators.ECTA

-----------------------------------------------------------------


--------------------------------------------------------------
----------------------------- Main ---------------------------
--------------------------------------------------------------

#ifdef PROFILE_CACHES
spec :: Spec
spec = do

  describe "Broken test: same result before and after resetting caches" $
    -- TODO: Fix the parse error that occurs from uncommenting this
    {-
    it "QuickCheck property" $
      property $ \n -> monadicIO $ do
                         let n1 = reducePartially n
                         nodeCount n1 `seq` run resetAllEctaCaches
                         let n2 = reducePartially n
                         assert $ n1 == n2
    -}

{-
    it "Fixed input" $
      -- Easier to do this than to figure out how to do IO in pure HSpec
      property $ \() -> monadicIO $ do
                          let n = size2
                          let n1 = reducePartially n
                          nodeCount n1 `seq` run resetAllEctaCaches_BrokenDoNotUse
                          let n2 = reducePartially n
                          assert $ n1 == n2
-}
    return ()

#else
spec :: Spec
spec = return ()
#endif