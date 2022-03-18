{-# LANGUAGE RecordWildCards #-}
module CCTP.Plugin (plugin) where

import GhcPlugins
import TcHoleErrors
import TcHoleFitTypes
import TcRnTypes
import Constraint

import CCTP.Utils

import Application.TermSearch.Dataset
import Application.TermSearch.Type
import Application.TermSearch.TermSearch
import Data.ECTA
import Data.ECTA.Term

import qualified Data.Map as Map
import Data.Text (pack, unpack, Text)
import Data.Maybe (fromMaybe)
import Data.Tuple (swap)
import Data.List (sortOn, groupBy)
import Data.Function (on)
import qualified Data.Monoid as M
import MonadUtils (concatMapM)

plugin :: Plugin
plugin =
  defaultPlugin
    { holeFitPlugin = \_ ->
        Just $
          fromPureHFPlugin
            ( HoleFitPlugin
                { candPlugin = \_ c -> return [],
                  fitPlugin = \h _ -> ectaPlugin h
                }
            )
    }


pAnyFunc :: Node
pAnyFunc = Node (map ($ 1) hoogleComps)


invertMap :: Ord b => Map.Map a b -> Map.Map b [a]
invertMap = toMap . groupBy ((==) `on` fst) . sortOn fst . map swap . Map.toList
  where toMap = Map.fromList . map (\((a,r):rs) -> (a,r:map snd rs))

invGroupMapping :: Map.Map Text [Text]
invGroupMapping = invertMap groupMapping

invSkel :: Map.Map Text TypeSkeleton
invSkel = Map.map head $ invertMap hoogleComponents

prettyMatch :: Term -> TcM [Text]
prettyMatch (Term (Symbol t) _) =
  do ty <- skeletonToType tsk
     let str = case ty of
               Just t  -> pack (" :: " ++  showSDocUnsafe (ppr t))
               _ -> pack (" :: " ++ show tsk)
     return $ map (M.<> str) terms
  where tsk = invSkel Map.! t
        terms = invGroupMapping Map.! t


ectaPlugin :: TypedHole -> TcM [HoleFit]
ectaPlugin TyH{..} | Just hole <- tyHCt,
                     ty <- ctPred hole = do
      case typeToSkeleton ty of
         Just t | resNode <- typeToFta t -> do
             let res = getAllTerms $ refold $ reduceFully $ filterType pAnyFunc resNode
             ppterms <- concatMapM (prettyMatch . prettyTerm) res
             return $ map (RawHoleFit . text . unpack) ppterms
         _ ->  do liftIO $ putStrLn $  "Could not skeleton `" ++ showSDocUnsafe (ppr ty) ++"`"
                  return []
