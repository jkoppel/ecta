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

invSkel :: Map.Map Text [TypeSkeleton]
invSkel = invertMap hoogleComponents

prettyMatch :: Term -> [Text]
prettyMatch (Term (Symbol t) _) = map (M.<> tsk) $ invGroupMapping Map.! t
  where tsk = pack $ " :: " ++ unwords (map show $ invSkel Map.! t)


ectaPlugin :: TypedHole -> TcM [HoleFit]
ectaPlugin TyH{..} | Just hole <- tyHCt,
                     ty <- ctPred hole = do
      case ghcTypeToSkeleton ty of
         Just t | resNode <- typeToFta t -> do
             let res = getAllTerms $ refold $ reduceFully $ filterType pAnyFunc resNode
             return $ map (RawHoleFit . text . show ) $ concatMap (prettyMatch . prettyTerm) res
         _ ->  do liftIO $ putStrLn $  "Could not skeleton `" ++ showSDocUnsafe (ppr ty) ++"`"
                  return []
