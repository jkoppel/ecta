{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
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
import TcRnMonad (writeTcRef, newTcRef, readTcRef, mapMaybeM)
import TcEnv (tcLookupId, tcLookupIdMaybe)

plugin :: Plugin
plugin =
  defaultPlugin
    { holeFitPlugin = \opts ->
        Just $
          HoleFitPluginR {
            hfPluginInit = newTcRef [],
            hfPluginRun = \ref ->
                  ( HoleFitPlugin
                   { candPlugin = \_ c -> writeTcRef ref c >> return [],
                     fitPlugin = \h _ -> readTcRef ref >>= ectaPlugin opts h
                                  }
                              ),
            hfPluginStop = const (return ())
          }
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

prettyMatch :: Map.Map Text TypeSkeleton -> Map.Map Text [Text] -> Term -> TcM [Text]
prettyMatch skels groups (Term (Symbol t) _) =
  do ty <- skeletonToType tsk
     let str = case ty of
               Just t  -> pack (" :: " ++  showSDocUnsafe (ppr t))
               _ -> pack (" :: " ++ show tsk)
     return $ map (M.<> str) terms
  where tsk = skels Map.! t
        terms = groups Map.! t

candsToComps :: [HoleFitCandidate] -> TcM [(Text, TypeSkeleton)]
candsToComps = mapMaybeM candToTN
  where candToTN :: HoleFitCandidate -> TcM (Maybe (Text, TypeSkeleton))
        candToTN cand =
              fmap (fmap (nm,) . (>>= typeToSkeleton)) (
                case cand of
                   IdHFCand id -> return $ Just $ idType id
                   NameHFCand nm -> fmap idType <$> tcLookupIdMaybe nm
                   GreHFCand GRE{..} -> fmap idType <$> tcLookupIdMaybe gre_name)
          where nm = pack $ occNameString $ occName cand

ectaPlugin :: [CommandLineOption] -> TypedHole -> [HoleFitCandidate] -> TcM [HoleFit]
ectaPlugin opts TyH{..} scope  | Just hole <- tyHCt,
                            ty <- ctPred hole = do
      scopeComps <- candsToComps scope
      let (scopeNode, skels, groups) =
            if "useHPlusComps" `elem` opts
            then let scopeNode = pAnyFunc
                     skels = invSkel
                     groups = invGroupMapping
                 in (scopeNode, skels, groups)
            else let scopeNode = Node . map (($ 0) . uncurry parseHoogleComponent) $ scopeComps
                     skels = Map.fromList scopeComps
                     groups = Map.fromList $ map (\(t,_) -> (t,[t])) scopeComps
                 in (scopeNode, skels, groups)
      case typeToSkeleton ty of
         Just t | resNode <- typeToFta t -> do
             let res = getAllTerms $ refold $ reduceFully $ filterType scopeNode resNode
             ppterms <- concatMapM (prettyMatch skels groups . prettyTerm ) res
             return $ map (RawHoleFit . text . unpack) ppterms
         _ ->  do liftIO $ putStrLn $  "Could not skeleton `" ++ showSDocUnsafe (ppr ty) ++"`"
                  return []
