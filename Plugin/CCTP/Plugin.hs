{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
module CCTP.Plugin (plugin) where

import GhcPlugins hiding ((<>))
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
import Data.Maybe (fromMaybe, mapMaybe, isJust, fromJust)
import Data.Tuple (swap)
import Data.List (sortOn, groupBy, nub, nubBy)
import Data.Function (on)
import qualified Data.Monoid as M
import MonadUtils (concatMapM)
import TcRnMonad (writeTcRef, newTcRef, readTcRef, mapMaybeM, getTopEnv)
import TcEnv (tcLookupId, tcLookupIdMaybe)
import qualified Data.Bifunctor as Bi
import TcRnDriver (tcRnGetInfo)
import GHC (ClsInst)
import InstEnv (ClsInst(ClsInst, is_tvs, is_cls_nm, is_tys))
import Language.Dot.Pretty (renderDot)


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


prettyMatch :: Map.Map Text TypeSkeleton -> Map.Map Text [Text] -> Term -> TcM [Text]
prettyMatch skels groups (Term (Symbol t) _) =
  do ty <- skeletonToType tsk
     let str = case ty of
               Just t  -> pack (" :: " ++  showSDocUnsafe (ppr t))
               _ -> pack (" :: " ++ show tsk)
     return $ map (M.<> str) terms
  where tsk = skels Map.! t
        terms = groups Map.! t

candsToComps :: [HoleFitCandidate] -> TcM [((Text, TypeSkeleton), [Type])]
candsToComps = mapMaybeM (fmap (fmap extract) . candToTN)
  where candToTN :: HoleFitCandidate -> TcM (Maybe (Text, (TypeSkeleton, [Type])))
        candToTN cand = fmap (fmap (nm,) . (>>= typeToSkeleton)) (c2t cand)
          where nm = pack $ occNameString $ occName cand
                c2t cand =
                  case cand of
                    IdHFCand id -> return $ Just $ idType id
                    NameHFCand nm -> fmap idType <$> tcLookupIdMaybe nm
                    GreHFCand GRE{..} -> fmap idType <$> tcLookupIdMaybe gre_name
        extract (a, (b,c)) = ((a,b), c)


instToTerm :: ClsInst -> Maybe (Text, TypeSkeleton)
instToTerm ClsInst{..} | [] <- is_tvs,
                         all isJust args,
                         jargs <- map (fst . fromJust) args =
  Just (clsstr <> tystr,TCons clsstr jargs )
  where clsstr =  pack $  showSDocUnsafe $ ppr is_cls_nm
        tystr = pack $ showSDocUnsafe $ ppr is_tys
        args = map typeToSkeleton is_tys
instToTerm _ =  Nothing

ectaPlugin :: [CommandLineOption] -> TypedHole -> [HoleFitCandidate] -> TcM [HoleFit]
ectaPlugin opts TyH{..} scope  | Just hole <- tyHCt,
                            ty <- ctPred hole = do
      (fun_comps, scons) <- fmap (nubBy eqType . concat) . unzip <$> candsToComps scope
      -- TODO: like in the Hoogle comp: if we encounter a requirement
      -- like "Functor a" or similar, we can use ":info" on "Functor"
      -- to generate "Functor []", "Functor Maybe" etc. from scope.
      -- We can use the lookupInsts :: TyThing -> TcM ([ClsInsts], [FamInsts]),
      -- where the insts
      let constraints = filter (tcReturnsConstraintKind . tcTypeKind) scons
      hsc_env <- getTopEnv
      instance_comps <- mapMaybe instToTerm . concat <$>
                             mapMaybeM (fmap (fmap (\(_,_,c,_,_) -> c) . snd)
                                       . liftIO  . tcRnGetInfo hsc_env . getName
                                       . tyConAppTyCon) constraints
      let scope_comps = fun_comps ++ instance_comps
      let (scopeNode, anyArg, skels, groups) =
            let argNodes = map (Bi.bimap Symbol typeToFta) scope_comps
                anyArg = Node $
                   map (\(s,t) -> Edge (Symbol s) [typeToFta t]) scope_comps
                scopeNode = anyArg
                skels = Map.fromList scope_comps
                groups = Map.fromList $ map (\(t,_) -> (t,[t])) scope_comps
            in (scopeNode, anyArg, skels, groups)
      case typeToSkeleton ty of
         Just (t, cons) | resNode <- typeToFta t -> do
             let res = getAllTerms $ refold $ reduceFully $ filterType scopeNode resNode
             ppterms <- concatMapM (prettyMatch skels groups . prettyTerm ) res

             let moreTerms = map (pp . prettyTerm) $ concatMap (getAllTerms . refold . reduceFully . flip filterType resNode ) (tk anyArg 2)
            --  liftIO $ mapM_ (putStrLn . unpack . pp . prettyTerm ) $
            --             concatMap (getAllTerms . refold . reduceFully . flip filterType resNode ) (tk anyArg 2)

             liftIO $ writeFile "scope-node.dot" $ renderDot $ toDot scopeNode
             return $ map (RawHoleFit . text . unpack) $ ppterms ++ moreTerms
         _ ->  do liftIO $ putStrLn $  "Could not skeleton `" ++ showSDocUnsafe (ppr ty) ++"`"
                  return []
