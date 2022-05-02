{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE  OverloadedStrings #-}
module CCTP.Utils where

-- These will be ruined by GHC 9.0+ due to the reorganization
-- These will be ruined by GHC 9.0+ due to the reorganization
import GhcPlugins hiding ((<>))
import TcRnTypes

import Application.TermSearch.Dataset
import Application.TermSearch.Type
import GhcPlugins hiding ((<>))
import Type
import Data.Text (pack, Text, unpack)
import Data.Maybe (mapMaybe, isJust, fromJust)

import Data.Map (Map)
import qualified Data.Map as Map

import GHC.IO.Unsafe
import Data.IORef
import TcRnMonad (newUnique, getTopEnv, getLocalRdrEnv, getGlobalRdrEnv)
import TcEnv (tcLookupTyCon)
import Data.Char (isAlpha, isAscii)
import Data.ECTA (Node (Node), mkEdge, Edge (Edge), pathsMatching, mapNodes, createMu)
import Data.ECTA.Term
import Application.TermSearch.Utils (theArrowNode, arrowType, var1, var2, var3, var4, varAcc, mkDatatype)
import Data.ECTA (union)
import Data.ECTA.Paths (getPath, mkEqConstraints, path, Path)
import Debug.Trace (traceShow)
import qualified Data.Monoid as M
import Data.List (groupBy, sortOn, permutations)
import Data.Function (on)
import Data.Tuple (swap)
import Data.Containers.ListUtils (nubOrd)
import Data.List (subsequences)

 -- The old "global variable" trick, as we are creating new type variables
 -- from scratch, but we want all 'a's to refer to the same variabel, etc.
tyVarMap :: IORef (Map Text TyVar)
{-# NOINLINE tyVarMap #-}
tyVarMap = unsafePerformIO (newIORef Map.empty)

skeletonToType :: TypeSkeleton -> TcM (Maybe Type)
skeletonToType (TVar t) = Just <$>
     do tm <- liftIO $ readIORef tyVarMap
        case tm Map.!? t of
            Just tv -> return $ mkTyVarTy tv
            _ -> do
                unq <- newUnique
                let nm = mkSystemName unq $ mkOccName tvName (unpack t)
                    ntv = mkTyVar nm liftedTypeKind
                liftIO $ modifyIORef tyVarMap (Map.insert t ntv)
                return $ mkTyVarTy ntv
skeletonToType (TFun arg ret) =
     do argty <- skeletonToType arg
        retty <- skeletonToType ret
        case (argty, retty) of
            (Just a, Just r) -> return (Just (mkVisFunTy a r))
            _ -> return Nothing
        -- This will be mkVisFunTyMany in 9.0+
skeletonToType (TCons con sk) =
    do args <- mapM skeletonToType sk
       let occn = mkOccName tcName (unpack con)
       lcl_env <- getLocalRdrEnv
       gbl_env <- getGlobalRdrEnv
       let conName = case lookupLocalRdrOcc lcl_env occn of
                        Just res -> Just res
                        _ -> case lookupGlobalRdrEnv gbl_env occn of
                          -- Note: does not account for shadowing
                          (GRE{..}:_) -> Just gre_name
                          _ -> Nothing
       case conName of
           Just n | all isJust args, argTys <- map fromJust args ->  do
               conTy <- tcLookupTyCon n
               return $ Just $ mkTyConApp conTy argTys
           _ -> return Nothing




-- | Extremely crude at the moment!!
-- Returns the typeSkeleton and any constructors (for instance lookup)
typeToSkeleton :: Type -> Maybe (TypeSkeleton, [Type])
typeToSkeleton ty | (vars@(_:_), r) <- splitForAllTys ty,
                    all valid vars
                    = typeToSkeleton r
  where
      valid :: TyCoVar -> Bool
      -- for now
      valid = (`elem` ["a", "b", "c", "d", "acc"]) . showSDocUnsafe . ppr
typeToSkeleton ty | isTyVarTy ty,
                       Just tt <- tyVarToSkeletonText ty = Just  (TVar tt, [])
typeToSkeleton ty | Just (arg, ret) <- splitFunTy_maybe ty,
                       Just (argsk, ac)<- typeToSkeleton arg,
                       Just (retsk, rc)<- typeToSkeleton ret =
    Just (TFun argsk retsk,ac)
typeToSkeleton ty | (cons, args@(_:_)) <- splitAppTys ty,
                       Just const <- typeToSkeletonText cons,
                       argsks <- mapMaybe typeToSkeleton args,
                       (aks, acs) <- unzip argsks =
    Just (TCons const aks, cons:concat acs)
typeToSkeleton ty | (cons, []) <- splitAppTys ty,
                     Just const <- typeToSkeletonText cons
    -- These are the ones we don't handle so far
    = Just (TCons const [], [cons])

-- TODO: Filter out lifted rep etc.
typeToSkeletonText :: Outputable a => a -> Maybe Text
typeToSkeletonText ty = Just $ pack $ showSDocUnsafe $ ppr ty

-- TODO: make sure it's one of the supported ones
tyVarToSkeletonText :: Outputable a => a -> Maybe Text
tyVarToSkeletonText ty = Just $ pack $ stripNumbers $ showSDocUnsafe $ ppr ty
  -- by default, the variables are given a number (e.g. a1).
  -- we just strip them off for now.
  where stripNumbers :: String -> String
        stripNumbers = takeWhile isAlpha


constFunc :: Symbol -> Node -> Edge
constFunc s t = Edge s [t]

applyOperator :: Comps -> Node
applyOperator comps = Node
  [ constFunc
    "$"
    (generalize comps $ arrowType (arrowType var1 var2) (arrowType var1 var2))
  , constFunc "id" (generalize comps  $ arrowType var1 var1)
  ]

tk :: Comps -> Node -> Bool -> Int -> [Node]
tk _ _ _ 0 = []
tk _ anyArg False 1 = [anyArg]
tk comps anyArg True 1 = [anyArg, applyOperator comps]
tk comps anyArg _ k = map constructApp [1 .. (k-1)]
 where
   constructApp :: Int -> Node
   constructApp i =
      mapp (union $ tk comps anyArg False i) (union $ tk comps anyArg True (k-i))

tkUpToK :: Comps -> Node -> Bool -> Int -> [Node]
tkUpToK comps anyArg includeApp k = concatMap (tk comps anyArg includeApp) [1..k]

-- type Argument = (Symbol, Node)
rtk :: [Argument] -> Comps -> Node -> Bool -> Int -> [Node]
rtk [] comps anyArg includeApplyOp k = tk comps anyArg False k
rtk [(s,t)] _ _ _ 1 = [Node [constFunc s t]] -- If we have one arg we use it
rtk args _ _ _ k | k < length args = []
rtk args comps anyArg _ k = concatMap (\i -> map (constructApp i) allSplits) [1..(k-1)]
  where allSplits = map (`splitAt` args) [0.. (length args)]
        constructApp :: Int -> ([Argument], [Argument]) -> Node
        constructApp i (xs, ys) =
          let f = union $ rtk xs comps anyArg False i
              x = union $ rtk ys comps anyArg True (k-i)
          in mapp f x

rtkOfSize :: [Argument] -> Comps -> Node -> Bool -> Int -> Node
rtkOfSize args comps anyArg includeApp k = union $ concatMap (\a -> rtk a comps anyArg includeApp k) $ permutations args

rtkUpToK :: [Argument] -> Comps -> Node -> Bool -> Int -> [Node]
rtkUpToK args comps anyArg includeApp k =  map (rtkOfSize args comps anyArg includeApp) [1..k]

rtkUpToKAtLeast1 :: [Argument] -> Comps -> Node -> Bool -> Int -> [Node]
rtkUpToKAtLeast1 args comps anyArg includeApp k =
  concatMap (\as -> rtkUpToK as comps anyArg includeApp k) $ map (:[]) args



mapp :: Node -> Node -> Node
mapp n1 n2 = Node [
    mkEdge "app"
    [getPath (path [0,2]) n1, theArrowNode, n1, n2]
    (mkEqConstraints [
          [path [1], path [2, 0, 0]] -- it's a function
        , [path [3, 0], path [2, 0, 1]]
        , [path [0], path [2,0,2]]
        ]
    )]


pp :: Term -> Text
pp = mconcat . pp' False
 where
  pp' :: Bool -> Term -> [Text]
  pp' _ (Term (Symbol t) []) | ('@':str) <- unpack t = [pack str]
  pp' _ (Term (Symbol t) [])  = [t]
  pp' par (Term (Symbol "app") (arg:rest)) | res@(_:_) <- concatMap (pp' True) rest =
      [rpar <> wparifreq <> " " <> mconcat (concatMap (pp' True) rest) <> lpar]
                                           | otherwise = [wparifreq]
    where parg = pp arg
          (rpar,lpar) = if par then ("(", ")") else ("","")
          wparifreq = if length (words $ unpack parg) > 1
                      then "(" <> parg <> ")" else parg

allConstructors :: Comps -> [(Text, Int)]
allConstructors comps = nubOrd (concatMap (getConstructors . snd) comps)
 where
  getConstructors :: TypeSkeleton -> [(Text, Int)]
  getConstructors (TVar _    ) = []
  getConstructors (TFun t1 t2) = getConstructors t1 ++ getConstructors t2
  getConstructors (TCons nm ts) =
    (nm, length ts) : concatMap getConstructors ts

type Comps = [(Text,TypeSkeleton)]

mtau :: Comps -> Node
mtau comps = createMu
  (\n -> union
    (  (arrowType n n:globalTyVars)
    ++ map (Node . (: []) . constructorToEdge n) usedConstructors
    )
  )
 where
  constructorToEdge :: Node -> (Text, Int) -> Edge
  constructorToEdge n (nm, arity) = Edge (Symbol nm) (replicate arity n)

  usedConstructors = allConstructors comps

globalTyVars :: [Node]
globalTyVars = [var1, var2, var3, var4, varAcc]

generalize :: Comps -> Node -> Node
generalize comps n@(Node [_]) = Node
  [mkEdge s ns' (mkEqConstraints $ map pathsForVar vars)]
 where
  vars                = globalTyVars
  nWithVarsRemoved    = mapNodes (\x -> if x `elem` vars then mtau comps else x) n
  (Node [Edge s ns']) = nWithVarsRemoved

  pathsForVar :: Node -> [Path]
  pathsForVar v = pathsMatching (== v) n
generalize _ n = n -- error $ "cannot generalize: " ++ show n

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
  where tsk = case skels Map.!? t of
                Just r -> r
                _ -> skels Map.! (pack $ tail $ unpack t) -- for generalization
        terms = case groups Map.!? t of
                  Just r -> r
                  _ -> groups Map.! (pack $ tail $ unpack t)
            

mtypeToFta :: TypeSkeleton -> Node
mtypeToFta (TVar "a"  ) = var1
mtypeToFta (TVar "b"  ) = var2
mtypeToFta (TVar "c"  ) = var3
mtypeToFta (TVar "d"  ) = var4
mtypeToFta (TVar "acc") = varAcc
-- TODO: lift this restriction
mtypeToFta (TVar v) =
  error
    $ "Current implementation only supports function signatures with type variables a, b, c, d, and acc, but got "
    ++ show v
mtypeToFta (TFun  t1    t2      ) = arrowType (mtypeToFta t1) (mtypeToFta t2)
mtypeToFta (TCons "Fun" [t1, t2]) = arrowType (mtypeToFta t1) (mtypeToFta t2)
mtypeToFta (TCons s     ts      ) = mkDatatype s (map mtypeToFta ts)
