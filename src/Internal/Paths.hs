{-# LANGUAGE OverloadedStrings #-}

-- | Representations of paths in an FTA, data structures for
--   equality constraints over paths, algorithms for saturating these constraints

module Internal.Paths (
    Path(.., EmptyPath, ConsPath)
  , unPath
  , path
  , Pathable(..)
  , pathHeadUnsafe
  , pathTailUnsafe
  , isSubpath
  , isStrictSubpath
  , substSubpath

  , PathTrie(..)
  , InvertedPathTrie(..)
  , PathTrieZipper(..)
  , smallestNonempty
  , toPathTrie
  , fromPathTrie
  , pathTrieToZipper
  , zipperCurPathTrie
  , pathTrieDescend
  , pathTrieAscend

  , PathEClass(PathEClass, ..)
  , unPathEClass
  , hasSubsumingMember
  , completedSubsumptionOrdering

  , EqConstraints(.., EmptyConstraints)
  , rawMkEqConstraints
  , unsafeGetEclasses
  , hasSubsumingMemberListBased
  , isContradicting
  , mkEqConstraints
  , combineEqConstraints
  , constraintsAreContradictory
  , constraintsImply
  , subsumptionOrderedEclasses
  , unsafeSubsumptionOrderedEclasses
  ) where

import Control.Monad ( (=<<) )
import qualified Data.Array as Array
import Data.Function ( on )
import Data.List ( intersperse, isSubsequenceOf, nub, sort, sortBy )
import Data.Monoid ( Any(..), Endo(..) )
import Data.Hashable ( Hashable )
import Data.Semigroup ( Max(..) )
import qualified Data.Text as Text
import Data.Vector ( Vector )
import qualified Data.Vector as Vector
import Data.Vector.Instances ()

import Data.Equivalence.Monad ( runEquivM, equate, desc, classes )

import GHC.Generics ( Generic )

import Data.Memoization ( MemoCacheTag(..), memo2 )
import Pretty
import Utilities

-------------------------------------------------------


-----------------------------------------------------------------------
--------------------------- Misc / general ----------------------------
-----------------------------------------------------------------------

flipOrdering :: Ordering -> Ordering
flipOrdering GT = LT
flipOrdering LT = GT
flipOrdering EQ = EQ

-----------------------------------------------------------------------
-------------------------------- Paths --------------------------------
-----------------------------------------------------------------------

data Path = Path ![Int]
  deriving (Eq, Ord, Show, Generic)

unPath :: Path -> [Int]
unPath (Path p) = p

instance Hashable Path

{-
instance Show Path where
  showsPrec d (Path ps) =   showString "Path ["
                          . (appEndo $ mconcat $ map Endo $ intersperse (showString ".") $ map (showsPrec (d+1)) ps)
                          . showString "]"
-}

path :: [Int] -> Path
path = Path

{-# COMPLETE EmptyPath, ConsPath #-}

pattern EmptyPath :: Path
pattern EmptyPath = Path []

pattern ConsPath :: Int -> Path -> Path
pattern ConsPath p ps <- Path (p : (Path -> ps)) where
  ConsPath p (Path ps) = Path (p : ps)

pathHeadUnsafe :: Path -> Int
pathHeadUnsafe (Path ps) = head ps

pathTailUnsafe :: Path -> Path
pathTailUnsafe (Path ps) = Path (tail ps)

instance Pretty Path where
  pretty (Path ps) = Text.intercalate "." (map (Text.pack . show) ps)

isSubpath :: Path -> Path -> Bool
isSubpath EmptyPath         _                 = True
isSubpath (ConsPath p1 ps1) (ConsPath p2 ps2)
          | p1 == p2                          = isSubpath ps1 ps2
isSubpath _                 _                 = False

isStrictSubpath :: Path -> Path -> Bool
isStrictSubpath EmptyPath          EmptyPath        = False
isStrictSubpath EmptyPath          _                = True
isStrictSubpath (ConsPath p1 ps1) (ConsPath p2 ps2)
         | p1 == p2                                 = isStrictSubpath ps1 ps2
isStrictSubpath _                 _                 = False


-- | Read `substSubpath p1 p2 p3` as `[p1/p2]p3`
--
-- `substSubpath replacement toReplace target` takes `toReplace`, a prefix of target,
--  and returns a new path in which `toReplace` has been replaced by `replacement`.
--
--  Undefined if toReplace is not a prefix of target
substSubpath :: Path -> Path -> Path -> Path
substSubpath replacement toReplace target = Path $ (unPath replacement) ++ drop (length $ unPath toReplace) (unPath target)


--------------------------------------------------------------------------
---------------------------- Using paths ---------------------------------
--------------------------------------------------------------------------

-- | TODO: Should this be redone as a lens-library traversal?
-- | TODO: I am unhappy about this Emptyable design; makes one question whether
--         this should be a typeclass at all. (Terms/ECTAs differ in that
--         there is always an ECTA Node that represents the value at a path)
class Pathable t t' | t -> t' where
  type Emptyable t'
  getPath      :: Path -> t -> Emptyable t'
  getAllAtPath :: Path -> t -> [t']
  modifyAtPath :: (t' -> t') -> Path -> t -> t


-----------------------------------------------------------------------
----------------------- Path tries and zippers ------------------------
-----------------------------------------------------------------------

---------------------
------- Generic-ish utility functions
---------------------

-- | Precondition: A nonempty cell exists
smallestNonempty :: Vector PathTrie -> Int
smallestNonempty v = Vector.ifoldr (\i pt oldMin -> case pt of
                                                      EmptyPathTrie -> oldMin
                                                      _             -> i)
                                   maxBound
                                   v

---------------------
------- Path tries
---------------------

data PathTrie = EmptyPathTrie
              | TerminalPathTrie
              | PathTrieSingleChild {-# UNPACK #-} !Int !PathTrie
              | PathTrie !(Vector PathTrie) -- Invariant: Must have at least two nonempty nodes
  deriving ( Eq, Show, Generic )

instance Hashable PathTrie

comparePathTrieVectors :: Vector PathTrie -> Vector PathTrie -> Ordering
comparePathTrieVectors v1 v2 = foldr (\i res -> let (t1, t2) = (v1 Vector.! i, v2 Vector.! i)
                                                in case (isEmptyPathTrie t1, isEmptyPathTrie t2) of
                                                     (False, True)  -> LT
                                                     (True, False)  -> GT
                                                     (True, True)   -> res
                                                     (False, False) -> case compare t1 t2 of
                                                                         LT -> LT
                                                                         GT -> GT
                                                                         EQ -> res)
                                     valueIfComponentsMatch
                                     [0..(min (Vector.length v1) (Vector.length v2) - 1)]
  where
    valueIfComponentsMatch = compare (Vector.length v1) (Vector.length v2)



isEmptyPathTrie :: PathTrie -> Bool
isEmptyPathTrie EmptyPathTrie = True
isEmptyPathTrie _             = False

instance Ord PathTrie where
  compare EmptyPathTrie                EmptyPathTrie                = EQ
  compare EmptyPathTrie                _                            = LT
  compare _                            EmptyPathTrie                = GT
  compare TerminalPathTrie             TerminalPathTrie             = EQ
  compare TerminalPathTrie             _                            = LT
  compare _                            TerminalPathTrie             = GT
  compare (PathTrieSingleChild i1 pt1) (PathTrieSingleChild i2 pt2)
                          | i1 < i2                                 = LT
                          | i1 > i2                                 = GT
                          | otherwise                               = compare pt1 pt2
  compare (PathTrieSingleChild i1 pt1) (PathTrie v2)                = let i2 = smallestNonempty v2 in
                                                                      case compare i1 i2 of
                                                                        LT -> LT
                                                                        GT -> GT
                                                                        EQ -> case compare pt1 (v2 Vector.! i2) of
                                                                                LT -> LT
                                                                                GT -> GT
                                                                                EQ -> LT -- v2 must have a second nonempty
  compare a@(PathTrie _)               b@(PathTrieSingleChild _ _)  = flipOrdering $ compare b a
  compare (PathTrie v1)                (PathTrie v2)                = comparePathTrieVectors v1 v2


-- | Precondition: No path in the input is a subpath of another
toPathTrie :: [Path] -> PathTrie
toPathTrie []          = EmptyPathTrie
toPathTrie [EmptyPath] = TerminalPathTrie
toPathTrie ps          = if all (\p -> pathHeadUnsafe p == pathHeadUnsafe (head ps)) ps then
                           PathTrieSingleChild (pathHeadUnsafe $ head ps) (toPathTrie $ map pathTailUnsafe ps)
                         else
                           PathTrie vec
  where
    maxIndex = getMax $ foldMap (Max . pathHeadUnsafe) ps

    -- TODO: Inefficient to use this; many passes. over the list.
    -- This may not be used in a place where perf matters, though
    pathsStartingWith :: Int -> [Path] -> [Path]
    pathsStartingWith i ps = concatMap (\case EmptyPath    -> []
                                              ConsPath j p -> if i == j then [p] else [])
                                    ps

    vec = Vector.generate (maxIndex + 1) (\i -> toPathTrie $ pathsStartingWith i ps)

fromPathTrie :: PathTrie -> [Path]
fromPathTrie EmptyPathTrie              = []
fromPathTrie TerminalPathTrie           = [EmptyPath]
fromPathTrie (PathTrieSingleChild i pt) = map (ConsPath i) $ fromPathTrie pt
fromPathTrie (PathTrie v)               = Vector.ifoldr (\i pt acc -> map (ConsPath i) (fromPathTrie pt) ++ acc) [] v

---------------------
------- Zippers
---------------------

data InvertedPathTrie = PathZipperRoot
                      | PathTrieAt {-# UNPACK #-} !Int !PathTrie !InvertedPathTrie
  deriving ( Eq, Ord, Show )

data PathTrieZipper = PathTrieZipper !PathTrie !InvertedPathTrie
  deriving ( Eq, Ord, Show )


pathTrieToZipper :: PathTrie -> PathTrieZipper
pathTrieToZipper pt = PathTrieZipper pt PathZipperRoot

zipperCurPathTrie :: PathTrieZipper -> PathTrie
zipperCurPathTrie (PathTrieZipper pt _) = pt


pathTrieDescend :: PathTrieZipper -> Int -> PathTrieZipper
pathTrieDescend (PathTrieZipper     EmptyPathTrie              z) i = PathTrieZipper EmptyPathTrie  (PathTrieAt i EmptyPathTrie    z)
pathTrieDescend (PathTrieZipper     TerminalPathTrie           z) i = PathTrieZipper EmptyPathTrie  (PathTrieAt i TerminalPathTrie z)
pathTrieDescend (PathTrieZipper pt@(PathTrie v)                z) i = PathTrieZipper (v Vector.! i) (PathTrieAt i pt z)
pathTrieDescend (PathTrieZipper pt@(PathTrieSingleChild j pt') z) i
                | i == j                                            = PathTrieZipper pt'           (PathTrieAt i pt z)
                | otherwise                                         = PathTrieZipper EmptyPathTrie (PathTrieAt i pt z)

-- | The semantics of this may not be what you expect: Path trie zippers do not support editing currently, only traversing.
--   The value at the cursor (as well as the index) is ignored except when traversing above the root, where it uses those
--   values to extend the path trie upwards.
pathTrieAscend :: PathTrieZipper -> Int -> PathTrieZipper
pathTrieAscend (PathTrieZipper pt PathZipperRoot)         i = PathTrieZipper (PathTrieSingleChild i pt) PathZipperRoot
pathTrieAscend (PathTrieZipper pt (PathTrieAt i pt' ipt)) _ = PathTrieZipper pt'                        ipt

--------------------------------------------------------------------------
---------------------- Equality constraints over paths -------------------
--------------------------------------------------------------------------

---------------------------
---------- Path E-classes
---------------------------

data PathEClass = PathEClass' { getPathTrie  :: !PathTrie
                              , getOrigPaths :: ![Path]
                              }
  deriving ( Show, Generic )

instance Eq PathEClass where
  (==) = (==) `on` getPathTrie

instance Ord PathEClass where
  compare = compare `on` getPathTrie

-- | TODO: This pattern (and the caching of the original path list) is a temporary affair
--         until we convert all clients of PathEclass to fully be based on tries
pattern PathEClass :: [Path] -> PathEClass
pattern PathEClass ps <- PathEClass' _ ps where
  PathEClass ps = PathEClass' (toPathTrie $ nub ps) (sort $ nub ps)

unPathEClass :: PathEClass -> [Path]
unPathEClass (PathEClass' _ paths) = paths

instance Pretty PathEClass where
  pretty pec = "{" <> (Text.intercalate "=" $ map pretty $ unPathEClass pec) <> "}"

instance Hashable PathEClass

hasSubsumingMember :: PathEClass -> PathEClass -> Bool
hasSubsumingMember pec1 pec2 = go (getPathTrie pec1) (getPathTrie pec2)
  where
    go :: PathTrie -> PathTrie -> Bool
    go EmptyPathTrie                _                            = False
    go _                            EmptyPathTrie                = False
    go TerminalPathTrie             TerminalPathTrie             = False
    go TerminalPathTrie             _                            = True
    go _                            TerminalPathTrie             = False
    go (PathTrieSingleChild i1 pt1) (PathTrieSingleChild i2 pt2) = if i1 == i2 then
                                                                     go pt1 pt2
                                                                   else
                                                                     False
    go (PathTrieSingleChild i1 pt1) (PathTrie v2)                = case v2 Vector.!? i1 of
                                                                     Nothing  -> False
                                                                     Just pt2 -> go pt1 pt2
    go (PathTrie v1)                (PathTrieSingleChild i2 pt2) = case v1 Vector.!? i2 of
                                                                     Nothing  -> False
                                                                     Just pt1 -> go pt1 pt2
    go (PathTrie v1)                (PathTrie v2)                = any (\i -> go (v1 Vector.! i) (v2 Vector.! i))
                                                                       [0..(min (Vector.length v1) (Vector.length v2) - 1)]


-- | Extends the subsumption ordering to a total ordering by using the default lexicographic
--   comparison for incomparable elements.
-- | TODO: Optimization opportunity: Redundant work in the hasSubsumingMember calls
completedSubsumptionOrdering :: PathEClass -> PathEClass -> Ordering
completedSubsumptionOrdering pec1 pec2
                       | hasSubsumingMember pec1 pec2 = LT
                       | hasSubsumingMember pec2 pec1 = GT
                       -- | This next line is some hacky magic. Basically, it means that for the
                       --   Hoogle+/TermSearch workload, where there is no subsumption,
                       --   constraints will be evaluated in left-to-right order (instead of the default
                       --   right-to-left), which for that particular workload produces better
                       --   constraint-propagation
                       | otherwise                    = compare pec2 pec1

--------------------------------
---------- Equality constraints
--------------------------------

data EqConstraints = EqConstraints { getEclasses :: [PathEClass] -- | Must be sorted
                                   }
                   | EqContradiction
  deriving ( Eq, Ord, Show, Generic )

instance Hashable EqConstraints

instance Pretty EqConstraints where
  pretty ecs = "{" <> (Text.intercalate "," $ map pretty (getEclasses ecs)) <> "}"

--------- Destructors and patterns

-- | Unsafe. Internal use only
ecsGetPaths :: EqConstraints -> [[Path]]
ecsGetPaths = map unPathEClass . getEclasses

pattern EmptyConstraints :: EqConstraints
pattern EmptyConstraints = EqConstraints []

unsafeGetEclasses :: EqConstraints -> [PathEClass]
unsafeGetEclasses EqContradiction = error "unsafeGetEclasses: Illegal argument 'EqContradiction'"
unsafeGetEclasses ecs             = getEclasses ecs

rawMkEqConstraints :: [[Path]] -> EqConstraints
rawMkEqConstraints = EqConstraints . map PathEClass


constraintsAreContradictory :: EqConstraints -> Bool
constraintsAreContradictory = (== EqContradiction)

--------- Construction


hasSubsumingMemberListBased :: [Path] -> [Path] -> Bool
hasSubsumingMemberListBased ps1 ps2 = getAny $ mconcat [Any (isStrictSubpath p1 p2) | p1 <- ps1
                                                                                    , p2 <- ps2]

-- | The real contradiction condition is a cycle in the subsumption ordering.
--   But, after congruence closure, this will reduce into a self-cycle in the subsumption ordering.
--
--   TODO; Prove this.
isContradicting :: [[Path]] -> Bool
isContradicting cs = any (\pec -> hasSubsumingMemberListBased pec pec) cs

-- Contains an inefficient implementation of the congruence closure algorithm
mkEqConstraints :: [[Path]] -> EqConstraints
mkEqConstraints initialConstraints = case completedConstraints of
                                       Nothing -> EqContradiction
                                       Just cs -> EqConstraints $ sort $ map PathEClass cs
  where
    removeTrivial :: (Eq a) => [[a]] -> [[a]]
    removeTrivial = filter (\x -> length x > 1) . map nub

    -- Reason for the extra "complete" in this line:
    -- The first simplification done to the constraints is eclass-completion,
    -- to remove redundancy and shrink things before the very inefficienc
    -- addCongruences step (important in tests; less so in realistic input).
    -- The last simplification must also be completion, to give a valid value.
    completedConstraints = fixMaybe round $ complete $ removeTrivial initialConstraints

    round :: [[Path]] -> Maybe [[Path]]
    round cs = let cs'  = addCongruences cs
                   cs'' = complete cs'
               in if isContradicting cs'' then
                    Nothing
                  else
                    Just cs''

    addCongruences :: [[Path]] -> [[Path]]
    addCongruences cs = cs ++ [map (\z -> substSubpath z x y) left | left <- cs, right <- cs, x <- left, y <- right, isStrictSubpath x y]

    assertEquivs xs = mapM (\y -> equate (head xs) y) (tail xs)

    complete :: (Ord a) => [[a]] -> [[a]]
    complete initialClasses = runEquivM (:[]) (++) $ do
      mapM_ assertEquivs initialClasses
      mapM desc =<< classes

---------- Operations

combineEqConstraints :: EqConstraints -> EqConstraints -> EqConstraints
combineEqConstraints = memo2 (NameTag "combineEqConstraints") go
  where
    go EqContradiction _               = EqContradiction
    go _               EqContradiction = EqContradiction
    go ec1             ec2             = mkEqConstraints $ ecsGetPaths ec1 ++ ecsGetPaths ec2
{-# NOINLINE combineEqConstraints #-}

-- A faster implementation would be: Merge the eclasses of both, run mkEqConstraints (or at least do eclass completion),
-- check result equal to ecs2
constraintsImply :: EqConstraints -> EqConstraints -> Bool
constraintsImply EqContradiction _               = True
constraintsImply _               EqContradiction = False
constraintsImply ecs1            ecs2            = all (\cs -> any (isSubsequenceOf cs) (ecsGetPaths ecs1)) (ecsGetPaths ecs2)



subsumptionOrderedEclasses :: EqConstraints -> Maybe [PathEClass]
subsumptionOrderedEclasses ecs = case ecs of
                                   EqContradiction    -> Nothing
                                   EqConstraints pecs -> Just $ sortBy completedSubsumptionOrdering pecs

unsafeSubsumptionOrderedEclasses :: EqConstraints -> [PathEClass]
unsafeSubsumptionOrderedEclasses (EqConstraints pecs) = sortBy completedSubsumptionOrdering pecs