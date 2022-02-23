{-# LANGUAGE OverloadedStrings #-}

-- | A very bad SAT solver written by reduction to ECTA
--
--  Also a constructive proof of the NP-hardness of finding
--  a term represented by an ECTA

module Application.SAT (
  -- * Data types
    Var
  , mkVar
  , CNF(..)
  , Clause(..)
  , Lit(..)

  -- * Solving
  , toEcta
  , allSolutions

  -- * Examples
  , ex1
  , ex2
  , ex3
  ) where

import Data.Hashable ( Hashable )
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HashSet
import Data.List ( elemIndex, sort )
import Data.Maybe ( fromJust )
import Data.String (IsString(..) )
import Data.Text ( Text )

import GHC.Generics ( Generic )

import Data.List.Index ( imap )

import Data.ECTA
import Data.ECTA.Paths
import Data.ECTA.Term
import Data.Text.Extended.Pretty
import Utility.Fixpoint

----------------------------------------------------------------

-------------------------------------------------------------------
------------------------- SAT variables ---------------------------
-------------------------------------------------------------------


newtype Var = Var { unVar :: Text }
  deriving ( Eq, Ord, Show, Generic )

instance Hashable Var

instance IsString Var where
  fromString = Var . fromString

mkVar :: Text -> Var
mkVar = Var

_varToSymbol :: Var -> Symbol
_varToSymbol = Symbol . unVar

_varToNegSymbol :: Var -> Symbol
_varToNegSymbol v = Symbol ("~" <> unVar v)


-------------------------------------------------------------------
----------------------- CNF representation ------------------------
-------------------------------------------------------------------

-- | Our construction generalizes to arbitrary NNF formulas,
--   and possibly to arbitrary SAT,
--   but we don't need to bother; just CNF is good enough

data CNF = And [Clause]
  deriving ( Eq, Ord, Show, Generic )

instance Hashable CNF

data Clause = Or [Lit]
  deriving ( Eq, Ord, Show, Generic )

instance Hashable Clause

data Lit = PosLit Var
         | NegLit Var
  deriving ( Eq, Ord, Show, Generic )

instance Hashable Lit

instance Pretty Lit where
  pretty (PosLit v) = unVar v
  pretty (NegLit v) = "~" <> unVar v

getLitVar :: Lit -> Var
getLitVar (PosLit v) = v
getLitVar (NegLit v) = v

---------------------
-------- Traversals
---------------------

-- | This is an updatable fold algebra; see "Dealing with Large Bananas"
data CNFAlg a  = CNFAlg { runCNF    :: CNF    -> [a] -> a
                        , runClause :: Clause -> [a] -> a
                        , runLit    :: Lit           -> a
                        }

_emptyAlg :: (Monoid m) => CNFAlg m
_emptyAlg = CNFAlg (const mempty) (const mempty) (const mempty)


class FoldAlg a where
  foldAlg :: CNFAlg m -> a -> m

instance FoldAlg CNF where
  foldAlg alg c@(And clauses) = runCNF alg c (map (foldAlg alg) clauses)

instance FoldAlg Clause where
  foldAlg alg c@(Or lits) = runClause alg c (map (foldAlg alg) lits)

instance FoldAlg Lit where
  foldAlg alg l = runLit alg l

crushAlg :: (Monoid m) => (Lit -> m) -> CNFAlg m
crushAlg f = CNFAlg (const mconcat) (const mconcat) f

getVars :: CNF -> HashSet Var
getVars = foldAlg (crushAlg (HashSet.singleton  . getLitVar))

-----
-- Lit paths
-----

newtype LitPaths = LitPaths { unLitPaths :: HashMap Lit [Path] }

instance Semigroup LitPaths where
  lp1 <> lp2 = LitPaths $ HashMap.unionWith mappend (unLitPaths lp1) (unLitPaths lp2)

instance Monoid LitPaths where
  mempty  = LitPaths HashMap.empty

getLitPathsAlg :: CNFAlg LitPaths
getLitPathsAlg = CNFAlg { runCNF    = \_ lps -> mconcat $ imap (\i lp -> LitPaths $ HashMap.map (map (ConsPath i)) $ unLitPaths lp) lps
                        , runClause = \_ lps -> mconcat lps
                        , runLit    = \lit -> LitPaths $ HashMap.singleton lit [EmptyPath]
                         }

_getLitPaths :: CNF -> LitPaths
_getLitPaths = foldAlg getLitPathsAlg

-------------------------------------------------------------------
------------------------- ECTA conversion -------------------------
-------------------------------------------------------------------

falseNode :: Node
falseNode = Node [Edge "0" []]

trueNode :: Node
trueNode = Node [Edge "1" []]

trueOrFalseNode :: Node
trueOrFalseNode = union [falseNode, trueNode]

falseTerm :: Term
falseTerm = head $ naiveDenotation falseNode

trueTerm :: Term
trueTerm = head $ naiveDenotation trueNode




-- | Encoding:
--   clauses(<list of clause nodes>)
--
-- assnNode:
--  * One edge, with one child per variable
--  * Each variable has two choices, true or false
--
--
-- Clause nodes:
--  * One edge per literal in the clause, each corresponding to a choice of which variable
--    makes the clause true.
--  * First child of each edge is an assnNode (will be constrained to be the same as all other assnNode's)
--  * Second child of each edge is trueNode or falseNode, depending on if that literal is positive or negative
--  * Constrain said second child to be equal to the truth value of the corresponding variable
--    in the assnNode
--
-- Top level constraints:
--  * Constrain all assignment nodes in all the clauses to be the same
--
-- An optimization not taken: Put the constraints on individual variables across assignments,
--                            not on the assignment node itself. Plays more nicely with enumeration.

toEcta :: CNF -> Node
toEcta formula = formulaNode
  where
    clauses :: [Clause]
    And clauses = formula

    numClauses :: Int
    numClauses = length clauses

    sortedVars :: [Var]
    sortedVars = sort $ HashSet.toList $ getVars formula

    varToIndex :: Var -> Int
    varToIndex v = fromJust (elemIndex v sortedVars)

    litToIndex :: Lit -> Int
    litToIndex (PosLit v) = varToIndex v
    litToIndex (NegLit v) = varToIndex v

    assnNode :: Node
    assnNode = Node [Edge "assignment" (map (const trueOrFalseNode) sortedVars)]

    formulaNode :: Node
    formulaNode = Node [mkEdge "clauses" (map mkClauseNode clauses) assnCopyingConstraints]

    mkClauseNode :: Clause -> Node
    mkClauseNode (Or lits) = Node (map mkLitChoiceEdge lits)
      where
        mkLitChoiceEdge :: Lit -> Edge
        mkLitChoiceEdge lit = mkEdge (Symbol $ "choice[" <> pretty lit <> "]")
                                     [assnNode, mkLitNode lit]
                                     (mkEqConstraints [[path [0, litToIndex lit],  path [1]]])

    mkLitNode :: Lit -> Node
    mkLitNode (PosLit _) = trueNode
    mkLitNode (NegLit _) = falseNode

    assnCopyingConstraints :: EqConstraints
    assnCopyingConstraints = mkEqConstraints [[path [i, 0] | i <- [0..numClauses - 1]]]


allSolutions :: CNF -> HashSet (HashMap Var Bool)
allSolutions formula = foldMap (HashSet.singleton . termToAssignment) $ getAllTerms $ fixUnbounded reducePartially $ toEcta formula
  where
    sortedVars :: [Var]
    sortedVars = sort $ HashSet.toList $ getVars formula

    termToAssignment :: Term -> HashMap Var Bool
    termToAssignment (Term _ (Term _ [(Term _ varVals), _] : _)) = foldMap (\(var, val) -> HashMap.singleton var (termToBool val))
                                                                           (zip sortedVars varVals)
    termToAssignment x                                           = error $ "Unexpected " <> show x

    termToBool :: Term -> Bool
    termToBool t | t == falseTerm = False
                 | t == trueTerm  = True
                 | otherwise      = error "termToBool: Invalid argument"


-------------------------------------------------------------------
------------------------ Example formulae -------------------------
-------------------------------------------------------------------

-- Naive generation: 2^30 * 3^4 possibilities
ex1 :: CNF
ex1 = And [ Or [PosLit "x1", PosLit "x2", PosLit "x3"]
          , Or [NegLit "x1", PosLit "x2", PosLit "x3"]
          , Or [PosLit "x1", NegLit "x2", PosLit "x3"]
          , Or [PosLit "x1", PosLit "x2", NegLit "x3"]
          ]

-- Naive generation: 2^14
ex2 :: CNF
ex2 = And [ Or [PosLit "x1", PosLit "x2"]
          , Or [NegLit "x1", NegLit "x2"]
          ]


-- Partial reduction of the ECTA effectively performs unit propagation, solving this quickly.
ex3 :: CNF
ex3 = And [ Or [NegLit "x1"]
          , Or [PosLit "x1", PosLit "x2"]
          , Or [NegLit "x2", PosLit "x3"]
          ]