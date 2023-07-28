module Parser.Internal where

import qualified Data.Map.Strict as M
import Data.Maybe (fromJust)
import qualified Data.Set as S

-- * Data representation for grammar

data Symbol
  = T Term
  | N NTerm
  deriving (Show, Eq, Ord)

-- nonterminal
newtype NTerm = NTerm String
  deriving (Show, Eq, Ord)

-- terminal
data Term
  = Empty
  | EOF
  | Term String
  deriving (Show, Eq, Ord)

type Grammar = (NTerm, [Rules]) -- (start symbol, rewriting rules)

type Rules = (NTerm, [RHS])

data RHS = RHS {index :: RuleIdx, lhs :: NTerm, prod :: [Symbol]}
  deriving (Eq, Ord)

type RuleIdx = Int -- index for rules to reference when reducing

-- * grammar for testing

testGrammar :: Grammar
testGrammar =
  ( NTerm "S",
    [ (NTerm "S", [RHS 0 (NTerm "S") [N $ NTerm "E", T $ Term "$"]]),
      ( NTerm "E",
        [ RHS 1 (NTerm "E") [T $ Term "+", N $ NTerm "E", N $ NTerm "E"],
          RHS 2 (NTerm "E") [T $ Term "#"]
        ]
      )
    ]
  )

g2 :: Grammar
g2 =
  ( NTerm "E",
    [ (NTerm "E", [RHS 0 (NTerm "E") [N $ NTerm "T", N $ NTerm "E'"]]),
      (NTerm "E'", [RHS 1 (NTerm "E'") [T $ Term "+", N $ NTerm "T", N $ NTerm "E'"], RHS 2 (NTerm "E'") [T Empty]]),
      (NTerm "T", [RHS 3 (NTerm "T") [N $ NTerm "F", N $ NTerm "T'"]]),
      (NTerm "T'", [RHS 4 (NTerm "T'") [T $ Term "*", N $ NTerm "F", N $ NTerm "T'"], RHS 5 (NTerm "T'") [T Empty]]),
      (NTerm "F", [RHS 6 (NTerm "F") [T $ Term "(", N $ NTerm "E", T $ Term ")"], RHS 7 (NTerm "F") [T $ Term "id"]])
    ]
  )

notlr0 :: Grammar
notlr0 =
  ( NTerm "S",
    [ (NTerm "S", [RHS 0 (NTerm "S") [N $ NTerm "E", T $ Term "$"]]),
      ( NTerm "E",
        [ RHS 1 (NTerm "E") [N $ NTerm "E", T $ Term "+", N $ NTerm "T"],
          RHS 2 (NTerm "E") [N $ NTerm "T"]
        ]
      ),
      ( NTerm "T",
        [ RHS 3 (NTerm "T") [N $ NTerm "T", T $ Term "*", T $ Term "#"],
          RHS 4 (NTerm "T") [T $ Term "#"]
        ]
      )
    ]
  )

-- * helper functions

symbols :: [Rules] -> S.Set Symbol
symbols rules = S.insert (T EOF) $ S.unions $ map (S.fromList . f) rules
  where
    f (n, nss) = N n : concatMap prod nss

closure :: Eq a => (a -> a) -> a -> a
closure f x = let next = f x in if x == next then x else closure f next

-- closureBy :: (a -> a -> Bool) -> (a -> a) -> a -> a
-- closureBy eq f x = let next = f x in if x `eq` next then x else closureBy eq f next

-- calculate first set for a grammar
first :: Grammar -> M.Map NTerm (S.Set Term)
first (_, rules) = closure (\m -> foldr f m rules) seed
  where
    seed = M.fromList $ [(e, S.empty) | N e <- S.elems $ symbols rules]
    -- update first set with a rule
    f :: Rules -> M.Map NTerm (S.Set Term) -> M.Map NTerm (S.Set Term)
    f (l, rss) m = M.insertWith S.union l (S.unions $ map (f' . prod) rss) m
      where
        -- calculate first set with rhs of rule
        f' :: [Symbol] -> S.Set Term
        f' (x : xs) = case x of
          (N n) -> let a = m M.! n in if S.member Empty a then S.union a (f' xs) else a
          (T Empty) -> f' xs
          (T t) -> S.singleton t
        f' [] = S.singleton Empty

-- calculate follow set for a grammar
follow :: Grammar -> M.Map NTerm (S.Set Term)
follow gram@(start, rules) = closure (\m -> foldr f m rules) seed
  where
    firstSet = first gram
    seed = M.fromList $ [if e == start then (e, S.singleton EOF) else (e, S.empty) | N e <- S.elems $ symbols rules]
    -- update table with rule
    f :: Rules -> M.Map NTerm (S.Set Term) -> M.Map NTerm (S.Set Term)
    f (lhs, rhss) m = foldr (g . prod) m rhss
      where
        -- update table with [Symbol]
        g :: [Symbol] -> M.Map NTerm (S.Set Term) -> M.Map NTerm (S.Set Term)
        g (T t : trail) m = g trail m
        g (N n : trail) m = g trail $ M.adjust (follow' trail) n m
          where
            -- update entry with [Symbol]
            follow' :: [Symbol] -> S.Set Term -> S.Set Term
            follow' (T Empty : ls) s = follow' ls s
            follow' (T t : _) s = S.insert t s
            follow' (N n : ls) s =
              let (empties, fs) = S.partition (== Empty) $ fromJust $ M.lookup n firstSet
               in if S.null empties then S.union fs s else S.union (follow' ls fs) s
            follow' [] s = S.union (fromJust $ M.lookup lhs m) s
        g [] m = m

type State = Int

data Action = Shift State | Reduce RuleIdx NTerm | Accept
  deriving (Show, Eq)

-- move from one state to the next
stepState :: Grammar -> Symbol -> S.Set RHS -> S.Set RHS
stepState gram sym old = S.unions $ S.map f old
  where
    f rhs@RHS {index = i, prod = l : ls} | l == sym = case ls of
      (N n) : as -> S.insert (rhs {prod = ls}) $ genState n gram
      x -> S.singleton (rhs {prod = x})
    f _ = S.empty

-- create new state from nonterminal
genState :: NTerm -> Grammar -> S.Set RHS
genState n (start, rules) = fst $ closure f (S.fromList seed, seed)
  where
    seed = fromJust $ lookup n rules
    -- process 1 element in the queue
    f :: (S.Set RHS, [RHS]) -> (S.Set RHS, [RHS])
    f (set, q : qs) = foldr tryInsert (set, qs) next
      where
        next = case head $ prod q of
          N n -> fromJust $ lookup n rules
          T t -> []
        tryInsert a (s, ls) = if not (S.member a s) then (S.insert a s, a : ls) else (s, ls)
    f a = a
