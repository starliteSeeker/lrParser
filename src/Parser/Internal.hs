module Parser.Internal where

import qualified Data.Bifunctor as Bifunctor
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust)
import qualified Data.Sequence as A
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

type Rules = (NTerm, [Rule])

data Rule = Rule {index :: RuleIdx, prod :: [Symbol], followI :: S.Set Term}
  deriving (Eq, Ord, Show)

{-
instance Show Rule where
  show Rule {index = Idx {ruleNo = i, leftSym = NTerm l}, prod = p} =
    "\"" ++ show i ++ " " ++ show l ++ " -> " ++ show p ++ "\""
-}

newRule :: Int -> NTerm -> [Symbol] -> Rule
newRule i l r = Rule (Idx {ruleNo = i, leftSym = l}) r S.empty

data RuleIdx = Idx {ruleNo :: Int, leftSym :: NTerm}
  deriving (Eq, Ord, Show)

-- (NTerm, Int, Int) -- index for rules to reference when reducing

-- * grammar for testing

testGrammar :: Grammar
testGrammar =
  ( NTerm "S",
    [ (NTerm "S", [newRule 0 (NTerm "S") [N $ NTerm "E", T $ Term "$"]]),
      ( NTerm "E",
        [ newRule 1 (NTerm "E") [T $ Term "+", N $ NTerm "E", N $ NTerm "E"],
          newRule 2 (NTerm "E") [T $ Term "#"]
        ]
      )
    ]
  )

g2 :: Grammar
g2 =
  ( NTerm "E",
    [ (NTerm "E", [newRule 0 (NTerm "E") [N $ NTerm "T", N $ NTerm "E'"]]),
      ( NTerm "E'",
        [ newRule 1 (NTerm "E'") [T $ Term "+", N $ NTerm "T", N $ NTerm "E'"],
          newRule 2 (NTerm "E'") [T Empty]
        ]
      ),
      (NTerm "T", [newRule 3 (NTerm "T") [N $ NTerm "F", N $ NTerm "T'"]]),
      ( NTerm "T'",
        [ newRule 4 (NTerm "T'") [T $ Term "*", N $ NTerm "F", N $ NTerm "T'"],
          newRule 5 (NTerm "T'") [T Empty]
        ]
      ),
      ( NTerm "F",
        [ newRule 6 (NTerm "F") [T $ Term "(", N $ NTerm "E", T $ Term ")"],
          newRule 7 (NTerm "F") [T $ Term "id"]
        ]
      )
    ]
  )

slr1Grammar :: Grammar
slr1Grammar =
  ( NTerm "S",
    [ (NTerm "S", [newRule 0 (NTerm "S") [N $ NTerm "E", T $ Term "$"]]),
      ( NTerm "E",
        [ newRule 1 (NTerm "E") [N $ NTerm "E", T $ Term "+", N $ NTerm "T"],
          newRule 2 (NTerm "E") [N $ NTerm "T"]
        ]
      ),
      ( NTerm "T",
        [ newRule 3 (NTerm "T") [N $ NTerm "T", T $ Term "*", T $ Term "#"],
          newRule 4 (NTerm "T") [T $ Term "#"]
        ]
      )
    ]
  )

lalr1Grammar :: Grammar
lalr1Grammar =
  ( NTerm "S'",
    [ (NTerm "S'", [newRule 0 (NTerm "S'") [N $ NTerm "S", T $ Term "$"]]),
      ( NTerm "S",
        [ newRule 1 (NTerm "S") [N $ NTerm "B", T $ Term "b", T $ Term "b"],
          newRule 2 (NTerm "S") [T $ Term "a", T $ Term "a", T $ Term "b"],
          newRule 3 (NTerm "S") [T $ Term "b", N $ NTerm "B", T $ Term "a"]
        ]
      ),
      (NTerm "B", [newRule 4 (NTerm "B") [T $ Term "a"]])
    ]
  )

lr1Grammar :: Grammar
lr1Grammar =
  ( NTerm "S'",
    [ (NTerm "S'", [newRule 0 (NTerm "S'") [N $ NTerm "S", T $ Term "$"]]),
      ( NTerm "S",
        [ newRule 1 (NTerm "S") [T $ Term "a", N $ NTerm "B", T $ Term "c"],
          newRule 2 (NTerm "S") [T $ Term "b", N $ NTerm "C", T $ Term "c"],
          newRule 3 (NTerm "S") [T $ Term "a", N $ NTerm "C", T $ Term "d"],
          newRule 4 (NTerm "S") [T $ Term "b", N $ NTerm "B", T $ Term "d"]
        ]
      ),
      (NTerm "B", [newRule 5 (NTerm "B") [T $ Term "e"]]),
      (NTerm "C", [newRule 6 (NTerm "B") [T $ Term "e"]])
    ]
  )

-- * helper functions

symbols :: [Rules] -> S.Set Symbol
symbols rules = S.insert (T EOF) $ S.unions $ map (S.fromList . f) rules
  where
    f (n, nss) = N n : concatMap prod nss

closure :: Eq a => (a -> a) -> a -> a
closure f x = let next = f x in if x == next then x else closure f next

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

data Action = Shift State | Reduce RuleIdx | Accept
  deriving (Show, Eq)

-- move from one state to the next
stepState :: Grammar -> Symbol -> S.Set Rule -> S.Set Rule
stepState gram sym old = S.unions $ S.map f old
  where
    f rhs@Rule {prod = l : ls} | l == sym = case ls of
      (N n) : as -> S.insert (rhs {prod = ls}) $ genState n gram
      x -> S.singleton (rhs {prod = x})
    f _ = S.empty

-- create new state from nonterminal
genState :: NTerm -> Grammar -> S.Set Rule
genState n (start, rules) = fst $ closure f (S.fromList seed, seed)
  where
    seed = fromJust $ lookup n rules
    -- process 1 element in the queue
    f :: (S.Set Rule, [Rule]) -> (S.Set Rule, [Rule])
    f (set, q : qs) = foldr tryInsert (set, qs) next
      where
        next = case head $ prod q of
          N n -> fromJust $ lookup n rules
          T t -> []
        tryInsert a (s, ls) = if not (S.member a s) then (S.insert a s, a : ls) else (s, ls)
    f a = a

insertUnique :: Symbol -> Action -> M.Map Symbol Action -> M.Map Symbol Action
insertUnique = M.insertWith (\v vv -> error (show v ++ " collides with " ++ show vv))

type Table = A.Seq (M.Map Symbol Action)

type Table' = A.Seq (S.Set Rule, M.Map Symbol Action)

toTable :: Table' -> Table
toTable = fmap snd

writeTableUnique :: State -> Symbol -> Action -> Table' -> Table'
writeTableUnique i j x = A.adjust' (Bifunctor.second (insertUnique j x)) i

-- an awful name for a funciton that might never be changed
initTable :: (Rule -> S.Set Symbol) -> Grammar -> Table'
initTable reduceSet gram@(start, rules) = setAccept $ fst $ closure f (A.singleton (seed, M.empty), 0)
  where
    syms = symbols rules
    seed = genState start gram
    -- fill in table for state n
    f :: (Table', Int) -> (Table', Int)
    f (sq, n) = case sq A.!? n of
      Just (rhs, _) ->
        let (reduces, shifts) = S.partition ((\a -> null a || a == [T Empty]) . prod) rhs
            foldShifts = S.foldr (g shifts) sq syms
         in (S.foldr (\rule@Rule {index = idx} s -> S.foldr (\t a -> writeTableUnique n t (Reduce idx) a) s (reduceSet rule)) foldShifts reduces, n + 1)
      Nothing -> (sq, n) -- all states filled in
      where
        -- decide whether a new state is needed for taking one step in a Rule
        g :: S.Set Rule -> Symbol -> Table' -> Table'
        g curr s a =
          let nextState = stepState gram s curr
           in if S.null nextState
                then a
                else case A.findIndexL ((== nextState) . fst) a of
                  -- next state already exists in table
                  Just nexti -> writeTableUnique n s (Shift nexti) a
                  -- add new state to table
                  Nothing -> A.adjust' (Bifunctor.second (insertUnique s (Shift $ A.length a))) n a A.|> (nextState, M.empty)
    setAccept = A.adjust' (Bifunctor.second (insertUnique (N start) Accept)) 0

fillReduce :: (Rule -> S.Set Symbol) -> Table' -> Table'
fillReduce reduceSet = fmap (\(rules, table) -> (rules, S.foldr f table rules))
  where
    f rule@Rule {index = i, prod = p} m = if null p then S.foldr (\s m' -> insertUnique s (Reduce i) m') m (reduceSet rule) else m
