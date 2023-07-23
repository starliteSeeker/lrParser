module LR0 (closure) where

import qualified Data.Bifunctor as Bifunctor
import Data.Function (on)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, isJust, isNothing)
import qualified Data.Sequence as A
import qualified Data.Set as S

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
  | Term String
  deriving (Show, Eq, Ord)

type RHS = (Index, [Symbol])

type Rule = (NTerm, [RHS])

type Index = Int -- index for rules

type Grammar = (NTerm, [Rule]) -- (start symbol, rewriting rules)

testGrammer :: Grammar
testGrammer =
  ( NTerm "S",
    [ (NTerm "S", [(0, [N $ NTerm "E", T $ Term "$"])]),
      ( NTerm "E",
        [ (1, [T $ Term "+", N $ NTerm "E", N $ NTerm "E"]),
          (2, [T $ Term "#"])
        ]
      )
    ]
  )

notlr0 :: Grammar
notlr0 =
  ( NTerm "S",
    [ (NTerm "S", [(0, [N $ NTerm "E", T $ Term "$"])]),
      ( NTerm "E",
        [ (1, [N $ NTerm "E", T $ Term "+", N $ NTerm "T"]),
          (2, [N $ NTerm "T"])
        ]
      ),
      ( NTerm "T",
        [ (3, [N $ NTerm "T", T $ Term "*", T $ Term "#"]),
          (4, [T $ Term "#"])
        ]
      )
    ]
  )

g2 :: Grammar
g2 =
  ( NTerm "E",
    [ (NTerm "E", [(0, [N $ NTerm "T", N $ NTerm "E'"])]),
      (NTerm "E'", [(1, [T $ Term "+", N $ NTerm "T", N $ NTerm "E'"]), (2, [T Empty])]),
      (NTerm "T", [(3, [N $ NTerm "F", N $ NTerm "T'"])]),
      (NTerm "T'", [(4, [T $ Term "*", N $ NTerm "F", N $ NTerm "T'"]), (5, [T Empty])]),
      (NTerm "F", [(6, [T $ Term "(", N $ NTerm "E", T $ Term ")"]), (7, [T $ Term "id"])])
    ]
  )

symbols :: [Rule] -> S.Set Symbol
symbols rules = S.unions $ map (S.fromList . f) rules
  where
    f (n, nss) = N n : concatMap snd nss

closure :: Eq a => (a -> a) -> a -> a
-- closure f x = let next = f x in if x == next then x else closure f next
closure = closureBy (==)

closureBy :: (a -> a -> Bool) -> (a -> a) -> a -> a
closureBy eq f x = let next = f x in if x `eq` next then x else closureBy eq f next

-- calculate first set for a grammer
first :: Grammar -> M.Map NTerm (S.Set Term)
first (_, rules) = closure (\m -> foldr f m rules) seed
  where
    seed = M.fromList $ [(e, S.empty) | N e <- S.elems $ symbols rules]
    -- update first set with a rule
    f :: Rule -> M.Map NTerm (S.Set Term) -> M.Map NTerm (S.Set Term)
    f (l, rss) m = M.insertWith S.union l (S.unions $ map (f' . snd) rss) m
      where
        -- calculate first set with rhs of rule
        f' :: [Symbol] -> S.Set Term
        f' (x : xs) = case x of
          (N n) -> let a = m M.! n in if S.member Empty a then S.union a (f' xs) else a
          (T Empty) -> f' xs
          (T t) -> S.singleton t
        f' [] = S.singleton Empty

type State = Int

data Action = Shift State | Reduce Index | Accept
  deriving (Show, Eq)

parseTable :: Grammar -> A.Seq (S.Set RHS, M.Map Symbol Action)
parseTable gram@(start, rules) = setAccept $ fst $ closure f (A.singleton (seed, M.empty), 0)
  where
    syms = symbols rules
    seed = genState start gram
    -- fill in table for state n
    f :: (A.Seq (S.Set RHS, M.Map Symbol Action), Int) -> (A.Seq (S.Set RHS, M.Map Symbol Action), Int)
    f (sq, n) = case sq A.!? n of
      Just (rhs, _) -> case Bifunctor.bimap S.toList S.toList (S.partition ((== []) . snd) rhs) of
        -- no reduce possible
        ([], _) -> (S.foldr (g rhs) sq syms, n + 1)
        -- only one reduce possible
        ([(i, _)], []) ->
          (A.adjust' (Bifunctor.second (const $ M.fromSet (const $ Reduce i) syms)) n sq, n + 1)
        -- multiple reduces possible
        _ -> error "not lr0, multiple reduces possible"
      Nothing -> (sq, n) -- all states filled in
      where
        -- decide whether a new state is needed for taking one step in a RHS
        g :: S.Set RHS -> Symbol -> A.Seq (S.Set RHS, M.Map Symbol Action) -> A.Seq (S.Set RHS, M.Map Symbol Action)
        g curr s a =
          let nextState = stepState gram s curr
           in if S.null nextState
                then a
                else case A.findIndexL ((== nextState) . fst) a of
                  -- next state already exists in table
                  Just nexti -> A.adjust' (Bifunctor.second (insertUnique s (Shift nexti))) n a
                  -- add new state to table
                  Nothing -> A.adjust' (Bifunctor.second (insertUnique s (Shift $ A.length a))) n a A.|> (nextState, M.empty)
    setAccept = A.adjust' (Bifunctor.second (insertUnique (N start) Accept)) 0

insertUnique :: Symbol -> Action -> M.Map Symbol Action -> M.Map Symbol Action
insertUnique = M.insertWith (\v vv -> error (show v ++ " collides with " ++ show vv))

-- move from one state to the next
stepState :: Grammar -> Symbol -> S.Set RHS -> S.Set RHS
stepState gram sym old = S.unions $ S.map f old
  where
    f (i, l : ls) | l == sym = case ls of
      (N n) : as -> S.insert (i, ls) $ genState n gram
      x -> S.singleton (i, x)
    f _ = S.empty

-- create new state from nonterminal
genState :: NTerm -> Grammar -> S.Set RHS
genState n (start, rules) = fst $ closure f (S.fromList seed, seed)
  where
    seed = fromMaybe (error "you what") $ lookup n rules
    -- process 1 element in the queue
    f :: (S.Set RHS, [RHS]) -> (S.Set RHS, [RHS])
    f (set, q : qs) = foldr tryInsert (set, qs) next
      where
        next = case head $ snd q of
          N n -> fromMaybe undefined $ lookup n rules
          T t -> []
        tryInsert a (s, ls) = if not (S.member a s) then (S.insert a s, a : ls) else (s, ls)
    f a = a
