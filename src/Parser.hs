module Parser where

import qualified Data.Bifunctor as Bifunctor
import qualified Data.Map.Strict as M
import qualified Data.Sequence as A
import qualified Data.Set as S
import Parser.Internal

lr0 :: Grammar -> A.Seq (M.Map Symbol Action)
lr0 gram@(start, rules) = setAccept $ fmap snd $ fst $ closure f (A.singleton (seed, M.empty), 0)
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
    setAccept = A.adjust' (insertUnique (N start) Accept) 0

-- maybe some way to reduce repeated code from lr0
slr1 :: Grammar -> A.Seq (M.Map Symbol Action)
slr1 gram@(start, rules) = setAccept $ fmap snd $ fst $ closure f (A.singleton (seed, M.empty), 0)
  where
    syms = symbols rules
    seed = genState start gram
    followSet = follow gram
    -- fill in table for state n
    f :: (A.Seq (S.Set RHS, M.Map Symbol Action), Int) -> (A.Seq (S.Set RHS, M.Map Symbol Action), Int)
    f (sq, n) = case sq A.!? n of
      Just (rhs, _) ->
        let (shifts, reduces) = (S.partition ((== []) . snd) rhs)
         in (S.foldr (g shifts) sq syms, n + 1) -- where is lhs
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
    setAccept = A.adjust' (insertUnique (N start) Accept) 0

insertUnique :: Symbol -> Action -> M.Map Symbol Action -> M.Map Symbol Action
insertUnique = M.insertWith (\v vv -> error (show v ++ " collides with " ++ show vv))
