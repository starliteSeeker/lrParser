module Parser where

import qualified Data.Bifunctor as Bifunctor
import Data.List (find)
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust)
import qualified Data.Sequence as A
import qualified Data.Set as S
import qualified Data.Tree as T
import Parser.Internal

type Table = A.Seq (M.Map Symbol Action)

leaf :: a -> T.Tree a
leaf x = T.Node x []

printAST :: T.Tree Symbol -> IO ()
printAST = putStrLn . T.drawTree . fmap show

parseWith :: (Grammar -> Table) -> Grammar -> [Symbol] -> T.Tree Symbol
parseWith parser grammar ls = parse' 0 [] $ map leaf ls
  where
    table = parser grammar
    parse' state stack ll@(l : ls) =
      case M.lookup (T.rootLabel l) (fromJust $ table A.!? state) of
        -- shift token onto stack
        Just (Shift i) -> parse' i ((l, state) : stack) ls
        -- take tokens from stack and put pack to queue
        Just (Reduce i lhs) ->
          let rhs = fromJust $ find ((== i) . index) $ fromJust $ lookup lhs (snd grammar)
              (matched, rest) = Bifunctor.first reverse $ splitAt (length $ prod rhs) stack
              checkMatch :: [(T.Tree Symbol, Int)] -> [Symbol] -> Int
              checkMatch m r =
                if and (zipWith (\a b -> T.rootLabel (fst a) == b) m r)
                  then snd $ head m -- return which state to backtrack to
                  else error "why"
           in if prod rhs == [T Empty]
                then parse' state stack (T.Node (N lhs) [T.Node (T Empty) []] : ll)
                else parse' (checkMatch matched (prod rhs)) rest (T.Node (N lhs) (map fst matched) : ll)
        Just Accept -> l
        Nothing -> error $ "didn't expect " ++ show ll ++ show state ++ show stack
    parse' state stack [] = parse' state stack [leaf $ T EOF]

lr0 :: Grammar -> A.Seq (M.Map Symbol Action)
lr0 gram@(start, rules) = setAccept $ fmap snd $ fst $ closure f (A.singleton (seed, M.empty), 0)
  where
    syms = symbols rules
    seed = genState start gram
    -- fill in table for state n
    f :: (A.Seq (S.Set RHS, M.Map Symbol Action), Int) -> (A.Seq (S.Set RHS, M.Map Symbol Action), Int)
    f (sq, n) = case sq A.!? n of
      Just (rhs, _) -> case Bifunctor.bimap S.toList S.toList (S.partition ((== []) . prod) rhs) of
        -- no reduce possible
        ([], _) -> (S.foldr (g rhs) sq syms, n + 1)
        -- only one reduce possible
        ([RHS {index = i, lhs = lhs}], []) ->
          (A.adjust' (Bifunctor.second (const $ M.fromSet (const $ Reduce i lhs) syms)) n sq, n + 1)
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
                  Just nexti -> writeTableUnique n s (Shift nexti) a
                  -- add new state to table
                  Nothing -> writeTableUnique n s (Shift $ A.length a) a A.|> (nextState, M.empty)
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
        let (reduces, shifts) = S.partition ((\a -> null a || a == [T Empty]) . prod) rhs
            foldShifts = S.foldr (g shifts) sq syms
         in (S.foldr (\RHS {index = i, lhs = lhs} s -> S.foldr (\t a -> writeTableUnique n (T t) (Reduce i lhs) a) s (fromJust $ M.lookup lhs followSet)) foldShifts reduces, n + 1)
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
                  Just nexti -> writeTableUnique n s (Shift nexti) a
                  -- add new state to table
                  Nothing -> A.adjust' (Bifunctor.second (insertUnique s (Shift $ A.length a))) n a A.|> (nextState, M.empty)
    setAccept = A.adjust' (insertUnique (N start) Accept) 0

insertUnique :: Symbol -> Action -> M.Map Symbol Action -> M.Map Symbol Action
insertUnique = M.insertWith (\v vv -> error (show v ++ " collides with " ++ show vv))

writeTableUnique :: State -> Symbol -> Action -> A.Seq (S.Set RHS, M.Map Symbol Action) -> A.Seq (S.Set RHS, M.Map Symbol Action)
writeTableUnique i j x = A.adjust' (Bifunctor.second (insertUnique j x)) i
