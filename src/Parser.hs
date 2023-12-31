module Parser where

import qualified Data.Bifunctor as Bifunctor
import Data.List (find)
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust)
import qualified Data.Sequence as A
import qualified Data.Set as S
import qualified Data.Tree as T
import Parser.Internal

leaf :: a -> T.Tree a
leaf x = T.Node x []

printAST :: T.Tree Symbol -> IO ()
printAST = putStrLn . T.drawTree . fmap show

parseWith :: (Grammar -> Table) -> Grammar -> [Symbol] -> T.Tree Symbol
parseWith parser grammar ls = parse' 0 [] $ map leaf ls
  where
    table = parser grammar
    parse' state stack ll@(l : ls) =
      case M.lookup (T.rootLabel l) $ fromJust $ table A.!? state of
        -- shift token onto stack
        Just (Shift i) -> parse' i ((l, state) : stack) ls
        -- take tokens from stack and put pack to queue
        Just (Reduce ii@Idx {leftSym = lhs, ruleNo = i}) ->
          let rhs = fromJust $ find ((== ii) . index) $ fromJust $ lookup lhs (snd grammar)
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

lr0 :: Grammar -> Table
lr0 g@(_, rules) = toTable $ initTable (const $ symbols rules) g

slr1 :: Grammar -> Table
slr1 g@(_, rules) = toTable $ initTable f g
  where
    followS = follow g
    f rule = S.map T $ fromJust $ M.lookup (leftSym $ index rule) followS

-- create table with shift and accept only -> calculate follow set for each rule instate -> fill in reduce based on follow set
lalr1 :: Grammar -> Table
lalr1 gram@(start, allRules) = toTable $ fillReduce (S.map T . followI) $ closure (fillEdge2 . fillEdge1) $ fillEOF common
  where
    common = initTable (const S.empty) gram
    firstS = first gram
    -- edges in a state (S' -> . S $ to S -> . + E E)
    fillEdge1 = fmap (\(rules, table) -> (S.foldr fillEdge1' rules rules, table))
    fillEdge1' :: Rule -> S.Set Rule -> S.Set Rule
    fillEdge1' rule@Rule {prod = N s : ss, followI = followR} rules =
      let f = first' ss
          extRules = S.fromList $ fromJust $ lookup s allRules
       in if S.member Empty f then S.foldr (updateFollow (f <> followR)) rules extRules else S.foldr (updateFollow f) rules extRules
    fillEdge1' _ rules = rules
    -- edges between states (S -> . + E E to S -> + . E E)
    fillEdge2 sq = foldr (\(rules, table) sq' -> S.foldr (fillEdge2' table) sq' rules) sq sq
    fillEdge2' table rule@Rule {prod = s : ss, followI = f} = A.adjust' (Bifunctor.first (updateFollow f rule {prod = ss})) (let Shift x = fromJust $ M.lookup s table in x)
    fillEdge2' _ _ = id
    -- first set of a list of symbols
    first' (N n : ss) =
      let f = fromJust $ M.lookup n firstS
       in if S.member Empty f then f <> first' ss else f
    first' (T t : ss) = S.singleton t
    first' _ = S.empty
    updateFollow newSet rule@Rule {index = i1, prod = p1} =
      S.map
        ( \r2@Rule {index = i2, prod = p2, followI = f2} ->
            if i1 == i2 && p1 == p2
              then r2 {followI = newSet <> f2}
              else r2
        )
    fillEOF =
      A.adjust'
        ( Bifunctor.first $
            S.map
              ( \k@Rule {index = Idx {leftSym = lhs}, followI = f} ->
                  if lhs == start then k {followI = S.insert EOF f} else k
              )
        )
        0
