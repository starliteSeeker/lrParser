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
        Just (Reduce ii@(lhs, i)) ->
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

lr0 :: Grammar -> A.Seq (M.Map Symbol Action)
lr0 g@(_, rules) = commonPartsOfParsers (const $ symbols rules) g

slr1 :: Grammar -> A.Seq (M.Map Symbol Action)
slr1 g@(_, rules) = commonPartsOfParsers (\lhs -> S.map T $ fromJust $ M.lookup lhs followSet) g
  where
    followSet = follow g

-- create all states and fill in Shifts first then fill in Reduces
lalr1 :: Grammar -> A.Seq (M.Map Symbol Action)
lalr1 g@(_, rules) = fillReduce $ fillFollow $ commonPartsOfParsers (const S.empty) g
  where
    fillReduce sq = A.mapWithIndex undefined sq
    fillFollow sq = closure undefined sq
