# lrParser

Me trying to understand LR parsers by writing code but ending up confused over my own code.

```
ghci> printAST $ parseWith lalr1 lalr1Grammar $ fmap (T . Term) ["b", "a", "a", "$"]
N (NTerm "S'")
|
+- N (NTerm "S")
|  |
|  +- T (Term "b")
|  |
|  +- N (NTerm "B")
|  |  |
|  |  `- T (Term "a")
|  |
|  `- T (Term "a")
|
`- T (Term "$")
ghci> slr1 lalr1Grammar 
fromList *** Exception: Reduce (Idx {ruleNo = 4, leftSym = NTerm "B"}) collides with Shift 9
CallStack (from HasCallStack):
  error, called at src/Parser/Internal.hs:214:39 in lrParser-0.1.0.0-inplace:Parser.Internal
```