# lrParser

Me trying to understand LR parsers by writing code but ending up confused over my own code.

```
ghci> printAST $ parseWith slr1 notlr0 [T $ Term "#", T $ Term "+", T $ Term "#", T $ Term "*", T $ Term "#", T $ Term "$"]
N (NTerm "S")
|
+- N (NTerm "E")
|  |
|  +- N (NTerm "E")
|  |  |
|  |  `- N (NTerm "T")
|  |     |
|  |     `- T (Term "#")
|  |
|  +- T (Term "+")
|  |
|  `- N (NTerm "T")
|     |
|     +- N (NTerm "T")
|     |  |
|     |  `- T (Term "#")
|     |
|     +- T (Term "*")
|     |
|     `- T (Term "#")
|
`- T (Term "$")
```