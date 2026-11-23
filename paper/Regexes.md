# Regexes used

To replace (eval $1 $2) with ⟦ $1 ⟧ₜ $2:

```regex
eval\s+([^\(\{\)\}\s]+|[\(\{][^)}]+[\)\}])\s+([^\s\(\{\}]+|[\(\{][^\s]+[\)\}])
```

To match `Pred Δ R[κ]` and `Pred Δ R[κ]`:

```regex
Pred\s+([^\(\{\)\}\s]+)\s+(R\[[^\]]+\]|[^\s\(\{\}\)]+)
```

## 

```tex
\Datatype{\Name{Kinds.Syntax}{Kind}}
\Type[Types.Syntax][Type.Π]{Π}
\Term{\Name[Agda]{Builtin.Unit}{⊤}}
\Term{\Name{Types.Renaming}{ren}}
\Function{\Name{Kinds.Syntax}{Kind}}
\Constructor[Types.Syntax][Type.Π]{Π}
\Typeclass{\Name{Types.Substitution}{\Underscore{}[\Underscore{}]ₛ}}
```
Regexes:

```regex
regex:        (Datatype|Type|Term|Function|Constructor|Typeclass)\{\\Name\{([^}]+)\}\{([^}]+)\}\}
replace with: $1[$2]{$3}
regex:        (Datatype|Type|Term|Function|Constructor|Typeclass)\{\\AName\{([^}]+)\}\{([^}]+)\}\{([^}]+)\}\}
replace with: $1[$2][$3]{$4}
```

