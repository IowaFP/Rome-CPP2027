# Regexes used

To replace (eval $1 $2) with ⟦ $1 ⟧ₜ $2:

```regex
eval\s+([^\(\{\)\}\s]+|[\(\{][^)}]+[\)\}])\s+([^\s\(\{\}]+|[\(\{][^\s]+[\)\}])
```

To match `Pred Δ R[κ]` and `Pred Δ R[κ]`:

```regex
Pred\s+([^\(\{\)\}\s]+)\s+(R\[[^\]]+\]|[^\s\(\{\}\)]+)
```