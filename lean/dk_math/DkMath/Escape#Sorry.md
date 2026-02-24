# Sorry を置いておくファイル

```lean
-- DkMath.CellDim.lean#L59
/- `translate` は和集合に分配（map の性質）。-/
lemma translate_union (v : Cell d) (A B : Finset (Cell d)) :
  translate (d := d) v (A ∪ B) = translate (d := d) v A ∪ translate (d := d) v B := by sorry
```
