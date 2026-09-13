import Graffiti84.LeafLemma
import Mathlib

/-!
# GraphConjecture84

Final arithmetic assembly for Graffiti.pc Conjecture 84.

This file contains no `sorry` and no `axiom`.

The graph-facing theorem is introduced only after the Leaf Lemma and the
Erdos--Saks--Sos / Chung bound have been kernel-formalized in the preceding
layers.  The pure arithmetic closure below is complete.
-/

namespace Graffiti84

/--
Pure arithmetic closure of Graffiti.pc #84.

`r` = radius, `δ` = minimum degree, `t` = largest induced-tree order.

The δ ≥ 2 branch now rests on the geodesic bound `r + 1 ≤ t`
(`BasicFacts`), so the Erdos--Saks--Sos `2r - 1 ≤ t` hypothesis is gone.
-/
theorem final_arithmetic
    (r δ t : ℕ)
    (hr : 1 ≤ r)
    (hδ : 1 ≤ δ)
    (hleaf : δ = 1 → 2 * r ≤ t)
    (hgeod : 2 ≤ δ → r + 1 ≤ t) :
    2 * r ≤ t * δ := by
  by_cases h1 : δ = 1
  · simpa [h1] using hleaf h1
  · have h2 : 2 ≤ δ := by omega
    have ht : r + 1 ≤ t := hgeod h2
    calc
      2 * r ≤ 2 * (r + 1) := by omega
      _ ≤ δ * t := Nat.mul_le_mul h2 ht
      _ = t * δ := Nat.mul_comm _ _

/-!
## Final graph theorem target

After `leafLemma` and the Chung theorem are imported:

```
theorem graphConjecture84
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) :
    2 * G.radius.toNat ≤
      G.largestInducedTreeSize * minDegree G := by
  ...
```

The exact `minDegree` definition should be fixed only after checking the
Mathlib/FormalConjectures API used in the user's local environment.
-/

end Graffiti84
