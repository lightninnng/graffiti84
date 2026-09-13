import Graffiti84.RadiusCriticalStructure
import Mathlib

/-!
# LeafLemma

This layer is reserved for the strong leaf lemma

  if `G` is finite, connected, and has a leaf, then
  `2 * radius(G) <= largestInducedTreeSize(G)`.

There are no `sorry`/`axiom` declarations in this snapshot.

The final theorem is intentionally not declared until both of its classical
ingredients are kernel-formalized:
1. the radius-drop / UEP criterion,
2. the theorem-specific vrd cut-vertex structure closure.

This file already contains the fully formal arithmetic inequality required
for the corona-count branch and the final leaf-extension counting helper.
-/

namespace Graffiti84

open Classical
open SimpleGraph

/--
Arithmetic core of the vrd-corona Case A:
for core radius `s >= 2` and pendant length `l >= 1`,
the induced tree constructed above a Chung path has at least `2(s+l)` vertices.
-/
theorem corona_tree_count
    {s l : ℕ} (hs : 2 ≤ s) (hl : 1 ≤ l) :
    2 * (s + l) ≤ (2 * s - 1) * (l + 1) := by
  omega

/--
F13 (geodesic count): for `s, l >= 1`, a geodesic of the core block with all
full-length pendant paths already yields `(s+1)(l+1) >= 2(s+l)` vertices.
This replaces the ESS-based count `corona_tree_count` in the simplified proof.
-/
theorem tip_tree_count
    {s l : ℕ} (hs : 1 ≤ s) (hl : 1 ≤ l) :
    2 * (s + l) ≤ (s + 1) * (l + 1) := by
  nlinarith [hs, hl]

/-- Radius-one core case: `S_l(K₂)` has exactly `2(l+1)=2r` vertices. -/
theorem radius_one_core_count (l : ℕ) :
    2 * (1 + l) = 2 * l + 2 := by
  omega

/--
If one already has an induced path/tree witness on `2r-1` old vertices and
adds a genuinely new leaf, the resulting order is at least `2r`.
-/
theorem add_leaf_count {r n : ℕ}
    (h : 2 * r - 1 ≤ n) :
    2 * r ≤ n + 1 := by
  omega

/--
Elementary reduction used in the minimal-counterexample proof:
if a smaller leaf graph has radius at least `r`, its `2*radius` tree bound
is already enough for the original target.
-/
theorem smaller_radius_bound_mono
    {r r' t : ℕ}
    (hrr : r ≤ r')
    (ht : 2 * r' ≤ t) :
    2 * r ≤ t := by
  omega

/-!
## Final theorem target

Once `RadiusCriticalStructure.lean` has the two missing structural lemmas and
the rooted Chung lemma has been ported from the already-formalized WOWII #31
proof, declare and prove:

```
theorem leafLemma
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hleaf : ∃ u : α, G.degree u = 1) :
    2 * G.radius.toNat ≤ G.largestInducedTreeSize := by
  ...
```

No placeholder theorem is introduced before that proof is available.
-/

end Graffiti84
