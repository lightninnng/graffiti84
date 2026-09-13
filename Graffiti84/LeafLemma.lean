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
F13 (geodesic count): for `s, l >= 1`, a geodesic of the core block with all
full-length pendant paths already yields `(s+1)(l+1) >= 2(s+l)` vertices.
This is the count used by the simplified proof (Corollary 3.B in
`docs/full-proof.md`); the ESS-based count of the original draft is gone.
-/
theorem tip_tree_count
    {s l : ℕ} (hs : 1 ≤ s) (hl : 1 ≤ l) :
    2 * (s + l) ≤ (s + 1) * (l + 1) := by
  nlinarith [hs, hl]

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
