import Graffiti84.RadiusCriticalStructure
import Graffiti84.CaseB
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

/-- A cycle cannot contain a degree-one vertex. -/
lemma leaf_not_mem_cycle {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {u x : α} (hu : G.degree u = 1)
    {p : G.Walk x x} (hp : p.IsCycle) : u ∉ p.support := by
  intro hmem
  have hc := hp.rotate hmem
  exact hc.snd_ne_penultimate
    (adj_eq_of_degree_eq_one hu
      ((p.rotate u hmem).adj_snd hc.not_nil)
      ((p.rotate u hmem).adj_penultimate hc.not_nil).symm)

/-- Adding a leaf adjacent to a vertex of an induced tree preserves the tree. -/
theorem isInducedTree_insert_leaf {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {S : Finset α} {u a : α}
    (hS : IsInducedTree G S) (ha : a ∈ S)
    (hu : G.degree u = 1) (hua : G.Adj u a) :
    IsInducedTree G (insert u S) := by
  have to_a : ∀ z ∈ insert u S, ConnectsWithin G (insert u S) z a := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzu | hzS
    · subst z
      refine ⟨hua.toWalk, ?_⟩
      intro z hz
      simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.mem_singleton] at hz
      rcases hz with hz | hz
      · rw [hz]; exact Finset.mem_insert_self u S
      · rw [hz]; exact Finset.mem_insert_of_mem ha
    · obtain ⟨p, hp⟩ := hS.1 z hzS a ha
      exact ⟨p, fun w hw => Finset.mem_insert_of_mem (hp w hw)⟩
  constructor
  · intro x hx y hy
    obtain ⟨p, hp⟩ := to_a x hx
    obtain ⟨q, hq⟩ := to_a y hy
    refine ⟨p.append q.reverse, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hz
    exact hz.elim (hp z) (hq z)
  · intro x p hp
    right
    intro hcycle
    have havoid := leaf_not_mem_cycle hu hcycle
    have hinside : ∀ z ∈ p.support, z ∈ S := by
      intro z hz
      rcases Finset.mem_insert.mp (hp z hz) with hzu | hzS
      · exact (havoid (hzu ▸ hz)).elim
      · exact hzS
    rcases hS.2 x p hinside with hzero | hnot
    · have := hcycle.three_le_length
      omega
    · exact hnot hcycle

/-- The graph-level counting step at the end of Case B. -/
theorem treeNumber_ge_of_rooted_tree_and_leaf {α : Type*} [Fintype α]
    [DecidableEq α] {G : SimpleGraph α} {S : Finset α} {u a : α} {r : ℕ}
    (hS : IsInducedTree G S) (ha : a ∈ S) (huS : u ∉ S)
    (hu : G.degree u = 1) (hua : G.Adj u a) (hcard : 2 * r - 1 ≤ S.card) :
    2 * r ≤ treeNumber G := by
  have ht := isInducedTree_insert_leaf hS ha hu hua
  have hbound : (insert u S).card ≤ treeNumber G :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
  rw [Finset.card_insert_of_notMem huS] at hbound
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
