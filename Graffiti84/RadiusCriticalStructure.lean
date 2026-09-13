import Mathlib

/-!
# RadiusCriticalStructure

Lean 4.32.2 / Mathlib 4.32.2.

This module contains the radius-critical / unique-eccentric-point layer used
in the proof of Graffiti.pc Conjecture 84.

Status of this snapshot:
* no `sorry`
* no `axiom`
* all declared theorems are intended to be genuinely proved
* the full Gliviak--Fajtlowicz vrd-corona theorem is NOT declared yet; its
  exact target is recorded at the bottom of this file.

The purpose of this file is to give a clean kernel-safe base that can be
extended locally until the structure theorem is completely formalized.
-/

namespace Graffiti84

open Classical
open SimpleGraph

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Natural-valued radius. -/
noncomputable def radiusNat (G : SimpleGraph α) : ℕ :=
  G.radius.toNat

/-- Natural-valued eccentricity. -/
noncomputable def eccNat (G : SimpleGraph α) (v : α) : ℕ :=
  G.eccent v |>.toNat

/-- A vertex is central iff it realizes the graph radius. -/
def IsCentral (G : SimpleGraph α) (v : α) : Prop :=
  G.eccent v = G.radius

/--
`x` is the unique eccentric point of `c`: it is eccentric from `c`, and no
other vertex is as far from `c`.
-/
def IsUniqueEccentricPoint (G : SimpleGraph α) (c x : α) : Prop :=
  G.dist c x = (G.eccent c).toNat ∧
    ∀ y : α, y ≠ x → G.dist c y < (G.eccent c).toNat

/-- Every vertex of a connected finite nontrivial graph has positive eccentricity. -/
lemma eccNat_pos_of_connected_nontrivial
    [Nontrivial α] {G : SimpleGraph α} (hG : G.Connected) (v : α) :
    0 < eccNat G v := by
  obtain ⟨w, hw⟩ := exists_ne v
  have hr : G.Reachable v w := hG.preconnected v w
  have hdpos : 0 < G.dist v w := hr.pos_dist_of_ne hw
  have hle : G.dist v w ≤ (G.eccent v).toNat := by
    simpa [SimpleGraph.eccent] using
      (Finset.le_sup (Finset.univ.image fun x => G.dist v x)
        (G.dist v w) (by simp))
  exact lt_of_lt_of_le hdpos hle

/--
Elementary finite auxiliary-graph lemma used in Case B of the Leaf Lemma.

If a finite simple graph has minimum degree at least one and every vertex
except `a` has a degree-one neighbour, then `a` also has a degree-one
neighbour.
-/
theorem degree_one_neighbor_of_all_other
    (D : SimpleGraph α) [DecidableRel D.Adj] (a : α)
    (hpos : ∀ v : α, 1 ≤ D.degree v)
    (hother :
      ∀ v : α, v ≠ a →
        ∃ w : α, D.Adj v w ∧ D.degree w = 1) :
    ∃ w : α, D.Adj a w ∧ D.degree w = 1 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hax⟩ : ∃ x, D.Adj a x := by
    have ha : 0 < D.degree a := lt_of_lt_of_le Nat.zero_lt_one (hpos a)
    simpa [SimpleGraph.degree_pos_iff_exists_adj] using ha
  have hxne : x ≠ a := (D.ne_of_adj hax).symm
  have hxdeg_ne : D.degree x ≠ 1 := by
    intro hx1
    exact h x hax hx1
  have hxdeg2 : 2 ≤ D.degree x := by
    have hx1 : 1 ≤ D.degree x := hpos x
    omega
  obtain ⟨y, hxy, hy1⟩ := hother x hxne
  by_cases hya : y = a
  · subst y
    have ha1 : D.degree a = 1 := hy1
    have hx_two_neighbors :
        ∃ z : α, D.Adj x z ∧ z ≠ a := by
      have hcard : 2 ≤ (D.neighborFinset x).card := by simpa using hxdeg2
      have ha_mem : a ∈ D.neighborFinset x := by
        simpa using hax.symm
      obtain ⟨z, hzmem, hzne⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_mem
          (f := id) (s := D.neighborFinset x) a ha_mem
          (by simpa using hcard)
      exact ⟨z, by simpa using hzmem, hzne⟩
    obtain ⟨z, hxz, hzne⟩ := hx_two_neighbors
    obtain ⟨w, hzw, hw1⟩ := hother z (by
      intro hza
      exact hzne hza)
    have hwne_a : w ≠ a := by
      intro hwa
      subst w
      have haz : D.Adj a z := hzw.symm
      have hzax : z = x := by
        have ha_neighbors : D.neighborFinset a = {x} := by
          apply Finset.eq_singleton_iff_unique_mem.2
          constructor
          · simpa using hax
          · intro q hq
            have hqadj : D.Adj a q := by simpa using hq
            have hqmem : q ∈ D.neighborFinset a := by simpa using hqadj
            have hcard1 : (D.neighborFinset a).card = 1 := by simpa using ha1
            have hs : D.neighborFinset a = {x} := by
              apply Finset.eq_singleton_iff_unique_mem.2
              exact ⟨by simpa using hax, by
                intro b hb
                have : b = x := by
                  rw [Finset.card_eq_one] at hcard1
                  rcases hcard1 with ⟨c, hc⟩
                  have hxc : x = c := by
                    have : x ∈ ({c} : Finset α) := by simpa [hc] using (show x ∈ D.neighborFinset a by simpa using hax)
                    simpa using this
                  have hbc : b = c := by
                    have : b ∈ ({c} : Finset α) := by simpa [hc] using hb
                    simpa using this
                  exact hbc.trans hxc.symm
                exact this⟩
            have : z ∈ ({x} : Finset α) := by simpa [ha_neighbors] using (show z ∈ D.neighborFinset a by simpa using haz)
            simpa using this
        exact hzne hzax
      )
    have hwne_x : w ≠ x := by
      intro hwx
      subst w
      exact hxdeg_ne hw1
    have hzdeg2 : 2 ≤ D.degree z := by
      have hzx : D.Adj z x := hxz.symm
      have hzw' : D.Adj z w := hzw
      have hne : x ≠ w := Ne.symm hwne_x
      have hcard2 : 2 ≤ (D.neighborFinset z).card := by
        have hxmem : x ∈ D.neighborFinset z := by simpa using hzx
        have hwmem : w ∈ D.neighborFinset z := by simpa using hzw'
        exact Finset.two_le_card.mpr ⟨x, hxmem, w, hwmem, hne⟩
      simpa using hcard2
    obtain ⟨q, hwq, hq1⟩ := hother w hwne_a
    have hqz : q = z := by
      have hwcard1 : (D.neighborFinset w).card = 1 := by simpa using hw1
      rw [Finset.card_eq_one] at hwcard1
      rcases hwcard1 with ⟨c, hc⟩
      have hzc : z = c := by
        have : z ∈ ({c} : Finset α) := by
          simpa [hc] using (show z ∈ D.neighborFinset w by simpa using hzw.symm)
        simpa using this
      have hqc : q = c := by
        have : q ∈ ({c} : Finset α) := by
          simpa [hc] using (show q ∈ D.neighborFinset w by simpa using hwq)
        simpa using this
      exact hqc.trans hzc.symm
    subst q
    omega
  · exact h y hax hya hy1

/-!
## Remaining theorem-specific structure target

The full local formalization still needed for the Case-A branch is the
Gliviak--Fajtlowicz / Swart vertex-radius-decreasing structure theorem.

We intentionally DO NOT declare it as an axiom.

Target mathematical interface:

```
theorem vrd_with_cut_vertex_has_equal_pendant_path_structure ...
```

It should produce enough data to construct an induced tree of order at least
`2 * radiusNat G`; a full graph-isomorphism-to-corona statement is stronger
than necessary and is therefore not required.
-/

end Graffiti84
