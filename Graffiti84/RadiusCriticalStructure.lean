import Mathlib
import Graffiti84.BasicFacts

/-!
# RadiusCriticalStructure

Lean 4.32.2 / Mathlib 4.32.2.

This module contains the radius-critical / unique-eccentric-point layer used
in the proof of Graffiti.pc Conjecture 84.

Status of this snapshot:
* no forbidden proof placeholders and no custom declarations by assumption;
* all declared theorems are genuinely proved (CI-audited);
* the full Gliviak--Fajtlowicz vrd-corona structure theorem is NOT declared
  yet; its exact target is recorded at the bottom of this file.

The auxiliary lemma `degree_one_neighbor_of_all_other` is the formal
counterpart of Lemma F15 in `docs/full-proof.md`; the eccentricity lemma
formalizes F5/F6 prerequisites.  Both were rewritten against the actual
Mathlib `Diam`/`Metric` API (`eccent` as an `ENat` iSup, `edist`, `dist`).
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

-- `IsCentral` and `IsUniqueEccentricPoint` now live in `BasicFacts`
-- (together with F9).

/--
Every vertex of a connected finite nontrivial graph has positive
eccentricity (F5/F6 prerequisite).
-/
lemma eccNat_pos_of_connected_nontrivial
    [Nontrivial α] {G : SimpleGraph α} (hG : G.Connected) (v : α) :
    0 < eccNat G v := by
  obtain ⟨x, hx⟩ := G.exists_edist_eq_eccent_of_finite v
  have hxt : G.eccent v ≠ ⊤ := fun h =>
    G.edist_ne_top_iff_reachable.mpr (hG.preconnected v x) (by rw [hx, h])
  have hne0 : G.eccent v ≠ 0 := G.eccent_ne_zero v
  have hpos : 0 < G.eccent v := by
    by_contra h0
    exact hne0 (le_antisymm (not_lt.mp h0) zero_le)
  simp only [eccNat]
  exact ENat.toNat_pos hne0 hxt

/--
Elementary finite auxiliary-graph lemma used in Case B of the Leaf Lemma
(F15 in `docs/full-proof.md`).

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
  -- The neighbour of a degree-one vertex is unique.
  have uniq_nb : ∀ {v u z : α}, D.degree v = 1 → D.Adj v u → D.Adj v z → z = u := by
    intro v u z hv1 hvu hvz
    have hcard : (D.neighborFinset v).card = 1 := by simpa using hv1
    rw [Finset.card_eq_one] at hcard
    obtain ⟨c, hc⟩ := hcard
    have hzu : z ∈ ({c} : Finset α) := by rw [← hc]; simpa using hvz
    have huu : u ∈ ({c} : Finset α) := by rw [← hc]; simpa using hvu
    simp only [Finset.mem_singleton] at hzu huu
    exact hzu.trans huu.symm
  obtain ⟨x, hax⟩ : ∃ x, D.Adj a x := by
    have ha : 0 < D.degree a := lt_of_lt_of_le Nat.zero_lt_one (hpos a)
    simpa [SimpleGraph.degree_pos_iff_exists_adj] using ha
  have hxa : x ≠ a := (D.ne_of_adj hax).symm
  have hx1 : D.degree x ≠ 1 := h x hax
  -- Step 1: some degree-one neighbour `y` of `x` must be `a` itself.
  obtain ⟨y, hxy, hy1⟩ := hother x hxa
  have hya : a = y := by
    by_contra hyne
    obtain ⟨y', hy'x, hy'1⟩ := hother y (Ne.symm hyne)
    have hyy' : y' = x := uniq_nb hy1 hxy.symm hy'x
    exact hx1 (hyy' ▸ hy'1)
  subst hya
  -- So `deg(a) = 1` and `x` is the unique neighbour of `a`.
  have ha1 : D.degree a = 1 := hy1
  have hamem : a ∈ D.neighborFinset x := by simpa using hax.symm
  have hx2 : 2 ≤ (D.neighborFinset x).card := by
    have h1 : 1 ≤ D.degree x := hpos x
    simpa using (show 2 ≤ D.degree x by omega)
  -- Step 2: pick another neighbour `z ≠ a` of `x`.
  obtain ⟨z, hzmem, hzane⟩ : ∃ z ∈ D.neighborFinset x, z ≠ a := by
    by_contra hcon
    push_neg at hcon
    have hsing : D.neighborFinset x = {a} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨hamem, fun b hb => hcon b hb⟩
    rw [hsing] at hx2
    simp at hx2
  have hzx : D.Adj x z := by simpa using hzmem
  -- Step 3: the degree-one neighbour `w` of `z` differs from `a` and from `x`.
  obtain ⟨w, hzw, hw1⟩ := hother z hzane
  have hwnea : w ≠ a := by
    intro hwa
    subst hwa
    rw [uniq_nb ha1 hax hzw.symm] at hzx
    exact (D.ne_of_adj hzx) rfl
  have hxw : x ≠ w := by
    intro hwx
    exact hx1 (hwx ▸ hw1)
  -- Step 4: `w` is a leaf, so its unique neighbour `z` must have degree one,
  -- but `z` is adjacent to the two distinct vertices `x` and `w`.
  obtain ⟨q, hwq, hq1⟩ := hother w hwnea
  have hqz : q = z := uniq_nb hw1 hzw.symm hwq
  have hz1 : D.degree z = 1 := by rw [← hqz]; exact hq1
  have hxmem : x ∈ D.neighborFinset z := by simpa using hzx.symm
  have hwmem : w ∈ D.neighborFinset z := by simpa using hzw
  have h2 : 2 ≤ (D.neighborFinset z).card := by
    by_contra hcon
    have hcon1 : (D.neighborFinset z).card ≤ 1 := by omega
    exact hxw ((Finset.card_le_one.mp hcon1) x hxmem w hwmem)
  have h2' : 2 ≤ D.degree z := by simpa using h2
  omega

/-!
## Remaining theorem-specific structure target

The full local formalization still needed for the Case-A branch is the
Gliviak--Fajtlowicz / Swart vertex-radius-decreasing structure theorem,
reproved semantically in `docs/full-proof.md` (Section 3).

We intentionally DO NOT declare it with an unproved body.

Target mathematical interface:

```
theorem vrd_with_cut_vertex_structure ...
```

It should produce enough data to construct an induced tree of order at least
`2 * radiusNat G`; a full graph-isomorphism-to-corona statement is stronger
than necessary and is therefore not required.
-/

end Graffiti84
