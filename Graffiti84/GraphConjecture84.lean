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

open Classical

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

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


/-- The minimum degree of `G`. -/
noncomputable def minDegree (G : SimpleGraph α) [Nonempty α] : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty fun v => G.degree v

lemma degree_ge_minDegree {G : SimpleGraph α} [Nonempty α] {v : α} :
    minDegree G ≤ G.degree v := by
  simp only [minDegree]
  exact Finset.inf'_le (fun w => G.degree w) (Finset.mem_univ v)

/-- **Conjecture 84, minimum-degree-at-least-two branch (graph level).**
A connected graph with `δ ≥ 2` satisfies `2r ≤ t·δ`. -/
theorem two_radius_le_treeNumber_mul_minDegree {G : SimpleGraph α} [Nonempty α]
    (hconn : G.Connected) (hδ : 2 ≤ minDegree G) :
    2 * G.radius.toNat ≤ treeNumber G * minDegree G := by
  have h1 : G.radius.toNat + 1 ≤ treeNumber G :=
    radius_add_one_le_treeNumber hconn
  have hdeg : ∀ v : α, 2 ≤ G.degree v := fun v =>
    le_trans hδ (degree_ge_minDegree)
  haveI : Nontrivial α := by
    by_contra hnt
    obtain ⟨v⟩ := ‹Nonempty α›
    have hv2 : 2 ≤ G.degree v := hdeg v
    have hpos : 0 < G.degree v := by omega
    obtain ⟨x, hx⟩ :=
      (SimpleGraph.degree_pos_iff_exists_adj (G := G) v).mp hpos
    exact hnt ⟨v, x, G.ne_of_adj hx⟩
  have hrad1 : (1 : ℕ∞) ≤ G.radius := by
    refine (le_iInf_iff).mpr fun u => ?_
    have hu : (0 : ℕ∞) < G.eccent u :=
      pos_iff_ne_zero.mpr (G.eccent_ne_zero u)
    exact Order.one_le_iff_pos.mpr hu
  have hne0 : G.radius ≠ 0 := by
    intro h
    rw [h] at hrad1
    exact absurd hrad1 (by simp)
  have hrtop : G.radius ≠ ⊤ := by
    obtain ⟨c, y, hcy⟩ := G.exists_edist_eq_radius_of_finite
    rw [← hcy]
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c y)
  have hpos : 0 < G.radius.toNat := ENat.toNat_pos hne0 hrtop
  have hr : 1 ≤ G.radius.toNat := by omega
  exact final_arithmetic G.radius.toNat (minDegree G) (treeNumber G) hr
    (by omega) (fun h0 => absurd h0 (by omega)) (fun _ => h1)

end Graffiti84
