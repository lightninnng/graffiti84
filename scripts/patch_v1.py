# -*- coding: utf-8 -*-
"""V1: 3.2 UEP neighbour lemma appended to EndBlocks.lean."""

ADD = r'''
/-! ### 3.2: the UEP neighbour lemma -/

private lemma one_le_dist_of_ne {G : SimpleGraph α} (hconn : G.Connected)
    {a b : α} (hne : a ≠ b) : 1 ≤ G.dist a b := by
  obtain ⟨t, ht⟩ := hconn.exists_walk_length_eq_dist a b
  cases t with
  | nil => exact absurd rfl hne
  | cons h t' => rw [SimpleGraph.Walk.length_cons] at ht; omega

private lemma dist_le_one_of_adj {G : SimpleGraph α} {a b : α} (h : G.Adj a b) :
    G.dist a b ≤ 1 := by
  have hle := SimpleGraph.dist_le (SimpleGraph.Adj.toWalk h)
  simpa [SimpleGraph.Adj.toWalk] using hle

/-- **3.2 (UEP neighbour lemma).** If `v` is the unique eccentric point of
`c` and `deg v ≥ 2`, then every neighbour `x` of `v` satisfies
`d(c, x) = ecc(c) - 1` and is not a cut vertex. -/
theorem deleteConnected_of_isUniqueEccentricPoint_neighbor {G : SimpleGraph α}
    (hconn : G.Connected) {c v : α} (huep : IsUniqueEccentricPoint G c v)
    (hdeg : 2 ≤ G.degree v) {x : α} (hxv : G.Adj x v) :
    G.dist c x + 1 = (G.eccent c).toNat ∧ DeleteConnected G x := by
  have hd1 := dist_le_one_of_adj (G := G)
  set r := (G.eccent c).toNat with hrdef
  have hxvne : x ≠ v := G.ne_of_adj hxv
  -- (a) the distance statement
  have htr : G.dist c v ≤ G.dist c x + 1 := by
    have h1 := hconn.dist_triangle (u := c) (v := x) (w := v)
    have hx1 : G.dist x v ≤ 1 := hd1 _ _ hxv
    omega
  have hdist := huep.2 x hxvne
  have hda : G.dist c x + 1 = r := by omega
  refine ⟨hda, ?_⟩
  -- (b) x is not a cut vertex
  -- a second neighbour y of v with y ≠ x
  have hxnb : x ∈ G.neighborFinset v := SimpleGraph.mem_neighborFinset.mpr
    (G.symm hxv)
  obtain ⟨y, hyv, hyx⟩ : ∃ y, G.Adj y v ∧ y ≠ x := by
    by_contra hcon
    push_neg at hcon
    have hsub : G.neighborFinset v ⊆ Finset.singleton x := by
      intro z hz
      have hz2 := hcon z (SimpleGraph.mem_neighborFinset.mp hz)
      rw [hz2]
      exact Finset.mem_singleton.mpr rfl
    have h1 : G.degree v ≤ 1 := by
      have hcard : (G.neighborFinset v).card ≤ ({x} : Finset α).card :=
        Finset.card_le_card hsub
      rw [SimpleGraph.degree]
      omega
    omega
  have hyne : y ≠ v := G.ne_of_adj hyv
  -- x ≠ c: otherwise the second neighbour y would sit strictly between
  -- eccentricity bounds
  have hxc : x ≠ c := by
    intro e
    have hv1 : G.dist c v ≤ 1 := by
      rw [← e]
      exact hd1 _ _ hxv
    have hdy1 : 1 ≤ G.dist c y := one_le_dist_of_ne hconn
      (fun hcy => hyx (by rw [hcy, e]))
    have hlt2 := huep.2 y hyne
    omega
  -- every vertex other than x reaches c avoiding x
  have reach : ∀ z : α, z ≠ x → ∃ w : G.Walk z c, x ∉ w.support := by
    intro z hz
    by_cases hzv : z = v
    · -- z = v: hop to the other neighbour y, then the geodesic y -> c
      subst hzv
      obtain ⟨t, ht⟩ := hconn.exists_walk_length_eq_dist y c
      have hxt : x ∉ t.support := by
        intro hxc2
        have hle := edist_add_edist_le_of_mem_support (p := t) hxc2
        have hc1 : ((G.dist y x : ℕ) : ℕ∞) = G.edist y x :=
          (hconn.preconnected y x).coe_dist_eq_edist
        have hc2 : ((G.dist x c : ℕ) : ℕ∞) = G.edist x c :=
          (hconn.preconnected x c).coe_dist_eq_edist
        have hc3 : ((G.dist y c : ℕ) : ℕ∞) = G.edist y c :=
          (hconn.preconnected y c).coe_dist_eq_edist
        rw [hc3, hc1, hc2] at hle
        have hle2 : G.dist y x + G.dist x c ≤ G.dist y c :=
          ENat.coe_le_coe.mp hle
        have hdyx : 1 ≤ G.dist y x := one_le_dist_of_ne hconn hyx
        have hdxc : 1 ≤ G.dist x c := one_le_dist_of_ne hconn hxc
        have hsym : G.dist y c = G.dist c y := SimpleGraph.dist_comm y c
        have hlt2 := huep.2 y hyne
        omega
      refine ⟨(SimpleGraph.Adj.toWalk (G.symm hvy)).append t, ?_⟩
      intro hc
      rw [SimpleGraph.Walk.support_append, SimpleGraph.Adj.toWalk] at hc
      simp only [List.mem_append, List.mem_cons, List.mem_singleton] at hc
      rcases hc with hc2 | hc2
      · rcases List.mem_cons.mp hc2 with e | e
        · exact hxvne e
        · exact hyx e.symm
      · exact hxt (List.mem_of_mem_tail hc2)
    · -- z ≠ v: the geodesic z -> c avoids x
      obtain ⟨t, ht⟩ := hconn.exists_walk_length_eq_dist z c
      have hxt : x ∉ t.support := by
        intro hxc2
        have hle := edist_add_edist_le_of_mem_support (p := t) hxc2
        have hc1 : ((G.dist z x : ℕ) : ℕ∞) = G.edist z x :=
          (hconn.preconnected z x).coe_dist_eq_edist
        have hc2 : ((G.dist x c : ℕ) : ℕ∞) = G.edist x c :=
          (hconn.preconnected x c).coe_dist_eq_edist
        have hc3 : ((G.dist z c : ℕ) : ℕ∞) = G.edist z c :=
          (hconn.preconnected z c).coe_dist_eq_edist
        rw [hc3, hc1, hc2] at hle
        have hle2 : G.dist z x + G.dist x c ≤ G.dist z c :=
          ENat.coe_le_coe.mp hle
        have hdzx : 1 ≤ G.dist z x := one_le_dist_of_ne hconn
          (fun e => hz e)
        have hdxc : 1 ≤ G.dist x c := one_le_dist_of_ne hconn hxc
        have hlt2 := huep.2 z (fun e => hzv e)
        omega
      exact ⟨t, hxt⟩
  intro a b ha hb
  obtain ⟨w₁, h₁⟩ := reach a ha
  obtain ⟨w₂, h₂⟩ := reach b hb
  refine ⟨w₁.append w₂.reverse, ?_⟩
  intro hu
  rw [SimpleGraph.Walk.support_append, List.mem_append] at hu
  rcases hu with h | h
  · exact h₁ h
  · rw [SimpleGraph.Walk.support_reverse] at h
    exact h₂ (List.mem_reverse.mp (List.mem_of_mem_tail h))

'''

p = 'Graffiti84/EndBlocks.lean'
s = open(p, encoding='utf-8').read()
marker = 'end Graffiti84'
assert marker in s and s.count(marker) == 1
s = s.replace(marker, ADD + marker)
open(p, 'w', encoding='utf-8').write(s)
print('3.2 appended')
