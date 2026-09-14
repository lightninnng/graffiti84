# -*- coding: utf-8 -*-
"""Batch C1: pair-distance lemma + chung_chords (all chord exclusions)."""

ADD = r'''
/-- On a geodesic, the distance between two positions is their separation:
for `i <= j <= length`, `d(getVert i, getVert j) = j - i`. -/
theorem dist_getVert_pair_le {G : SimpleGraph α}
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hi : i ≤ p.length := le_trans hij hj
  have htakei : (p.take i).length = i := by
    rw [SimpleGraph.Walk.take_length]
    exact Nat.min_eq_left hi
  have htakej : (p.take j).length = j := by
    rw [SimpleGraph.Walk.take_length]
    exact Nat.min_eq_left hj
  have hdropj : (p.drop j).length = p.length - j :=
    SimpleGraph.Walk.drop_length p j
  have hseg : ((p.take j).drop i).length = j - i := by
    rw [SimpleGraph.Walk.drop_length, htakej]
    omega
  have hle : G.dist (p.getVert i) (p.getVert j) ≤ j - i := by
    have h := SimpleGraph.dist_le ((p.take j).drop i)
    rw [hseg] at h
    exact h
  rcases Nat.eq_or_lt_of_le hle with h | h
  · exact h
  · exfalso
    obtain ⟨s, hs⟩ := ((p.take i).reachable).exists_walk_length_eq_dist
    have hsplit : (((p.take i).append s).append (p.drop j)).length
        = i + (p.length - j) + s.length := by
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
        htakei]
      omega
    have hshort : (((p.take i).append s).append (p.drop j)).length
        < p.length := by
      rw [hsplit, hs]
      omega
    have hd := SimpleGraph.dist_le (((p.take i).append s).append (p.drop j))
    rw [← hp] at hd
    omega

/-- **Chung chords.** Given the Chung context, all cross-chords between the
two geodesics are excluded, the exceptional chord `v1 - p1` forces
`m = r - 1`, and the two supports overlap only at `v0`. -/
theorem chung_chords {G : SimpleGraph α} (hconn : G.Connected) {a : α}
    (hr2 : 2 ≤ G.radius.toNat)
    (hdrop : radOn G (Finset.univ.erase a) + 1 ≤ G.radius) :
    ∃ (v₀ v₂ w : α) (p : G.Walk v₀ a) (q : G.Walk v₀ w) (r m : ℕ),
      r = G.radius.toNat ∧ m + 1 ≤ r ∧ 2 ≤ r ∧ p.length = r ∧ q.length = m ∧
      p.getVert 2 = v₂ ∧ r ≤ G.dist v₂ w ∧
      (∀ i j, i ≤ m → j ≤ r → 2 ≤ j → ¬ G.Adj (q.getVert i) (p.getVert j)) ∧
      (∀ i, 2 ≤ i → i ≤ m → ¬ G.Adj (p.getVert 1) (q.getVert i)) ∧
      (G.Adj (p.getVert 1) (q.getVert 1) → m + 1 = r) ∧
      (∀ i j, 1 ≤ i → i ≤ r → 1 ≤ j → j ≤ m →
        p.getVert i = q.getVert j → False) := by
  obtain ⟨v₀, v₂, w, p, q, hp, hdva, hv₂, hdv₂a, hq, hdvw, hdv₂w⟩ :=
    chung_context hconn hr2 hdrop
  have hed1 : ∀ x y : α, G.Adj x y → G.dist x y ≤ 1 := fun x y hh => by
    have h' := SimpleGraph.dist_le (SimpleGraph.Adj.toWalk hh)
    simpa [SimpleGraph.Adj.toWalk] using h'
  have h12 : G.dist (p.getVert 2) (p.getVert 1) = 1 := by
    rw [SimpleGraph.dist_comm]
    exact dist_getVert_pair_le hp 1 2 (by omega) (by omega)
  refine ⟨v₀, v₂, w, p, q, G.radius.toNat, q.length, hdva, hdvw, hr2,
    hp.trans hdva, hq, hv₂, hdv₂w, ?_, ?_, ?_, ?_⟩
  · -- (7a): no q_i - v_j chord for j >= 2
    intro i j him hjr h2j hadj
    have hedge := hed1 (q.getVert i) (p.getVert j) hadj
    have hip : G.dist v₀ (q.getVert i) = i :=
      dist_getVert_of_length_eq_dist hq i him
    have hpj : G.dist v₀ (p.getVert j) = j :=
      dist_getVert_of_length_eq_dist hp j hjr
    have hji : j ≤ i + 1 := by
      have ht := hconn.dist_triangle v₀ (q.getVert i) (p.getVert j)
      rw [hip, hpj] at ht
      omega
    have hpair := dist_getVert_pair_le hp 2 j (by omega) hjr
    have hqw : G.dist (q.getVert i) w = q.length - i :=
      dist_getVert_end_of_length_eq_dist hq i him
    have hd : G.dist v₂ w ≤ (j - 2) + 1 + (q.length - i) := by
      calc G.dist v₂ w ≤ G.dist (p.getVert 2) (p.getVert j)
            + G.dist (p.getVert j) w := by
            rw [hv₂]
            exact hconn.dist_triangle v₂ (p.getVert j) w
        _ ≤ (j - 2) + (1 + (q.length - i)) := by
            refine add_le_add hpair ?_
            exact le_trans (add_le_add hedge le_rfl)
              (by rw [← hqw]; omega)
    omega
  · -- (7b): no v1 - p_i chord for i >= 2
    intro i h2i him hadj
    have hedge := hed1 (p.getVert 1) (q.getVert i) hadj
    have hqw : G.dist (q.getVert i) w = q.length - i :=
      dist_getVert_end_of_length_eq_dist hq i him
    have hd : G.dist v₂ w ≤ 1 + 1 + (q.length - i) := by
      calc G.dist v₂ w ≤ G.dist (p.getVert 2) (p.getVert 1)
            + G.dist (p.getVert 1) w := by
            rw [hv₂]
            exact hconn.dist_triangle v₂ (p.getVert 1) w
        _ ≤ 1 + (1 + (q.length - i)) := by
            refine add_le_add h12 ?_
            exact le_trans (add_le_add hedge le_rfl)
              (by rw [← hqw]; omega)
    omega
  · -- (7c): the chord v1 - p1 forces m = r - 1
    intro hadj
    have hedge := hed1 (p.getVert 1) (q.getVert 1) hadj
    have hq1 : G.dist (q.getVert 1) w = q.length - 1 :=
      dist_getVert_end_of_length_eq_dist hq 1 (by omega)
    have hd : G.dist v₂ w ≤ 1 + 1 + (q.length - 1) := by
      calc G.dist v₂ w ≤ G.dist (p.getVert 2) (p.getVert 1)
            + G.dist (p.getVert 1) w := by
            rw [hv₂]
            exact hconn.dist_triangle v₂ (p.getVert 1) w
        _ ≤ 1 + (1 + (q.length - 1)) := by
            refine add_le_add h12 ?_
            exact add_le_add hedge hq1
    omega
  · -- supports overlap only at v0
    intro i j h1i hir h1j hjm heq
    have hip : G.dist v₀ (p.getVert i) = i :=
      dist_getVert_of_length_eq_dist hp i hir
    have hqj : G.dist v₀ (q.getVert j) = j :=
      dist_getVert_of_length_eq_dist hq j hjm
    rw [heq] at hip
    have hij : i = j := by omega
    rcases Nat.eq_or_lt_of_le h1i with h1 | h2i
    · -- i = j = 1
      have hq1 : G.dist (q.getVert 1) w = q.length - 1 :=
        dist_getVert_end_of_length_eq_dist hq 1 (by omega)
      have hd : G.dist v₂ w ≤ 1 + (q.length - 1) := by
        calc G.dist v₂ w ≤ G.dist (p.getVert 2) (p.getVert 1)
              + G.dist (p.getVert 1) w := by
              rw [hv₂]
              exact hconn.dist_triangle v₂ (p.getVert 1) w
          _ ≤ 1 + (q.length - 1) := by
              refine add_le_add h12 ?_
              rw [heq]
              exact hq1
      omega
    · -- i = j >= 2
      have hpair := dist_getVert_pair_le hp 2 i (by omega) hir
      have hqw : G.dist (q.getVert i) w = q.length - i :=
        dist_getVert_end_of_length_eq_dist hq i hjm
      have hd : G.dist v₂ w ≤ (i - 2) + (q.length - i) := by
        calc G.dist v₂ w ≤ G.dist (p.getVert 2) (p.getVert i)
              + G.dist (p.getVert i) w := by
              rw [hv₂]
              exact hconn.dist_triangle v₂ (p.getVert i) w
          _ ≤ (i - 2) + (q.length - i) := by
              refine add_le_add hpair ?_
              rw [heq]
              exact hqw
      omega
'''

import io
import re

p = 'Graffiti84/RootedChung.lean'
s = io.open(p, encoding='utf-8').read()
marker = 'end Graffiti84'
assert marker in s
assert not re.search(r'\b(sorry|admit)\b', ADD)
s = s.replace(marker, ADD + '\n' + marker)
io.open(p, 'w', encoding='utf-8').write(s)
print('batch C1 appended')
