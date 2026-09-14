# -*- coding: utf-8 -*-
"""Replace the four chord-exclusion branches with fully calc-based proofs."""

NEW_BRANCHES = r'''  haveI : Nonempty α := hconn.nonempty
  have hmle : q.length + 1 ≤ G.radius.toNat := by rw [← hq]; exact hdvw
  have hrle : G.radius.toNat ≤ p.length := (hp.trans hdva).symm.le
  refine ⟨v₀, v₂, w, p, q, hp.trans hdva, ?_, ?_, hv₂,
    (hp.trans hdva).le.trans hdv₂w, ?_, ?_, ?_, ?_⟩
  · exact by rw [hq, hp, hdva]; exact hdvw
  · exact le_trans hr2 hrle
  · -- (7a): no q_i - v_j chord for j >= 2
    intro i j him hjr h2j hadj
    have hchain : G.radius.toNat ≤ (j - 2) + 1 + (q.length - i) := by
      calc G.radius.toNat ≤ G.dist (p.getVert 2) w := hdv₂w'
        _ ≤ G.dist (p.getVert 2) (p.getVert j) + G.dist (p.getVert j) w :=
            hconn.dist_triangle (u := p.getVert 2) (v := p.getVert j)
              (w := w)
        _ = (j - 2) + G.dist (p.getVert j) w := by
            rw [dist_getVert_pair_le hp 2 j (by omega) hjr]
        _ ≤ (j - 2) + (G.dist (p.getVert j) (q.getVert i)
              + G.dist (q.getVert i) w) := by
            exact add_le_add le_rfl
              (hconn.dist_triangle (u := p.getVert j) (v := q.getVert i)
                (w := w))
        _ ≤ (j - 2) + (1 + (q.length - i)) := by
            refine add_le_add le_rfl ?_
            exact add_le_add (hed1 (p.getVert j) (q.getVert i) hadj.symm)
              (dist_getVert_end_of_length_eq_dist hq i him).le
    have hji : j ≤ i + 1 := by
      calc j = G.dist v₀ (p.getVert j) :=
            (dist_getVert_of_length_eq_dist hp j hjr).symm
        _ ≤ G.dist v₀ (q.getVert i) + G.dist (q.getVert i) (p.getVert j) :=
            hconn.dist_triangle (u := v₀) (v := q.getVert i)
              (w := p.getVert j)
        _ = i + G.dist (q.getVert i) (p.getVert j) := by
            rw [dist_getVert_of_length_eq_dist hq i him]
        _ ≤ i + 1 :=
            Nat.add_le_add_left
              (hed1 (q.getVert i) (p.getVert j) hadj) i
    omega
  · -- (7b): no v1 - p_i chord for i >= 2
    intro i h2i him hadj
    have hchain : G.radius.toNat ≤ 1 + 1 + (q.length - i) := by
      calc G.radius.toNat ≤ G.dist (p.getVert 2) w := hdv₂w'
        _ ≤ G.dist (p.getVert 2) (p.getVert 1) + G.dist (p.getVert 1) w :=
            hconn.dist_triangle (u := p.getVert 2) (v := p.getVert 1)
              (w := w)
        _ = 1 + G.dist (p.getVert 1) w := by rw [h12]
        _ ≤ 1 + (G.dist (p.getVert 1) (q.getVert i)
              + G.dist (q.getVert i) w) := by
            exact add_le_add le_rfl
              (hconn.dist_triangle (u := p.getVert 1) (v := q.getVert i)
                (w := w))
        _ ≤ 1 + (1 + (q.length - i)) := by
            refine add_le_add le_rfl ?_
            exact add_le_add (hed1 (p.getVert 1) (q.getVert i) hadj)
              (dist_getVert_end_of_length_eq_dist hq i him).le
    omega
  · -- (7c): the chord v1 - p1 forces m = r - 1
    intro hadj
    have hchain : G.radius.toNat ≤ 1 + 1 + (q.length - 1) := by
      calc G.radius.toNat ≤ G.dist (p.getVert 2) w := hdv₂w'
        _ ≤ G.dist (p.getVert 2) (p.getVert 1) + G.dist (p.getVert 1) w :=
            hconn.dist_triangle (u := p.getVert 2) (v := p.getVert 1)
              (w := w)
        _ = 1 + G.dist (p.getVert 1) w := by rw [h12]
        _ ≤ 1 + (G.dist (p.getVert 1) (q.getVert 1)
              + G.dist (q.getVert 1) w) := by
            exact add_le_add le_rfl
              (hconn.dist_triangle (u := p.getVert 1) (v := q.getVert 1)
                (w := w))
        _ ≤ 1 + (1 + (q.length - 1)) := by
            refine add_le_add le_rfl ?_
            exact add_le_add (hed1 (p.getVert 1) (q.getVert 1) hadj)
              (dist_getVert_end_of_length_eq_dist hq 1 (by omega)).le
    omega
  · -- supports overlap only at v0
    intro i j h1i hir h1j hjm heq
    have hip : G.dist v₀ (p.getVert i) = i :=
      dist_getVert_of_length_eq_dist hp i hir
    have hqj : G.dist v₀ (q.getVert j) = j :=
      dist_getVert_of_length_eq_dist hq j hjm
    rw [heq] at hip
    have hij : i = j := by omega
    subst hij
    rcases Nat.eq_or_lt_of_le h1i with h1 | h2i
    · -- i = 1
      subst h1
      have hchain : G.radius.toNat ≤ 1 + (q.length - 1) := by
        calc G.radius.toNat ≤ G.dist (p.getVert 2) w := hdv₂w'
          _ ≤ G.dist (p.getVert 2) (p.getVert 1) + G.dist (p.getVert 1) w :=
              hconn.dist_triangle (u := p.getVert 2) (v := p.getVert 1)
                (w := w)
          _ = 1 + G.dist (p.getVert 1) w := by rw [h12]
          _ = 1 + G.dist (q.getVert 1) w := by rw [heq]
          _ = 1 + (q.length - 1) :=
              (dist_getVert_end_of_length_eq_dist hq 1 (by omega))
      omega
    · -- i >= 2
      have hchain : G.radius.toNat ≤ (i - 2) + (q.length - i) := by
        calc G.radius.toNat ≤ G.dist (p.getVert 2) w := hdv₂w'
          _ ≤ G.dist (p.getVert 2) (p.getVert i) + G.dist (p.getVert i) w :=
              hconn.dist_triangle (u := p.getVert 2) (v := p.getVert i)
                (w := w)
          _ = (i - 2) + G.dist (p.getVert i) w := by
              rw [dist_getVert_pair_le hp 2 i (by omega) hir]
          _ = (i - 2) + G.dist (q.getVert i) w := by rw [heq]
          _ = (i - 2) + (q.length - i) :=
              (dist_getVert_end_of_length_eq_dist hq i hjm)
      omega
'''

import io
import re

p = 'Graffiti84/RootedChung.lean'
s = io.open(p, encoding='utf-8').read()
start = s.index('  refine ⟨v₀, v₂, w, p, q, hp.trans hdva, ?_, ?_, hv₂,')
end = s.index('end Graffiti84')
assert start < end
assert not re.search(r'\b(sorry|admit)\b', NEW_BRANCHES)
s = s[:start] + NEW_BRANCHES + '\n' + s[end:]
io.open(p, 'w', encoding='utf-8').write(s)
print('branches replaced (C1v4)')
