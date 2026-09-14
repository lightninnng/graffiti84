# -*- coding: utf-8 -*-
"""C2 part 1: general chord-index induced-tree lemma + the m=0 case."""

ADD = r'''
/-- A walk whose support has no chords (adjacent support vertices sit at
neighbouring indices) induces a tree.  Injectivity of the index potential
needs only membership (`List.idxOf_inj`), not `Nodup`. -/
theorem isInducedTree_of_walk_chords {G : SimpleGraph α} {x z : α}
    (Q : G.Walk x z)
    (hchord : ∀ u v, u ∈ Q.support → v ∈ Q.support → G.Adj u v →
      (Q.support.idxOf u + 1 = Q.support.idxOf v ∨
        Q.support.idxOf v + 1 = Q.support.idxOf u)) :
    IsInducedTree G Q.support.toFinset := by
  constructor
  · -- connected within the support: subwalks of Q
    intro a ha b hb
    have ha' : a ∈ Q.support := List.mem_toFinset.mp ha
    have hb' : b ∈ Q.support := List.mem_toFinset.mp hb
    refine ⟨(Q.dropUntil a ha').append ((Q.dropUntil b hb').reverse), ?_⟩
    intro t ht
    rw [SimpleGraph.Walk.mem_support_append_iff] at ht
    rw [List.mem_toFinset]
    rcases ht with h | h
    · exact (SimpleGraph.Walk.support_dropUntil_suffix_support Q ha').subset h
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h
      exact (SimpleGraph.Walk.support_dropUntil_suffix_support Q hb').subset h
  · -- acyclic via the index potential
    refine acyclicWithin_of_phi (fun z => (Q.support.idxOf z : ℤ)) ?_ ?_
    · intro u hu v hv heq
      have hu' : u ∈ Q.support := List.mem_toFinset.mp hu
      have hv' : v ∈ Q.support := List.mem_toFinset.mp hv
      have hn : Q.support.idxOf u = Q.support.idxOf v := by
        exact_mod_cast heq
      exact List.idxOf_inj hu' |>.mp hn
    · intro u hu v hv hadj
      have hu' : u ∈ Q.support := List.mem_toFinset.mp hu
      have hv' : v ∈ Q.support := List.mem_toFinset.mp hv
      rcases hchord u v hu' hv' hadj with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num

/-- **Rooted Chung lemma (m = 0 case).** When the second geodesic is
trivial, `r = 2` and the first geodesic alone is an induced tree of order
`r + 1 = 2r - 1` containing `a`. -/
theorem rooted_chung_m_zero {G : SimpleGraph α} (hconn : G.Connected) {a : α}
    (hr2 : 2 ≤ G.radius.toNat)
    (hdrop : radOn G (Finset.univ.erase a) + 1 ≤ G.radius) :
    ∃ S : Finset α, IsInducedTree G S ∧ a ∈ S ∧
      2 * G.radius.toNat - 1 ≤ S.card := by
  obtain ⟨v₀, v₂, w, p, q, hp, hmle, hplen, hv₂, hdv₂w, h7a, h7b, h7c,
    hover⟩ := chung_chords hconn hr2 hdrop
  -- q.length = 0 forces r <= 2 via the triangle v2 - v0 - w
  have hq0 : q.length = 0 := by omega
  have hweq : w = v₀ := by
    have : q.length = 0 → w = v₀ := by
      intro h
      have : q = SimpleGraph.Walk.nil := by
        cases q with
        | nil => rfl
        | cons h' _ => omega
      rw [this]
      rfl
    exact this hq0
  -- triangle: r <= dist(p2, w) <= dist(p2, v0) + dist(v0, w) = 2 + 0
  have hd2 : G.dist v₀ (p.getVert 2) = 2 :=
    dist_getVert_of_length_eq_dist hp 2 (by omega)
  have ht := hconn.dist_triangle (u := p.getVert 2) (v := v₀) (w := w)
  rw [hweq, ← SimpleGraph.dist_comm (G := G) (u := p.getVert 2) (v := v₀),
    hd2] at ht
  -- ht : dist(p2, v0) <= 2 + dist(v0, v0)?? -- rewrite direction off; use omega on hdv2w'
  sorry
'''

import io
import re

p = 'Graffiti84/RootedChung.lean'
s = io.open(p, encoding='utf-8').read()
marker = 'end Graffiti84'
assert marker in s
s = s.replace(marker, ADD + '\n' + marker)
io.open(p, 'w', encoding='utf-8').write(s)
print('C2 part 1 draft written (has sorry in m_zero tail)')
