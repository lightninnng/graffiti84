# -*- coding: utf-8 -*-
"""C2 main-1 v2: rooted_chung_flat, corrected after run #110 log."""

ADD = r'''
/-- **Rooted Chung, flat case.** Given the Chung data with no exceptional
chord `v₁ - q₁`, the glued walk `p.reverse ++ q` has a chord-free support
carrying an induced tree of order `r + m + 1 ≥ 2r - 1` that contains `a`. -/
theorem rooted_chung_flat {G : SimpleGraph α} (hconn : G.Connected) {a : α}
    {v₀ v₂ w : α} {p : G.Walk v₀ a} {q : G.Walk v₀ w}
    (hp : p.length = G.radius.toNat) (hdva : G.dist v₀ a = G.radius.toNat)
    (hq : q.length = G.dist v₀ w) (h2 : 2 ≤ p.length)
    (hv₂ : p.getVert 2 = v₂) (hpw : p.length ≤ G.dist v₂ w)
    (h7a : ∀ i j, i ≤ q.length → j ≤ p.length → 2 ≤ j →
      ¬ G.Adj (q.getVert i) (p.getVert j))
    (h7b : ∀ i, 2 ≤ i → i ≤ q.length → ¬ G.Adj (p.getVert 1) (q.getVert i))
    (hover : ∀ i j, 1 ≤ i → i ≤ p.length → 1 ≤ j → j ≤ q.length →
      p.getVert i = q.getVert j → False)
    (hnc : ¬ G.Adj (p.getVert 1) (q.getVert 1)) :
    ∃ S : Finset α, IsInducedTree G S ∧ a ∈ S ∧
      2 * G.radius.toNat - 1 ≤ S.card := by
  haveI : Nonempty α := hconn.nonempty
  haveI : Inhabited α := ⟨v₀⟩
  set r := G.radius.toNat with hrdef
  have hpgeo : p.length = G.dist v₀ a := hp.trans hdva.symm
  have hpp : p.IsPath := isPath_of_length_eq_dist hconn hpgeo
  have hqq : q.IsPath := isPath_of_length_eq_dist hconn hq
  have hpN : p.support.Nodup := hpp.support_nodup
  have hqN : q.support.Nodup := hqq.support_nodup
  have hpsl : p.support.length = p.length + 1 :=
    SimpleGraph.Walk.length_support p
  have hqsl : q.support.length = q.length + 1 :=
    SimpleGraph.Walk.length_support q
  have hplen : p.support.length = r + 1 := by rw [hpsl, hp]
  -- the glued walk and its support list
  set Q := p.reverse.append q with hQdef
  have hsupL : Q.support = p.support.reverse ++ q.support.tail := by
    rw [hQdef, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse]
  -- overlap exclusion (works in both directions)
  have hcore : ∀ x, x ∈ p.support → x ∈ q.support.tail → False := by
    intro x hx hxq
    have hxg : p.getVert (p.support.idxOf x) = x :=
      SimpleGraph.Walk.getVert_support_idxOf p hx
    have hxgq : q.getVert (q.support.idxOf x) = x :=
      SimpleGraph.Walk.getVert_support_idxOf q (List.mem_of_mem_tail hxq)
    have hile : p.support.idxOf x ≤ p.length := by
      have := List.idxOf_lt_length_of_mem hx
      omega
    have hj1 : 1 ≤ q.support.idxOf x := by
      have hts := idxOf_tail_succ q.support hqN x hxq
      omega
    have hjle : q.support.idxOf x ≤ q.length := by
      have := List.idxOf_lt_length_of_mem (List.mem_of_mem_tail hxq)
      omega
    rcases Nat.eq_zero_or_pos (p.support.idxOf x) with h0 | h2i
    · -- x = v0 sits at q-position ≥ 1: contradicts geodesic injectivity
      rw [h0, SimpleGraph.Walk.getVert_zero] at hxg
      rw [← hxg] at hxgq
      have hne := getVert_ne_of_length_eq_dist hq hj1 (Nat.zero_le q.length)
        (by omega)
      rw [SimpleGraph.Walk.getVert_zero] at hne
      exact hne hxgq
    · exact hover (p.support.idxOf x) (q.support.idxOf x) h2i hile hj1 hjle
        (hxg.trans hxgq.symm)
  have hdisj : List.Disjoint p.support.reverse q.support.tail := by
    intro x hx1 hx2
    exact hcore x (List.mem_reverse.mp hx1) hx2
  have hLnd : Q.support.Nodup := by
    rw [hsupL]
    exact (List.nodup_reverse.mpr hpN).append hqN.tail hdisj
  -- index positions in the glued list
  have hpidx : ∀ x ∈ p.support, Q.support.idxOf x = r - p.support.idxOf x := by
    intro x hx
    rw [hsupL, List.idxOf_append_of_mem (by rw [List.mem_reverse]; exact hx)]
    have h := idxOf_reverse_mem p.support hpN x hx
    omega
  have hqidx : ∀ x ∈ q.support.tail, Q.support.idxOf x = r + q.support.idxOf x := by
    intro x hx
    have hxr : x ∉ p.support.reverse := fun hc =>
      hcore x (List.mem_reverse.mp hc) hx
    rw [hsupL, List.idxOf_append_of_notMem hxr]
    have h1 := List.idxOf_eq_length hxr
    have h2t := idxOf_tail_succ q.support hqN x hx
    have h3 : p.support.reverse.length = r + 1 := by
      rw [List.length_reverse, hplen]
    omega
  -- the cross case: p-side vertex adjacent to q-side vertex
  have hcross : ∀ u v, u ∈ p.support → v ∈ q.support.tail → G.Adj u v →
      Q.support.idxOf u + 1 = Q.support.idxOf v := by
    intro u v hu hv hadj
    have hgu : p.getVert (p.support.idxOf u) = u :=
      SimpleGraph.Walk.getVert_support_idxOf p hu
    have hgv : q.getVert (q.support.idxOf v) = v :=
      SimpleGraph.Walk.getVert_support_idxOf q (List.mem_of_mem_tail hv)
    have hj1 : 1 ≤ q.support.idxOf v := by
      have hts := idxOf_tail_succ q.support hqN v hv
      omega
    have hjle : q.support.idxOf v ≤ q.length := by
      have := List.idxOf_lt_length_of_mem (List.mem_of_mem_tail hv)
      omega
    have hile : p.support.idxOf u ≤ p.length := by
      have := List.idxOf_lt_length_of_mem hu
      omega
    rcases Nat.eq_zero_or_pos (p.support.idxOf u) with h0 | h2i
    · -- u = v0: run the geodesic argument along q
      rw [h0, SimpleGraph.Walk.getVert_zero] at hgu
      have hu0 : u = q.getVert 0 := by
        rw [← hgu, SimpleGraph.Walk.getVert_zero]
      have huq : u ∈ q.support := by
        rw [hu0]
        exact SimpleGraph.Walk.getVert_mem_support q 0
      have hvq : v ∈ q.support := List.mem_of_mem_tail hv
      have hgeo := geodesic_adj_support_succ hconn hq huq hvq hadj
      have hgx : q.getVert (q.support.idxOf u) = q.getVert 0 :=
        (SimpleGraph.Walk.getVert_support_idxOf q huq).trans hu0
      have hu0idx : q.support.idxOf u = 0 := by
        rcases Nat.eq_zero_or_pos (q.support.idxOf u) with k0 | k1
        · exact k0
        · exact absurd hgx (getVert_ne_of_length_eq_dist hq
            (by have := List.idxOf_lt_length_of_mem huq; omega)
            (Nat.zero_le q.length) (by omega))
      rcases hgeo with h | h
      · rw [hpidx u hu, hqidx v hv]; omega
      · omega
    · -- u at p-position ≥ 1
      rcases Nat.lt_or_ge (p.support.idxOf u) 2 with h1i | h2i
      · -- i = 1: the exceptional chord v1 - q1, excluded by hypothesis
        have hi1 : p.support.idxOf u = 1 := by omega
        rw [hi1] at hgu
        rcases Nat.lt_or_ge (q.support.idxOf v) 2 with hjv1 | hjv2
        · have hjv1' : q.support.idxOf v = 1 := by omega
          rw [hjv1'] at hgv
          exact absurd (show G.Adj (p.getVert 1) (q.getVert 1) from by
            rw [hgu, hgv]; exact hadj) hnc
        · exact absurd (show G.Adj (p.getVert 1)
              (q.getVert (q.support.idxOf v)) from by
            rw [hgu, hgv]; exact hadj) (h7b (q.support.idxOf v) hjv2 hjle)
      · -- i ≥ 2: contradicts 7a
        exact absurd (show G.Adj (q.getVert (q.support.idxOf v))
              (p.getVert (p.support.idxOf u)) from by
            rw [hgv, hgu]; exact hadj.symm)
          (h7a (q.support.idxOf v) (p.support.idxOf u) hjle hile h2i)
  -- chord-freeness of the glued support
  have hchord : ∀ u v, u ∈ Q.support → v ∈ Q.support → G.Adj u v →
      (Q.support.idxOf u + 1 = Q.support.idxOf v ∨
        Q.support.idxOf v + 1 = Q.support.idxOf u) := by
    intro u v hu hv hadj
    rw [hsupL, List.mem_append] at hu hv
    rcases hu with hu1 | hu2 <;> rcases hv with hv1 | hv2
    · -- both in the p-part
      rw [List.mem_reverse] at hu1 hv1
      have hi := hpidx u hu1
      have hj := hpidx v hv1
      have hib : p.support.idxOf u ≤ p.length := by
        have := List.idxOf_lt_length_of_mem hu1; omega
      have hjb : p.support.idxOf v ≤ p.length := by
        have := List.idxOf_lt_length_of_mem hv1; omega
      have hgeo := geodesic_adj_support_succ hconn hpgeo hu1 hv1 hadj
      rcases hgeo with h | h
      · right; omega
      · left; omega
    · -- u in p-part, v in q-part
      rw [List.mem_reverse] at hu1
      exact Or.inl (hcross u v hu1 hv2 hadj)
    · -- u in q-part, v in p-part
      rw [List.mem_reverse] at hv1
      exact Or.inr (hcross v u hv1 hu2 hadj.symm)
    · -- both in the q-part
      have huq : u ∈ q.support := List.mem_of_mem_tail hu2
      have hvq : v ∈ q.support := List.mem_of_mem_tail hv2
      have hgeo := geodesic_adj_support_succ hconn hq huq hvq hadj
      have hui := hqidx u hu2
      have hvi := hqidx v hv2
      rcases hgeo with h | h
      · left; omega
      · right; omega
  refine ⟨Q.support.toFinset, isInducedTree_of_walk_chords Q hchord, ?_, ?_⟩
  · rw [List.mem_toFinset, hsupL, List.mem_append, List.mem_reverse]
    exact Or.inl (SimpleGraph.Walk.end_mem_support p)
  · rw [List.toFinset_card_of_nodup hLnd, SimpleGraph.Walk.length_support,
      hQdef, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse]
    have hv₂₀ : G.dist v₀ v₂ = 2 := by
      rw [← hv₂]
      exact dist_getVert_of_length_eq_dist hpgeo 2 h2
    have ht := hconn.dist_triangle (u := v₂) (v := v₀) (w := w)
    rw [hv₂₀, hq] at ht
    have horder : r ≤ q.length + 2 := by
      calc r = p.length := hp.symm
        _ ≤ G.dist v₂ w := hpw
        _ ≤ q.length + 2 := ht
    omega

'''

p = 'Graffiti84/RootedChung.lean'
s = open(p, encoding='utf-8').read()
marker = 'end Graffiti84'
assert marker in s and s.count(marker) == 1
s = s.replace(marker, ADD + marker)
open(p, 'w', encoding='utf-8').write(s)
print('rooted_chung_flat v2 appended')
