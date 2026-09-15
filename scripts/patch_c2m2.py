# -*- coding: utf-8 -*-
"""C2 main-2/3: rooted_chung_chord (3-segment splice) + rooted_chung dispatch."""

ADD = r'''
/-- **Rooted Chung, chord case.** When the exceptional chord `v₁ - q₁`
exists, 7c forces `m + 1 = r`, and the three-segment walk `a ↝ v₁`, chord,
`q₁ ↝ w` carries an induced tree of order exactly `2r - 1` containing `a`:
the splice removes `v₀`, so the chord joins the neighbouring positions
`r - 1` and `r`. -/
theorem rooted_chung_chord {G : SimpleGraph α} (hconn : G.Connected) {a : α}
    {v₀ v₂ w : α} {p : G.Walk v₀ a} {q : G.Walk v₀ w}
    (hp : p.length = G.radius.toNat) (hdva : G.dist v₀ a = G.radius.toNat)
    (hq : q.length = G.dist v₀ w) (h2 : 2 ≤ p.length)
    (h7a : ∀ i j, i ≤ q.length → j ≤ p.length → 2 ≤ j →
      ¬ G.Adj (q.getVert i) (p.getVert j))
    (h7b : ∀ i, 2 ≤ i → i ≤ q.length → ¬ G.Adj (p.getVert 1) (q.getVert i))
    (hover : ∀ i j, 1 ≤ i → i ≤ p.length → 1 ≤ j → j ≤ q.length →
      p.getVert i = q.getVert j → False)
    (h7c : 1 ≤ q.length → G.Adj (p.getVert 1) (q.getVert 1) →
      q.length + 1 = p.length)
    (h1m : 1 ≤ q.length) (hadj : G.Adj (p.getVert 1) (q.getVert 1)) :
    ∃ S : Finset α, IsInducedTree G S ∧ a ∈ S ∧
      2 * G.radius.toNat - 1 ≤ S.card := by
  haveI : Inhabited α := ⟨a⟩
  set r := G.radius.toNat with hrdef
  have hpgeo : p.length = G.dist v₀ a := hp.trans hdva.symm
  have hm1 : q.length + 1 = p.length := h7c h1m hadj
  have hpnn : ¬ p.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr (by omega)
  have hqnn : ¬ q.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr h1m
  have hpp : p.IsPath := isPath_of_length_eq_dist hconn hpgeo
  have hqq : q.IsPath := isPath_of_length_eq_dist hconn hq
  have hpN : p.support.Nodup := hpp.support_nodup
  have hqN : q.support.Nodup := hqq.support_nodup
  have hpsl : p.support.length = p.length + 1 :=
    SimpleGraph.Walk.length_support p
  have hqsl : q.support.length = q.length + 1 :=
    SimpleGraph.Walk.length_support q
  have hplen : p.support.length = r + 1 := by rw [hpsl, hp]
  have hv₁ : p.snd = p.getVert 1 :=
    (SimpleGraph.Walk.getVert_zero p.tail).trans
      (SimpleGraph.Walk.getVert_tail (p := p) (n := 0)).symm
  have hq1 : q.snd = q.getVert 1 :=
    (SimpleGraph.Walk.getVert_zero q.tail).trans
      (SimpleGraph.Walk.getVert_tail (p := q) (n := 0)).symm
  have hadj' : G.Adj p.snd q.snd := by rw [hv₁, hq1]; exact hadj
  set E := SimpleGraph.Adj.toWalk hadj' with hEdef
  set R := (p.tail.reverse.append E).append q.tail with hRdef
  have hElen : E.length = 1 := by
    rw [hEdef]
    simp [SimpleGraph.Adj.toWalk]
  -- support of the spliced walk
  have hsupR : R.support =
      p.support.tail.reverse ++ q.getVert 1 :: q.support.tail.tail := by
    simp only [hRdef, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse,
      p.support_tail_of_not_nil hpnn, q.support_tail_of_not_nil hqnn,
      SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.tail_cons, List.append_assoc,
      List.cons_append]
    rw [hq1]
  -- overlap exclusion between the two pieces
  have hcore2 : ∀ x, x ∈ p.support.tail → x ∈ q.support → False := by
    intro x hx1 hx2
    have hxp : p.getVert (p.support.idxOf x) = x :=
      SimpleGraph.Walk.getVert_support_idxOf p (List.mem_of_mem_tail hx1)
    have hxq : q.getVert (q.support.idxOf x) = x :=
      SimpleGraph.Walk.getVert_support_idxOf q hx2
    have hi1 : 1 ≤ p.support.idxOf x := by
      have := idxOf_tail_succ p.support hpN x hx1
      omega
    have hile : p.support.idxOf x ≤ p.length := by
      have := List.idxOf_lt_length_of_mem (List.mem_of_mem_tail hx1)
      omega
    have hjle : q.support.idxOf x ≤ q.length := by
      have := List.idxOf_lt_length_of_mem hx2
      omega
    rcases Nat.eq_zero_or_pos (q.support.idxOf x) with h0 | hj1
    · -- x = v0 sits at p-position ≥ 1
      rw [h0, SimpleGraph.Walk.getVert_zero] at hxq
      have hne := getVert_ne_of_length_eq_dist hpgeo hi1 (Nat.zero_le p.length)
        (by omega)
      rw [SimpleGraph.Walk.getVert_zero] at hne
      exact hne (hxp.trans hxq.symm)
    · exact hover (p.support.idxOf x) (q.support.idxOf x) hi1 hile hj1 hjle
        (hxp.trans hxq.symm)
  have hQmem : ∀ x ∈ q.getVert 1 :: q.support.tail.tail, x ∈ q.support := by
    intro x hx
    rcases List.mem_cons.mp hx with e | hx3
    · rw [e]
      exact SimpleGraph.Walk.getVert_mem_support q 1
    · exact List.mem_of_mem_tail (List.mem_of_mem_tail hx3)
  have hq1idx : q.support.idxOf (q.getVert 1) = 1 := by
    have hq0mem : q.getVert 0 ∈ q.support :=
      SimpleGraph.Walk.getVert_mem_support q 0
    have hq1mem : q.getVert 1 ∈ q.support :=
      SimpleGraph.Walk.getVert_mem_support q 1
    have hadj01 : G.Adj (q.getVert 0) (q.getVert 1) :=
      SimpleGraph.Walk.adj_getVert_succ q h1m
    have hgeo := geodesic_adj_support_succ hconn hq hq0mem hq1mem hadj01
    have hq0idx : q.support.idxOf (q.getVert 0) = 0 := by
      have hgx : q.getVert (q.support.idxOf (q.getVert 0)) = q.getVert 0 :=
        SimpleGraph.Walk.getVert_support_idxOf q hq0mem
      rcases Nat.eq_zero_or_pos (q.support.idxOf (q.getVert 0)) with k0 | k1
      · exact k0
      · exact absurd hgx (getVert_ne_of_length_eq_dist hq
          (by have := List.idxOf_lt_length_of_mem hq0mem; omega)
          (Nat.zero_le q.length) (by omega))
    rcases hgeo with h | h
    · rw [hq0idx] at h; omega
    · omega
  -- index positions in the spliced support
  have hPpos : ∀ x ∈ p.support.tail,
      R.support.idxOf x = r - p.support.idxOf x := by
    intro x hx
    have hxr : x ∈ p.support.tail.reverse := List.mem_reverse.mpr hx
    rw [hsupR, List.idxOf_append_of_mem hxr]
    have h1 := idxOf_reverse_mem p.support.tail
      (List.nodup_reverse.mpr hpN.tail) x hx
    have h2b := idxOf_tail_succ p.support hpN x hx
    have h3 : p.support.tail.reverse.length = r := by
      rw [List.length_reverse, List.length_tail, hplen]
    omega
  have hQpos : ∀ x ∈ q.getVert 1 :: q.support.tail.tail,
      R.support.idxOf x = r + q.support.idxOf x - 1 := by
    intro x hx
    have hxr : x ∉ p.support.tail.reverse := by
      intro hc
      exact hcore2 x (List.mem_reverse.mp hc) (hQmem x hx)
    rw [hsupR, List.idxOf_append_of_notMem hxr]
    have h1 := List.idxOf_eq_length hxr
    have h2a : p.support.tail.reverse.length = r := by
      rw [List.length_reverse, List.length_tail, hplen]
    rcases List.mem_cons.mp hx with e | hx3
    · subst e
      rw [List.idxOf_cons_self]
      omega
    · have h2t := idxOf_tail_succ q.support.tail hqN.tail x hx3
      have h2c := idxOf_tail_succ q.support hqN x (List.mem_of_mem_tail hx3)
      omega
  have hdisj2 : List.Disjoint p.support.tail.reverse
      (q.getVert 1 :: q.support.tail.tail) := by
    intro x hx1 hx2
    exact hcore2 x (List.mem_reverse.mp hx1) (hQmem x hx2)
  have hLnd : R.support.Nodup := by
    rw [hsupR]
    exact (List.nodup_reverse.mpr hpN.tail).append hqN.tail.tail hdisj2
  -- chord-freeness of the spliced support
  have hchord : ∀ u v, u ∈ R.support → v ∈ R.support → G.Adj u v →
      (R.support.idxOf u + 1 = R.support.idxOf v ∨
        R.support.idxOf v + 1 = R.support.idxOf u) := by
    intro u v hu hv hadj
    rw [hsupR, List.mem_append] at hu hv
    rcases hu with hu1 | hu2 <;> rcases hv with hv1 | hv2
    · -- both in the p-part
      rw [List.mem_reverse] at hu1 hv1
      have hu1' : u ∈ p.support := List.mem_of_mem_tail hu1
      have hv1' : v ∈ p.support := List.mem_of_mem_tail hv1
      have hgeo := geodesic_adj_support_succ hconn hpgeo hu1' hv1' hadj
      have hui := hPpos u hu1
      have hvi := hPpos v hv1
      have hib : p.support.idxOf u ≤ p.length := by
        have := List.idxOf_lt_length_of_mem hu1'; omega
      have hjb : p.support.idxOf v ≤ p.length := by
        have := List.idxOf_lt_length_of_mem hv1'; omega
      rcases hgeo with h | h
      · right; omega
      · left; omega
    · -- u in p-part, v in q-part
      rw [List.mem_reverse] at hu1
      have hu1' : u ∈ p.support := List.mem_of_mem_tail hu1
      have hv2' : v ∈ q.support := hQmem v hv2
      have hgu : p.getVert (p.support.idxOf u) = u :=
        SimpleGraph.Walk.getVert_support_idxOf p hu1'
      have hgv : q.getVert (q.support.idxOf v) = v :=
        SimpleGraph.Walk.getVert_support_idxOf q hv2'
      have hi1 : 1 ≤ p.support.idxOf u := by
        have := idxOf_tail_succ p.support hpN u hu1
        omega
      have hile : p.support.idxOf u ≤ p.length := by
        have := List.idxOf_lt_length_of_mem hu1'
        omega
      have hjle : q.support.idxOf v ≤ q.length := by
        have := List.idxOf_lt_length_of_mem hv2'
        omega
      have hui := hPpos u hu1
      have hvi := hQpos v hv2
      rcases Nat.lt_or_ge (p.support.idxOf u) 2 with h1i | h2i
      · -- i = 1: u = v1
        have hi1' : p.support.idxOf u = 1 := by omega
        rw [hi1'] at hgu
        rcases Nat.lt_or_ge (q.support.idxOf v) 2 with hjv1 | hjv2
        · -- j = 1: v = q1: the chord, now between positions r-1 and r
          have hj1 : q.support.idxOf v = 1 := by omega
          refine Or.inl ?_
          omega
        · -- j ≥ 2: contradicts 7b
          exact absurd (show G.Adj (p.getVert 1)
              (q.getVert (q.support.idxOf v)) from by
            rw [hgu, hgv]; exact hadj) (h7b _ hjv2 hjle)
      · -- i ≥ 2: contradicts 7a
        exact absurd (show G.Adj (q.getVert (q.support.idxOf v))
              (p.getVert (p.support.idxOf u)) from by
            rw [hgv, hgu]; exact hadj.symm)
          (h7a _ _ hjle hile h2i)
    · -- u in q-part, v in p-part
      rw [List.mem_reverse] at hv1
      have hv1' : v ∈ p.support := List.mem_of_mem_tail hv1
      have hu2' : u ∈ q.support := hQmem u hu2
      have hgv : p.getVert (p.support.idxOf v) = v :=
        SimpleGraph.Walk.getVert_support_idxOf p hv1'
      have hgu : q.getVert (q.support.idxOf u) = u :=
        SimpleGraph.Walk.getVert_support_idxOf q hu2'
      have hj1 : 1 ≤ q.support.idxOf u := by
        rcases List.mem_cons.mp hu2 with e | hx3
        · rw [e]; omega
        · have h2t := idxOf_tail_succ q.support.tail hqN.tail u hx3
          have h2c := idxOf_tail_succ q.support hqN u
            (List.mem_of_mem_tail hx3)
          omega
      have hjle : q.support.idxOf u ≤ q.length := by
        have := List.idxOf_lt_length_of_mem hu2'
        omega
      have hile : p.support.idxOf v ≤ p.length := by
        have := List.idxOf_lt_length_of_mem hv1'
        omega
      have hui := hQpos u hu2
      have hvi := hPpos v hv1
      rcases Nat.lt_or_ge (p.support.idxOf v) 2 with h1i | h2i
      · -- j = 1: v = v1
        have hi1' : p.support.idxOf v = 1 := by omega
        rw [hi1'] at hgv
        rcases Nat.lt_or_ge (q.support.idxOf u) 2 with hjv1 | hjv2
        · -- i = 1: u = q1: the chord, positions r-1 and r
          have hj1' : q.support.idxOf u = 1 := by omega
          refine Or.inr ?_
          omega
        · -- i ≥ 2: contradicts 7b
          exact absurd (show G.Adj (p.getVert 1)
              (q.getVert (q.support.idxOf u)) from by
            rw [hgv, hgu]; exact hadj.symm) (h7b _ hjv2 hjle)
      · -- j ≥ 2: contradicts 7a
        exact absurd (show G.Adj (q.getVert (q.support.idxOf u))
              (p.getVert (p.support.idxOf v)) from by
            rw [hgu, hgv]; exact hadj)
          (h7a _ _ hjle hile h2i)
    · -- both in the q-part
      have hu2' : u ∈ q.support := hQmem u hu2
      have hv2' : v ∈ q.support := hQmem v hv2
      have hgeo := geodesic_adj_support_succ hconn hq hu2' hv2' hadj
      have hui := hQpos u hu2
      have hvi := hQpos v hv2
      rcases hgeo with h | h
      · left; omega
      · right; omega
  refine ⟨R.support.toFinset, isInducedTree_of_walk_chords R hchord, ?_, ?_⟩
  · rw [List.mem_toFinset]
    exact SimpleGraph.Walk.start_mem_support R
  · rw [List.toFinset_card_of_nodup hLnd, SimpleGraph.Walk.length_support,
      hRdef, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse, hElen]
    have hpl1 : p.tail.length + 1 = p.length :=
      SimpleGraph.Walk.length_tail_add_one hpnn
    have hql1 : q.tail.length + 1 = q.length :=
      SimpleGraph.Walk.length_tail_add_one hqnn
    omega


/-- **Rooted Chung lemma.** If deleting the non-cut vertex `a` lowers the
radius by exactly one and `r ≥ 2`, the graph contains an induced tree on at
least `2r - 1` vertices that contains `a`. -/
theorem rooted_chung {G : SimpleGraph α} (hconn : G.Connected) {a : α}
    (hr2 : 2 ≤ G.radius.toNat)
    (hdrop : radOn G (Finset.univ.erase a) + 1 ≤ G.radius) :
    ∃ S : Finset α, IsInducedTree G S ∧ a ∈ S ∧
      2 * G.radius.toNat - 1 ≤ S.card := by
  obtain ⟨v₀, v₂, w, p, q, hp, hdva, hmle, h2, hv₂, hpw, h7a, h7b, h7c,
    hover⟩ := chung_chords hconn hr2 hdrop
  have hpgeo : p.length = G.dist v₀ a := hp.trans hdva.symm
  rcases Nat.eq_zero_or_pos q.length with hm0 | h1m
  · -- m = 0: r = 2 and the geodesic p alone spans 2r - 1 vertices
    have h2' : 2 ≤ p.length := by rw [hp]; exact hr2
    have hv₂₀ : G.dist v₂ v₀ = 2 := by
      rw [← hv₂]
      exact dist_getVert_of_length_eq_dist hpgeo 2 h2'
    have ht : G.dist v₂ w ≤ 2 := by
      have htr := hconn.dist_triangle (u := v₂) (v := v₀) (w := w)
      rw [hv₂₀, ← hq, hm0] at htr
      omega
    refine ⟨p.support.toFinset, isInducedTree_of_walk_chords p ?_, ?_, ?_⟩
    · intro u v hu hv hadj
      exact geodesic_adj_support_succ hconn hpgeo hu hv hadj
    · rw [List.mem_toFinset]
      exact SimpleGraph.Walk.end_mem_support p
    · rw [List.toFinset_card_of_nodup
        (isPath_of_length_eq_dist hconn hpgeo).support_nodup,
        SimpleGraph.Walk.length_support, hp]
      omega
  · by_cases hadj : G.Adj (p.getVert 1) (q.getVert 1)
    · exact rooted_chung_chord hconn hp hdva hq h2 h7a h7b hover h7c h1m hadj
    · exact rooted_chung_flat hconn hp hdva hq h2 hv₂ hpw h7a h7b hover hadj

'''

p = 'Graffiti84/RootedChung.lean'
s = open(p, encoding='utf-8').read()
marker = 'end Graffiti84'
assert marker in s and s.count(marker) == 1
s = s.replace(marker, ADD + marker)
open(p, 'w', encoding='utf-8').write(s)
print('rooted_chung_chord + rooted_chung appended')
