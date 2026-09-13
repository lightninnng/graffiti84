# -*- coding: utf-8 -*-
"""Append batch 3b part 2: potential-function acyclicity criterion + F2."""

ADD = r'''
private lemma abs_one_split : ∀ a : ℤ, |a| = 1 → a = 1 ∨ a = -1 := by
  intro a h
  omega

private lemma tail_getElem! {β : Type*} {l : List β} {t : ℕ}
    (ht : t + 1 < l.length) : l.tail[t]! = l[t + 1]! := by
  cases l with
  | nil => simp at ht
  | cons h r =>
      cases t with
      | zero => simp
      | succ t' => simp

/-- **Potential-function acyclicity criterion.** If `φ` is injective on `S`
and every `S`-edge changes `φ` by exactly one, then `S` induces a forest:
around a maximum-`φ` vertex of any hypothetical cycle, its two neighbours
carry equal `φ`-value, hence coincide, forcing a repeated vertex in the
cycle tail or a repeated edge. -/
theorem acyclicWithin_of_phi {G : SimpleGraph α} {S : Finset α} (φ : α → ℤ)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, φ x = φ y → x = y)
    (hstep : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → |φ x - φ y| = 1) :
    AcyclicWithin G S := by
  intro a w hwsub
  by_cases hw0 : w.length = 0
  · exact Or.inl hw0
  · refine Or.inr fun hcy => ?_
    exfalso
    set sup := w.support with hsupdef
    set Φ := sup.map φ with hΦdef
    have hΦlen : Φ.length = w.length + 1 := by
      rw [hΦdef, List.length_map, hsupdef, SimpleGraph.Walk.length_support]
    have hstepΦ : ∀ i (hi : i + 1 < Φ.length),
        (Φ[i + 1]! - Φ[i]! = 1 ∨ Φ[i + 1]! - Φ[i]! = -1) := by
      intro i hi
      have h1 : i + 1 < sup.length := by omega
      have h2 : i < sup.length := by omega
      have hv1 : sup[i + 1]! = w.getVert (i + 1) :=
        (w.getVert_eq_support_getElem (by omega)).symm
      have hv0 : sup[i]! = w.getVert i := (w.getVert_eq_support_getElem (by omega)).symm
      have hadj : G.Adj (w.getVert i) (w.getVert (i + 1)) :=
        w.adj_getVert_succ (by rw [hsupdef, SimpleGraph.Walk.length_support]; omega)
      have hm1 : w.getVert (i + 1) ∈ S := hwsub _ (by
        rw [hsupdef, ← hv1]; exact List.getElem_mem)
      have hm0 : w.getVert i ∈ S := hwsub _ (by
        rw [hsupdef, ← hv0]; exact List.getElem_mem)
      rw [hΦdef, List.getElem_map, List.getElem_map]
      exact abs_one_split _ (hstep _ hm0 _ hm1 hadj)
    have hfirst : sup[0]! = a := by
      have h := w.getVert_eq_support_getElem (Nat.zero_le _)
      simp only [SimpleGraph.Walk.getVert_zero] at h
      exact h.symm
    have hlast : sup[w.length]! = a := by
      have h := w.getVert_eq_support_getElem (Nat.le_refl _)
      rw [SimpleGraph.Walk.getVert_length] at h
      exact h.symm
    have hclosed : Φ[0]! = Φ[Φ.length - 1]! := by
      rw [hΦdef, List.getElem_map, List.getElem_map, hfirst, hlast, hΦlen]
      norm_num
    have hk1 : w.length ≠ 1 := by
      intro hk1
      have hs := hstepΦ 0 (by rw [hΦlen, hk1]; omega)
      rw [hΦdef, List.getElem_map, List.getElem_map, hfirst, hlast] at hs
      norm_num at hs
    have hk2 : w.length ≠ 2 := by
      intro hk2
      have hND := hcy.edges_nodup
      cases hw : w with
      | nil => omega
      | @cons a x c1 h1 r =>
          cases r with
          | nil => omega
          | @cons x y c2 h2 r' =>
              cases r' with
              | nil =>
                  rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons,
                    SimpleGraph.Walk.edges_nil, List.nodup_cons] at hND
                  exact hND.1 (List.mem_cons.mpr (Or.inl Sym2.eq_swap))
              | @cons z c3 h3 r'' => omega
    have hk3 : 3 ≤ w.length := by omega
    have hVne : Φ.toFinset.Nonempty := by
      refine ⟨Φ[0]!, ?_⟩
      rw [List.mem_toFinset, hΦdef, List.mem_map]
      exact ⟨_, List.getElem_mem, rfl⟩
    set μ := Φ.toFinset.max' hVne with hμdef
    have hub : ∀ i (hi : i < Φ.length), Φ[i]! ≤ μ := fun i hi =>
      Finset.le_max' _ _ (List.mem_toFinset.mpr (by
        rw [hΦdef]; exact List.getElem_mem))
    obtain ⟨i0, hi0lt, hi0val⟩ : ∃ i, i < Φ.length ∧ Φ[i]! = μ := by
      have hmem : μ ∈ Φ := List.mem_toFinset.mp (Finset.max'_mem _ _)
      obtain ⟨i, hi⟩ := List.mem_iff_get?.mp hmem
      rw [List.getElem?_eq_some_iff] at hi
      obtain ⟨hilt, hival⟩ := hi
      refine ⟨i, hilt, ?_⟩
      have : Φ[i]? = some Φ[i]! := List.getElem?_eq_getElem hilt
      rw [hi] at this
      simpa using this.symm
    obtain ⟨i1, hi1lt, hi1val⟩ :
        ∃ i, i < Φ.length - 1 ∧ Φ[i]! = μ := by
      by_cases hcase : i0 = Φ.length - 1
      · refine ⟨0, by omega, ?_⟩
        calc Φ[0]! = Φ[Φ.length - 1]! := hclosed
        _ = μ := by rw [hcase]; exact hi0val
      · exact ⟨i0, by omega, hi0val⟩
    have hneighb : ∀ j (hj : j < Φ.length), (j = i1 + 1 ∨ j + 1 = i1) →
        Φ[j]! = μ - 1 := by
      intro j hj hjpos
      have hjb : Φ[j]! ≤ μ := hub j hj
      rcases hjpos with h' | h'
      · have hs := hstepΦ i1 (by rw [h']; omega)
        rw [h'] at hs
        rw [hi1val] at hs
        omega
      · have hs := hstepΦ j (by rw [h']; omega)
        rw [hi1val] at hs
        omega
    obtain ⟨m, n, hmn, hmval, hnval, hposm, hposn, hne_triv⟩ :
        ∃ m n : ℕ, m < n ∧ Φ[m]! = μ - 1 ∧ Φ[n]! = μ - 1 ∧
          1 ≤ m ∧ n ≤ Φ.length - 1 ∧ (m, n) ≠ (0, Φ.length - 1) := by
      by_cases hcase : i1 = 0
      · refine ⟨1, Φ.length - 1, by omega, ?_, hneighb (Φ.length - 1) (by omega)
            (Or.inl rfl), by omega, le_refl _, ?_⟩
        · rw [hcase] at hi1val
          have := hneighb 1 (by omega) (Or.inl rfl)
          omega
        · intro hpair
          have : (1 : ℕ) = 0 := hpair.1
          omega
      · refine ⟨i1 - 1, i1 + 1, by omega, hneighb (i1 - 1) (by omega) (Or.inr rfl),
          hneighb (i1 + 1) (by omega) (Or.inl rfl), by omega, by omega, ?_⟩
        · intro hpair
          rcases hpair.1 with h' | h'
          · have hi1z : i1 - 1 = 0 := h'
            have hin : i1 + 1 = Φ.length - 1 := by
              rcases hpair.2 with h'' | h''
              · exact h''
              · omega
            omega
          · have : (i1 - 1 : ℕ) = 0 + 1 := h'
            omega
    have hpointeq : sup[m]! = sup[n]! := by
      have hmS : sup[m]! ∈ S := hwsub _ (by rw [hsupdef]; exact List.getElem_mem)
      have hnS : sup[n]! ∈ S := hwsub _ (by rw [hsupdef]; exact List.getElem_mem)
      have hφ : φ (sup[m]!) = φ (sup[n]!) := by
        rw [hΦdef, List.getElem_map, List.getElem_map] at hmval hnval
        rw [hmval, hnval]
      exact hinj _ hmS _ hnS hφ
    have hND2 := (List.nodup_iff_getElem?_ne_getElem?).mp hcy.support_nodup
    have hne := hND2 (m - 1) (n - 1) (by omega) (by rw [List.length_tail]; omega)
    have hmt : m - 1 + 1 < w.support.length := by
      rw [SimpleGraph.Walk.length_support]; omega
    have hnt : n - 1 + 1 < w.support.length := by
      rw [SimpleGraph.Walk.length_support]; omega
    have hm? : w.support.tail[m - 1]? = some (sup[m]!) := by
      rw [List.getElem?_eq_getElem (by rw [List.length_tail]; omega)]
      rw [tail_getElem! hmt, show m - 1 + 1 = m from by omega]
      rfl
    have hn? : w.support.tail[n - 1]? = some (sup[n]!) := by
      rw [List.getElem?_eq_getElem (by rw [List.length_tail]; omega)]
      rw [tail_getElem! hnt, show n - 1 + 1 = n from by omega]
      rfl
    rw [hm?, hn?, hpointeq] at hne
    exact absurd rfl hne

/-- **F2.** Every pair of vertices carries an induced tree containing a
geodesic between them; in particular `t(G) ≥ dist(u,v) + 1`. -/
theorem treeNumber_ge_dist_add_one {G : SimpleGraph α} (hconn : G.Connected)
    (u v : α) : G.dist u v + 1 ≤ treeNumber G := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  have hpath := isPath_of_length_eq_dist hconn hp
  set S := p.support.toFinset with hSdef
  have hconnw : ∀ x ∈ S, ∀ y ∈ S, ConnectsWithin G S x y := by
    intro x hx y hy
    have hx' : x ∈ p.support := List.mem_toFinset.mp hx
    have hy' : y ∈ p.support := List.mem_toFinset.mp hy
    refine ⟨(p.dropUntil x hx').append ((p.dropUntil y hy').reverse), ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rw [hSdef, List.mem_toFinset]
    rcases hz with h | h
    · exact ((SimpleGraph.Walk.support_dropUntil_suffix_support p hx').subset) h
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h
      exact (SimpleGraph.Walk.support_dropUntil_suffix_support p hy').subset h
  have hacyc : AcyclicWithin G S := by
    refine acyclicWithin_of_phi (fun z => (p.support.idxOf z : ℤ)) ?_ ?_
    · intro x hx y hy heq
      have hx' : x ∈ p.support := List.mem_toFinset.mp hx
      have hy' : y ∈ p.support := List.mem_toFinset.mp hy
      exact (SimpleGraph.Walk.getVert_support_idxOf p hx').symm.trans
        (heq ▸ SimpleGraph.Walk.getVert_support_idxOf p hy')
    · intro x hx y hy hadj
      have hx' : x ∈ p.support := List.mem_toFinset.mp hx
      have hy' : y ∈ p.support := List.mem_toFinset.mp hy
      rcases geodesic_adj_support_succ hconn hp hx' hy' hadj with h | h
      · rw [← h]; norm_num
      · rw [← h]; norm_num
  have htree : IsInducedTree G S := ⟨hconnw, hacyc⟩
  have hcard : S.card = G.dist u v + 1 := by
    rw [hSdef, List.toFinset_card_of_nodup hpath.support_nodup,
      SimpleGraph.Walk.length_support, hp]
  calc G.dist u v + 1 = S.card := hcard.symm
    _ ≤ treeNumber G := Finset.le_sup (f := fun T => T.card) (by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ S, htree⟩)
'''

import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()
marker = 'end Graffiti84'
assert marker in s
import re
assert not re.search(r'\b(sorry|admit)\b', ADD)
s = s.replace(marker, ADD + '\n' + marker)
io.open(p, 'w', encoding='utf-8').write(s)
print('appended criterion + F2')
