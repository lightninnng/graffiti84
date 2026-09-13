# -*- coding: utf-8 -*-
"""Rewrite batch 3b part 2 with self-proved index bridges (no API gambling)."""

ADD = r'''
private lemma abs_one_split : ∀ a : ℤ, |a| = 1 → a = 1 ∨ a = -1 := by
  intro a h
  by_cases ha : 0 ≤ a
  · rw [Int.abs_of_nonneg ha] at h
    left
    omega
  · rw [Int.abs_of_neg (by omega : a < 0)] at h
    right
    omega

private lemma get!_of? {β : Type*} [Inhabited β] : ∀ {l : List β} {i : ℕ} {x : β},
    l[i]? = some x → l[i]! = x := by
  intro l
  induction l with
  | nil => intro i x h; simp at h
  | cons h r ih =>
      intro i x h
      cases i with
      | zero => simpa using h.symm
      | succ i' => simpa using ih h

private lemma map_getElem! {β γ : Type*} [Inhabited γ] (f : β → γ) :
    ∀ {l : List β} {i : ℕ}, (l.map f)[i]! = f l[i]! := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons h r ih =>
      intro i
      cases i with
      | zero => simp
      | succ i' => simpa using ih

private lemma tail_getElem? {β : Type*} : ∀ {l : List β} {t : ℕ},
    l.tail[t]? = l[t + 1]? := by
  intro l
  induction l with
  | nil => intro t; simp
  | cons h r ih =>
      intro t
      cases t with
      | zero => simp
      | succ t' => simpa using ih

private lemma tail_getElem! {β : Type*} [Inhabited β] : ∀ {l : List β} {t : ℕ},
    l.tail[t]! = l[t + 1]! := by
  intro l
  induction l with
  | nil => intro t; simp
  | cons h r ih =>
      intro t
      cases t with
      | zero => simp
      | succ t' => simpa using ih

/-- **Potential-function acyclicity criterion.** If `φ` is injective on `S`
and every `S`-edge changes `φ` by exactly one, then `S` induces a forest:
around a maximum-`φ` vertex of any hypothetical cycle, its two neighbours
carry equal `φ`-value, hence coincide, forcing a repeated vertex in the
cycle tail or a repeated edge. -/
theorem acyclicWithin_of_phi {G : SimpleGraph α} [Inhabited α] {S : Finset α}
    (φ : α → ℤ)
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
    have hsupget! : ∀ i (hi : i < w.length + 1), sup[i]! = w.getVert i := by
      intro i hi
      have h1 : some (w.getVert i) = sup[i]? := by
        rw [hsupdef]
        exact w.getVert_eq_support_getElem? (by omega)
      exact get!_of? h1.symm
    have hstepΦ : ∀ i (hi : i + 1 < Φ.length),
        (Φ[i + 1]! - Φ[i]! = 1 ∨ Φ[i + 1]! - Φ[i]! = -1) := by
      intro i hi
      have hadj : G.Adj (w.getVert i) (w.getVert (i + 1)) :=
        w.adj_getVert_succ (by omega)
      have hm1 : w.getVert (i + 1) ∈ S := hwsub _ (w.getVert_mem_support _)
      have hm0 : w.getVert i ∈ S := hwsub _ (w.getVert_mem_support _)
      rw [map_getElem! φ, map_getElem! φ, hsupget! _ (by omega), hsupget! _ (by omega)]
      exact abs_one_split _ (hstep _ hm0 _ hm1 hadj)
    have hfirst : sup[0]! = a := by
      rw [hsupget! 0 (by omega)]
      exact SimpleGraph.Walk.getVert_zero w
    have hlast : sup[w.length]! = a := by
      rw [hsupget! w.length (by omega)]
      exact SimpleGraph.Walk.getVert_length w
    have hclosed : Φ[0]! = Φ[Φ.length - 1]! := by
      rw [map_getElem! φ, map_getElem! φ, hfirst, hlast, hΦlen]
    have hk1 : w.length ≠ 1 := by
      intro hk1
      have hs := hstepΦ 0 (by omega)
      rw [map_getElem! φ, map_getElem! φ, hfirst, hlast, hΦlen] at hs
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
      refine ⟨φ a, ?_⟩
      rw [List.mem_toFinset, hΦdef, List.mem_map]
      exact ⟨a, w.start_mem_support, rfl⟩
    set μ := Φ.toFinset.max' hVne with hμdef
    have hub : ∀ i (hi : i < Φ.length), Φ[i]! ≤ μ := by
      intro i hi
      exact Finset.le_max' _ _
        (List.mem_toFinset.mpr (List.mem_map_of_mem (l := sup) (f := φ)
          (by rw [hsupdef]; exact w.getVert_mem_support _)))
    obtain ⟨i0, hi0lt, hi0val⟩ : ∃ i, i < Φ.length ∧ Φ[i]! = μ := by
      have hmem : μ ∈ Φ := List.mem_toFinset.mp (Finset.max'_mem _ _)
      rw [hΦdef, List.mem_map] at hmem
      obtain ⟨x, hxmem, hxval⟩ := hmem
      have hidxlt : sup.idxOf x < sup.length := List.idxOf_lt_length_of_mem hxmem
      refine ⟨sup.idxOf x, ?_, ?_⟩
      · rw [hΦdef, List.length_map, hsupdef, SimpleGraph.Walk.length_support]
        omega
      · rw [map_getElem! φ, hsupget! _ (by omega), ← hxval]
        have h1 : some (w.getVert (sup.idxOf x)) = sup[sup.idxOf x]? := by
          rw [hsupdef]
          exact w.getVert_eq_support_getElem? (by omega)
        have h2 : sup[sup.idxOf x]? = some x := List.getElem?_idxOf hxmem
        rw [get!_of? (h1.symm.trans h2)]
    obtain ⟨i1, hi1lt, hi1val⟩ :
        ∃ i, i < Φ.length - 1 ∧ Φ[i]! = μ := by
      by_cases hcase : i0 = Φ.length - 1
      · have hz : Φ[Φ.length - 1]! = μ := by rw [hcase]; exact hi0val
        refine ⟨0, by omega, ?_⟩
        calc Φ[0]! = Φ[Φ.length - 1]! := hclosed
        _ = μ := hz
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
    obtain ⟨m, n, hmn, hmval, hnval, hposm, hposn⟩ :
        ∃ m n : ℕ, m < n ∧ Φ[m]! = μ - 1 ∧ Φ[n]! = μ - 1 ∧
          1 ≤ m ∧ n ≤ Φ.length - 1 := by
      by_cases hcase : i1 = 0
      · have h0 : Φ[0]! = μ := by rw [hcase]; exact hi1val
        refine ⟨1, Φ.length - 1, by omega, hneighb 1 (by omega) (Or.inl rfl),
          hneighb (Φ.length - 1) (by omega) (Or.inl rfl), by omega, le_refl _⟩
        rw [hcase] at hi1val
      · exact ⟨i1 - 1, i1 + 1, by omega, hneighb (i1 - 1) (by omega) (Or.inr rfl),
          hneighb (i1 + 1) (by omega) (Or.inl rfl), by omega, by omega⟩
    have hpointeq : w.getVert m = w.getVert n := by
      have hmS : w.getVert m ∈ S := hwsub _ (w.getVert_mem_support _)
      have hnS : w.getVert n ∈ S := hwsub _ (w.getVert_mem_support _)
      have hφ : φ (w.getVert m) = φ (w.getVert n) := by
        rw [← hsupget! m (by omega), ← hsupget! n (by omega), hmval, hnval]
      exact hinj _ hmS _ hnS hφ
    have hND2 := (List.nodup_iff_getElem?_ne_getElem?).mp hcy.support_nodup
    have hne := hND2 (m - 1) (n - 1) (by omega) (by rw [List.length_tail]; omega)
    have hm? : w.support.tail[m - 1]? = some (sup[m]!) := by
      rw [tail_getElem?, show m - 1 + 1 = m from by omega, hsupget! m (by omega)]
      exact (w.getVert_eq_support_getElem? (by omega)).symm
    have hn? : w.support.tail[n - 1]? = some (sup[n]!) := by
      rw [tail_getElem?, show n - 1 + 1 = n from by omega, hsupget! n (by omega)]
      exact (w.getVert_eq_support_getElem? (by omega)).symm
    rw [hm?, hn?, hpointeq] at hne
    exact absurd rfl hne

/-- **F2.** Every pair of vertices carries an induced tree containing a
geodesic between them; in particular `t(G) ≥ dist(u,v) + 1`. -/
theorem treeNumber_ge_dist_add_one {G : SimpleGraph α} (hconn : G.Connected)
    (u v : α) : G.dist u v + 1 ≤ treeNumber G := by
  haveI : Inhabited α := ⟨u⟩
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
    · exact (SimpleGraph.Walk.support_dropUntil_suffix_support p hx').subset h
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h
      exact (SimpleGraph.Walk.support_dropUntil_suffix_support p hy').subset h
  have hacyc : AcyclicWithin G S := by
    refine acyclicWithin_of_phi (fun z => (p.support.idxOf z : ℤ)) ?_ ?_
    · intro x hx y hy heq
      have hx' : x ∈ p.support := List.mem_toFinset.mp hx
      have hy' : y ∈ p.support := List.mem_toFinset.mp hy
      have hnat : p.support.idxOf x = p.support.idxOf y := by omega
      exact List.idxOf_inj hx' |>.mp hnat
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
  have hmem : S ∈ Finset.univ.filter (fun T : Finset α => IsInducedTree G T) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ S, htree⟩
  calc G.dist u v + 1 = S.card := hcard.symm
    _ ≤ treeNumber G := Finset.le_sup hmem
'''

import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()
start = s.index('private lemma abs_one_split')
end = s.index('end Graffiti84')
assert start < end
NEW = ADD + '\n'
import re
assert not re.search(r'\b(sorry|admit)\b', NEW)
s = s[:start] + NEW + s[end:]
io.open(p, 'w', encoding='utf-8').write(s)
print('rewrote criterion + F2 (v3)')
