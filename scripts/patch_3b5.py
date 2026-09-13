# -*- coding: utf-8 -*-
"""v5: fix helper lemmas (simp/length_cons), hsplen, hlast statement, direction fixes."""

HEAD = r'''
private lemma get!_of? {β : Type*} [Inhabited β] : ∀ {l : List β} {i : ℕ} {x : β},
    l[i]? = some x → l[i]! = x := by
  intro l
  induction l with
  | nil => intro i x h; simp at h
  | cons h r ih =>
      intro i x h
      cases i with
      | zero =>
          simp at h ⊢
          exact h
      | succ i' => simpa using ih h

private lemma map_getElem! {β γ : Type*} [Inhabited β] [Inhabited γ] (f : β → γ) :
    ∀ {l : List β} {i : ℕ}, i < l.length → (l.map f)[i]! = f l[i]! := by
  intro l
  induction l with
  | nil => intro i hi; simp at hi
  | cons h r ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i' =>
          have hlen := List.length_cons h r
          simpa using ih (by omega)

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

/-- **Potential-function acyclicity criterion.** If `φ` is injective on `S`
and every `S`-edge changes `φ` by exactly one, then `S` induces a forest:
around a maximum-`φ` vertex of any hypothetical cycle, its two neighbours
carry equal `φ`-value, hence coincide, forcing a repeated vertex in the
cycle tail or a repeated edge. -/
theorem acyclicWithin_of_phi {G : SimpleGraph α} [Inhabited α] {S : Finset α}
    (φ : α → ℤ)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, φ x = φ y → x = y)
    (hstep : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y →
      (φ x - φ y = 1 ∨ φ x - φ y = -1)) :
    AcyclicWithin G S := by
  intro a w hwsub
  by_cases hw0 : w.length = 0
  · exact Or.inl hw0
  · refine Or.inr fun hcy => ?_
    exfalso
    set sup := w.support with hsupdef
    set Φ := sup.map φ with hΦdef
    have hsplen : sup.length = w.length + 1 := by
      rw [hsupdef, SimpleGraph.Walk.length_support]
    have hΦlen : Φ.length = w.length + 1 := by
      rw [hΦdef, List.length_map, hsplen]
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
      rw [map_getElem! φ (by omega), map_getElem! φ (by omega),
        hsupget! _ (by omega), hsupget! _ (by omega)]
      rcases hstep _ hm0 _ hm1 hadj with h | h
      · right; linarith [h]
      · left; linarith [h]
    have hfirst : sup[0]! = a := by
      rw [hsupget! 0 (by omega)]
      exact SimpleGraph.Walk.getVert_zero w
    have hlast : sup[Φ.length - 1]! = a := by
      rw [show Φ.length - 1 = w.length from by omega]
      rw [hsupget! w.length (by omega)]
      exact SimpleGraph.Walk.getVert_length w
    have hclosed : Φ[0]! = Φ[Φ.length - 1]! := by
      rw [map_getElem! φ (by omega), map_getElem! φ (by omega), hfirst, hlast]
    have hk1 : w.length ≠ 1 := by
      intro hk1
      have hs := hstepΦ 0 (by omega)
      rw [map_getElem! φ (by omega), map_getElem! φ (by omega), hfirst, hlast] at hs
      norm_num at hs
    have hk2 : w.length ≠ 2 := by
      intro hk2
      have hND := hcy.edges_nodup
      cases hw : w with
      | nil => rw [hw] at hk2; simp at hk2
      | @cons a x c1 h1 r =>
          cases hr : r with
          | nil => rw [hw, hr] at hk2; simp at hk2
          | @cons x y c2 h2 r' =>
              cases hr' : r' with
              | nil =>
                  rw [hw, hr, hr'] at hND
                  rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons,
                    SimpleGraph.Walk.edges_nil, List.nodup_cons] at hND
                  exact hND.1 (List.mem_cons.mpr (Or.inl Sym2.eq_swap))
              | @cons z c3 h3 r'' =>
                  rw [hw, hr, hr', SimpleGraph.Walk.length_cons,
                    SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons] at hk2
                  simp at hk2
    have hk3 : 3 ≤ w.length := by omega
    have hVne : Φ.toFinset.Nonempty := by
      refine ⟨φ a, ?_⟩
      rw [List.mem_toFinset, hΦdef, List.mem_map]
      exact ⟨a, w.start_mem_support, rfl⟩
    set μ := Φ.toFinset.max' hVne with hμdef
    have hub : ∀ i (hi : i < Φ.length), Φ[i]! ≤ μ := by
      intro i hi
      have hmem : sup[i]! ∈ sup := by
        rw [hsupget! _ (by omega), hsupdef]
        exact w.getVert_mem_support i
      have hmemΦ : Φ[i]! ∈ Φ := by
        rw [hΦdef]
        exact List.mem_map_of_mem hmem
      exact Finset.le_max' _ _ (List.mem_toFinset.mpr hmemΦ)
    obtain ⟨i0, hi0lt, hi0val⟩ : ∃ i, i < Φ.length ∧ Φ[i]! = μ := by
      have hmem : μ ∈ Φ := List.mem_toFinset.mp (Finset.max'_mem _ _)
      rw [hΦdef, List.mem_map] at hmem
      obtain ⟨x, hxmem, hxval⟩ := hmem
      have h2 : sup[sup.idxOf x]? = some x := List.getElem?_idxOf hxmem
      refine ⟨sup.idxOf x, by omega, ?_⟩
      rw [map_getElem! φ (by omega), get!_of? h2, ← hxval]
    obtain ⟨i1, hi1lt, hi1val⟩ :
        ∃ i, i < Φ.length - 1 ∧ Φ[i]! = μ := by
      by_cases hcase : i0 = Φ.length - 1
      · have hz : Φ[Φ.length - 1]! = μ := by rw [← hcase]; exact hi0val
        exact ⟨0, by omega, by rw [hclosed]; exact hz⟩
      · have hle : i0 ≤ Φ.length - 1 := by omega
        rcases Nat.eq_or_lt_of_le hle with h' | h'
        · exact absurd h'.symm hcase
        · exact ⟨i0, h', hi0val⟩
    have hneighb : ∀ j (hj : j < Φ.length), (j = i1 + 1 ∨ j + 1 = i1) →
        Φ[j]! = μ - 1 := by
      intro j hj hjpos
      have hjb : Φ[j]! ≤ μ := hub j hj
      rcases hjpos with h' | h'
      · have hs := hstepΦ i1 (by omega)
        rw [hi1val] at hs
        rw [h']
        omega
      · have hs := hstepΦ j (by omega)
        rw [← h'] at hs
        rw [hi1val] at hs
        omega
    obtain ⟨m, n, hmn, hmval, hnval, hposm, hposn⟩ :
        ∃ m n : ℕ, m < n ∧ Φ[m]! = μ - 1 ∧ Φ[n]! = μ - 1 ∧
          1 ≤ m ∧ n ≤ Φ.length - 1 := by
      by_cases hcase : i1 = 0
      · have hLast : Φ[Φ.length - 1]! = μ := by
          rw [hclosed, hcase]
          exact hi1val
        have hv1 : Φ[1]! = μ - 1 := hneighb 1 (by omega)
          (Or.inl (by omega))
        have hvm2 : Φ[Φ.length - 2]! = μ - 1 := by
          have hs := hstepΦ (Φ.length - 2) (by omega)
          rw [show Φ.length - 2 + 1 = Φ.length - 1 from by omega] at hs
          rw [hLast] at hs
          have hub2 : Φ[Φ.length - 2]! ≤ μ := hub _ (by omega)
          omega
        exact ⟨1, Φ.length - 2, by omega, hv1, hvm2, by omega, by omega⟩
      · have hi1pos : 0 < i1 := Nat.pos_of_ne_zero hcase
        refine ⟨i1 - 1, i1 + 1, by omega, ?_, ?_, by omega, by omega⟩
        · exact hneighb (i1 - 1) (by omega) (Or.inr (by omega))
        · exact hneighb (i1 + 1) (by omega) (Or.inl rfl)
    have hpointeq : w.getVert m = w.getVert n := by
      have hmS : w.getVert m ∈ S := hwsub _ (w.getVert_mem_support _)
      have hnS : w.getVert n ∈ S := hwsub _ (w.getVert_mem_support _)
      have hφ : φ (w.getVert m) = φ (w.getVert n) := by
        rw [← hsupget! m (by omega), ← hsupget! n (by omega)]
        rw [← map_getElem! φ (by omega), ← map_getElem! φ (by omega)]
        rw [hmval, hnval]
      exact hinj _ hmS _ hnS hφ
    have hsplen2 : w.support.length = w.length + 1 :=
      SimpleGraph.Walk.length_support w
    have hND2 := (List.nodup_iff_getElem?_ne_getElem?).mp hcy.support_nodup
    have hne := hND2 (m - 1) (n - 1) (by omega)
      (by rw [List.length_tail]; omega)
    have hm? : w.support.tail[m - 1]? = some (sup[m]!) := by
      rw [tail_getElem?, show m - 1 + 1 = m from by omega, hsupget! m (by omega)]
      exact (w.getVert_eq_support_getElem? (by omega)).symm
    have hn? : w.support.tail[n - 1]? = some (sup[n]!) := by
      rw [tail_getElem?, show n - 1 + 1 = n from by omega, hsupget! n (by omega)]
      exact (w.getVert_eq_support_getElem? (by omega)).symm
    rw [hm?, hn?, hsupget! m (by omega), hsupget! n (by omega), hpointeq] at hne
    exact absurd rfl hne
'''

import io
import re

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()
start = s.index('private lemma get!_of?')
end = s.index('/-- **F2.**')
assert start < end
assert not re.search(r'\b(sorry|admit)\b', HEAD)
s = s[:start] + HEAD + '\n' + s[end:]
io.open(p, 'w', encoding='utf-8').write(s)
print('rewrote helpers + criterion (v5)')
