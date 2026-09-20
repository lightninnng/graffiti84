import Graffiti84.RootedChung

/-!
# EndBlocks

Case B tools: `F10` (every finite connected graph on at least two vertices
has two distinct non-cut vertices, via a longest path) and `F12` (radius
`≥ 2` forces at least four vertices).
-/

namespace Graffiti84

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### List helpers -/

/-- On a duplicate-free list, the index of a value is determined by any
position at which it sits. -/
private lemma idxOf_eq_of_getElem' {β : Type*} [DecidableEq β] {l : List β}
    (hnd : l.Nodup) {a : β} {j : ℕ} (hj : j < l.length) (hv : l[j] = a) :
    l.idxOf a = j := by
  have hmem : a ∈ l := hv ▸ List.getElem_mem hj
  have hlt := List.idxOf_lt_length_of_mem hmem
  have hge : l[l.idxOf a]'hlt = a := List.getElem_idxOf hlt
  exact (hnd.getElem_inj_iff).mp (hge.trans hv.symm)

/-- Membership in a prefix of a duplicate-free list is equivalent to the
index bound, provided the prefix does not run past the list. -/
private lemma mem_take_iff_idxOf_lt' {β : Type*} [DecidableEq β] {l : List β}
    (hnd : l.Nodup) {a : β} (hmem : a ∈ l) {n : ℕ} (hn : n ≤ l.length) :
    a ∈ l.take n ↔ l.idxOf a < n := by
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · obtain ⟨j, hj, heq⟩ := List.mem_take_iff_getElem.mp hc
    have hjl : j < l.length := by omega
    rw [idxOf_eq_of_getElem' hnd hjl heq]
    omega
  · have hlt := List.idxOf_lt_length_of_mem hmem
    have hv : l[l.idxOf a]'hlt = a := List.getElem_idxOf hlt
    refine List.mem_take_iff_getElem.mpr ⟨l.idxOf a, ?_, hv⟩
    rw [Nat.min_eq_left hn]
    exact hc

private lemma nodup_take' {β : Type*} [DecidableEq β] :
    ∀ (n : ℕ) (l : List β), l.Nodup → (l.take n).Nodup := by
  intro n l h
  induction l generalizing n with
  | nil => rw [List.take_nil]; exact List.nodup_nil
  | cons a t ih =>
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp h
    cases n with
    | zero => simp
    | succ m =>
      refine List.nodup_cons.mpr ⟨fun hc => h1 (List.mem_of_mem_take hc), ?_⟩
      exact ih m h2

/-- Vertices of a path at distinct positions are distinct. -/
private theorem getVert_inj_of_isPath {G : SimpleGraph α} {u v : α}
    {p : G.Walk u v} (hp : p.IsPath) {i j : ℕ} (hi : i ≤ p.length)
    (hj : j ≤ p.length) (hij : p.getVert i = p.getVert j) : i = j := by
  have hpn : p.support.Nodup := hp.support_nodup
  have hli : i < p.support.length := by
    rw [SimpleGraph.Walk.length_support]; omega
  have hlj : j < p.support.length := by
    rw [SimpleGraph.Walk.length_support]; omega
  have hii : p.getVert i = p.support[i] :=
    SimpleGraph.Walk.getVert_eq_support_getElem p hi
  have hjj : p.getVert j = p.support[j] :=
    SimpleGraph.Walk.getVert_eq_support_getElem p hj
  refine (List.getElem_inj (h₀ := hli) (h₁ := hlj) hpn).mp ?_
  rw [← hii, ← hjj]
  exact hij

private theorem dist_self' {G : SimpleGraph α} (hconn : G.Connected) (c : α) :
    G.dist c c = 0 := by
  have hle : G.dist c c ≤ SimpleGraph.Walk.nil.length :=
    SimpleGraph.dist_le SimpleGraph.Walk.nil
  rw [SimpleGraph.Walk.length_nil] at hle
  exact le_antisymm hle (Nat.zero_le _)

/-! ### F10 -/

/-- The neighbours of the start of a longest path all lie on the path:
otherwise the walk through the new neighbour would be a longer path. -/
private lemma mem_support_of_longest {G : SimpleGraph α} {u v : α}
    {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (x y : α) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    {y : α} (hy : G.Adj y u) : y ∈ p.support := by
  by_contra hys
  have hpn : p.support.Nodup := hp.support_nodup
  have hyu : y ≠ u := G.ne_of_adj hy
  have hpath : ((SimpleGraph.Adj.toWalk hy).append p).IsPath := by
    refine SimpleGraph.Walk.IsPath.mk' ?_
    rw [SimpleGraph.Walk.support_append]
    have he1 : (SimpleGraph.Adj.toWalk hy).support = [y, u] := by
      simp [SimpleGraph.Adj.toWalk]
    rw [he1]
    refine List.nodup_append.mpr ⟨by simp [hyu], hpn.tail, ?_⟩
    intro x hx1 b hb
    rcases List.mem_cons.mp hx1 with e | e
    · intro heq
      have hbt : x ∈ p.support.tail := heq ▸ hb
      have hxps : x ∈ p.support := List.mem_of_mem_tail hbt
      rw [e] at hxps
      exact hys hxps
    · have hxu : x = u := List.mem_singleton.mp e
      intro heq
      have hbu : b = u := heq.symm.trans hxu
      rw [hbu] at hb
      have hu0 : p.support.idxOf u = 0 := by
        have hxg : p.getVert (p.support.idxOf u) = p.getVert 0 :=
          (SimpleGraph.Walk.getVert_support_idxOf p
            p.start_mem_support).trans (SimpleGraph.Walk.getVert_zero p).symm
        exact getVert_inj_of_isPath hp
          (by have hpsl := SimpleGraph.Walk.length_support p
              have := List.idxOf_lt_length_of_mem p.start_mem_support
              omega)
          (Nat.zero_le _) hxg
      have hts := idxOf_tail_succ p.support hpn u hb
      omega
  have hlen : ((SimpleGraph.Adj.toWalk hy).append p).length = p.length + 1 := by
    rw [SimpleGraph.Walk.length_append]
    have h1 : (SimpleGraph.Adj.toWalk hy).length = 1 := rfl
    omega
  exact absurd (hmax _ _ _ hpath) (by omega)

/-- **F10, endpoint half.** Along a longest path, every other vertex reaches
the path's second vertex by a walk avoiding the start, so the start is not
a cut vertex. -/
private theorem deleteConnected_of_longest {G : SimpleGraph α}
    (hconn : G.Connected) {u v : α} {p : G.Walk u v} (hp : p.IsPath)
    (h1 : 1 ≤ p.length)
    (hmax : ∀ (x y : α) (q : G.Walk x y), q.IsPath → q.length ≤ p.length) :
    DeleteConnected G u := by
  have hpn : p.support.Nodup := hp.support_nodup
  have hpsl : p.support.length = p.length + 1 :=
    SimpleGraph.Walk.length_support p
  -- every z ≠ u reaches the second vertex of `p` by a walk avoiding u
  have reach : ∀ z : α, z ≠ u → ∃ w : G.Walk z (p.getVert 1), u ∉ w.support := by
    intro z hzu
    obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist z u
    have hqpath : q.IsPath := isPath_of_length_eq_dist hconn hq
    have hqn : q.support.Nodup := hqpath.support_nodup
    have hql : q.support.length = q.length + 1 :=
      SimpleGraph.Walk.length_support q
    set m := q.length with hm
    have hm1 : 1 ≤ m := by
      by_contra h0
      cases q with
      | nil => exact hzu rfl
      | cons h t =>
        rw [SimpleGraph.Walk.length_cons] at hm
        omega
    -- the penultimate vertex of `q` lies on `p`
    have hvL : q.getVert q.length = u := SimpleGraph.Walk.getVert_length q
    rw [← hm] at hvL
    have hxmne : q.getVert (m - 1) ≠ u := by
      intro e
      have hin := getVert_inj_of_isPath hqpath (by omega) (le_of_eq rfl)
        (e.trans hvL.symm)
      omega
    have hxm : q.getVert (m - 1) ∈ p.support := by
      have hadjm : G.Adj (q.getVert (m - 1)) (q.getVert (m - 1 + 1)) :=
        SimpleGraph.Walk.adj_getVert_succ q (i := m - 1) (by rw [hm]; omega)
      have hm1 : m - 1 + 1 = m := by omega
      rw [hm1, hvL] at hadjm
      exact mem_support_of_longest hp hmax hadjm
    set i := p.support.idxOf (q.getVert (m - 1)) with hi
    have hgx : p.getVert i = q.getVert (m - 1) :=
      SimpleGraph.Walk.getVert_support_idxOf p hxm
    have hi1 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h0 | h2
      · rw [h0, SimpleGraph.Walk.getVert_zero] at hgx
        exact absurd hgx.symm hxmne
      · exact h2
    -- prefix of the geodesic: z to the penultimate vertex, avoiding u
    have hQsup : (q.take (m - 1)).support = q.support.take m := by
      rw [SimpleGraph.Walk.support_take]
      congr 1
      omega
    have hQu : u ∉ (q.take (m - 1)).support := by
      intro hc
      rw [hQsup, List.mem_take_iff_getElem] at hc
      obtain ⟨j, hj, heq⟩ := hc
      have hjl : j < q.support.length := by
        have h2 := hql
        omega
      have hju : q.support.idxOf u = j :=
        idxOf_eq_of_getElem' hqn hjl heq
      have hjm : j = m := by
        have hux : q.getVert (q.support.idxOf u) = q.getVert m :=
          (SimpleGraph.Walk.getVert_support_idxOf q
            (SimpleGraph.Walk.end_mem_support q)).trans
            (by rw [hm]; exact (SimpleGraph.Walk.getVert_length q).symm)
        rw [hju] at hux
        have hb1 : q.support.idxOf u ≤ q.length := by
          have hlt := List.idxOf_lt_length_of_mem
            (SimpleGraph.Walk.end_mem_support q)
          rw [hql] at hlt
          omega
        exact getVert_inj_of_isPath hqpath (by omega) (le_of_eq hm) hux
      omega
    -- backward segment of `p` from position i down to position 1, avoiding u
    set W := (p.take i).reverse with hW
    have hWsup : W.support = (p.support.take (i + 1)).reverse := by
      rw [hW, SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_take]
    have hTnd : (p.support.take (i + 1)).Nodup := nodup_take' _ _ hpn
    have hib : i + 1 ≤ p.support.length := by
      have := List.idxOf_lt_length_of_mem hxm
      omega
    have hTlen : (p.support.take (i + 1)).length = i + 1 := by
      rw [List.length_take]
      omega
    have hv1p : p.support.idxOf (p.getVert 1) = 1 := by
      have hxg : p.getVert (p.support.idxOf (p.getVert 1)) = p.getVert 1 :=
        SimpleGraph.Walk.getVert_support_idxOf p
          (SimpleGraph.Walk.getVert_mem_support p 1)
      exact getVert_inj_of_isPath hp
        (by have := List.idxOf_lt_length_of_mem
              (SimpleGraph.Walk.getVert_mem_support p 1)
            omega)
        h1 hxg
    have hv1T : (p.support.take (i + 1)).idxOf (p.getVert 1) = 1 := by
      refine idxOf_eq_of_getElem' hTnd (by omega) ?_
      rw [List.getElem_take]
      exact (SimpleGraph.Walk.getVert_eq_support_getElem p (by omega)).symm
    have huT : u ∈ p.support.take (i + 1) := by
      rw [mem_take_iff_idxOf_lt' hpn (SimpleGraph.Walk.start_mem_support p)
        hib]
      have hxg : p.getVert (p.support.idxOf u) = p.getVert 0 :=
        (SimpleGraph.Walk.getVert_support_idxOf p
          p.start_mem_support).trans (SimpleGraph.Walk.getVert_zero p).symm
      have hinj := getVert_inj_of_isPath hp
        (by have := List.idxOf_lt_length_of_mem p.start_mem_support; omega)
        (Nat.zero_le _) hxg
      omega
    have hv₂T : p.getVert 1 ∈ p.support.take (i + 1) := by
      rw [mem_take_iff_idxOf_lt' hpn
        (SimpleGraph.Walk.getVert_mem_support p 1) hib]
      omega
    have hv₂W : p.getVert 1 ∈ W.support := by
      rw [hWsup, List.mem_reverse]
      exact hv₂T
    have hWT : u ∉ (W.takeUntil (p.getVert 1) hv₂W).support := by
      intro hc
      have hsup := SimpleGraph.Walk.takeUntil_eq_take W hv₂W
      have hcp : ((W.take (W.support.idxOf (p.getVert 1))).copy rfl
        (SimpleGraph.Walk.getVert_support_idxOf W hv₂W)).support
          = W.support.take (W.support.idxOf (p.getVert 1) + 1) := by
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_take]
      rw [hsup, hcp, List.mem_take_iff_getElem] at hc
      obtain ⟨j, hj, heq⟩ := hc
      have hWL : W.support.length = i + 1 := by
        rw [hWsup, List.length_reverse, hTlen]
      have hWnd : W.support.Nodup := by
        rw [hWsup]
        exact List.nodup_reverse.mpr hTnd
      have huW' : W.support.idxOf u = i := by
        rw [hWsup]
        have hrev := idxOf_reverse_mem (p.support.take (i + 1)) hTnd u huT
        have hu0T : (p.support.take (i + 1)).idxOf u = 0 := by
          refine idxOf_eq_of_getElem' hTnd (by omega) ?_
          rw [List.getElem_take]
          have hge : p.support[0] = p.getVert 0 :=
            (SimpleGraph.Walk.getVert_eq_support_getElem p
              (Nat.zero_le _)).symm
          rw [hge, SimpleGraph.Walk.getVert_zero]
        rw [hu0T, hTlen] at hrev
        omega
      have hv₂W' : W.support.idxOf (p.getVert 1) = i - 1 := by
        rw [hWsup]
        have hrev := idxOf_reverse_mem (p.support.take (i + 1)) hTnd
          (p.getVert 1) hv₂T
        rw [hv1T, hTlen] at hrev
        omega
      have hjl : j < W.support.length := by
        rw [hWL]
        rw [hv₂W'] at hj
        omega
      have hju : W.support.idxOf u = j :=
        idxOf_eq_of_getElem' (l := W.support) hWnd hjl heq
      subst hju
      rw [huW', hv₂W'] at hj
      omega
    have hWTc : u ∉ ((W.takeUntil (p.getVert 1) hv₂W).copy hgx rfl).support := by
      rw [SimpleGraph.Walk.support_copy]
      exact hWT
    refine ⟨(q.take (m - 1)).append
      ((W.takeUntil (p.getVert 1) hv₂W).copy hgx rfl), ?_⟩
    intro hu
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hu
    rcases hu with h | h
    · exact hQu h
    · exact hWTc (List.mem_of_mem_tail h)
  intro X Y hX hY
  obtain ⟨w₁, h₁⟩ := reach X hX
  obtain ⟨w₂, h₂⟩ := reach Y hY
  refine ⟨w₁.append w₂.reverse, ?_⟩
  intro hu
  rw [SimpleGraph.Walk.support_append, List.mem_append] at hu
  rcases hu with h | h
  · exact h₁ h
  · rw [SimpleGraph.Walk.support_reverse] at h
    exact h₂ (List.mem_reverse.mp (List.mem_of_mem_tail h))

/-- **F10.** Every finite connected graph on at least two vertices has two
distinct non-cut vertices. -/
theorem exists_two_deleteConnected {G : SimpleGraph α} (hconn : G.Connected)
    [Nontrivial α] :
    ∃ x y : α, x ≠ y ∧ DeleteConnected G x ∧ DeleteConnected G y := by
  classical
  -- a longest path: paths are bounded by the vertex count, so the least
  -- uniform bound is attained
  have htop : ∀ (x y : α) (q : G.Walk x y), q.IsPath →
      q.length ≤ Fintype.card α := fun _ _ q hq => le_of_lt hq.length_lt
  have hex : ∃ n, ∀ (x y : α) (q : G.Walk x y), q.IsPath →
      q.length ≤ n := ⟨Fintype.card α, htop⟩
  have hn0spec : ∀ (x y : α) (q : G.Walk x y), q.IsPath →
      q.length ≤ Nat.find hex :=
    Nat.find_spec (p := fun n : ℕ => ∀ (x y : α) (q : G.Walk x y),
      q.IsPath → q.length ≤ n) hex
  have hn1 : 1 ≤ Nat.find hex := by
    by_contra h0
    have h0' : Nat.find hex = 0 := by omega
    have a0 : α := Classical.arbitrary (α := α)
    obtain ⟨x, hxy⟩ := exists_ne a0
    obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist x a0
    have hqp : q.IsPath := isPath_of_length_eq_dist hconn hq
    refine hxy ?_
    have hle := hn0spec x a0 q hqp
    rw [hq, h0'] at hle
    have hdeq : G.dist x a0 = 0 := by omega
    obtain ⟨t, ht⟩ := hconn.exists_walk_length_eq_dist x a0
    rw [hdeq] at ht
    cases t with
    | nil => rfl
    | cons h t' => rw [SimpleGraph.Walk.length_cons] at ht; omega
  have hnmin : ¬ (∀ (x y : α) (q : G.Walk x y), q.IsPath →
      q.length ≤ Nat.find hex - 1) := by
    have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    have h2 := @Nat.find_min (fun n : ℕ => ∀ (x y : α) (q : G.Walk x y),
        q.IsPath → q.length ≤ n) _ hex (Nat.find hex - 1) hlt
    exact h2
  obtain ⟨u, v, p, hpp, hplen⟩ : ∃ (x y : α) (q : G.Walk x y), q.IsPath ∧
      q.length = Nat.find hex := by
    by_contra hcon
    push_neg at hcon
    have hnm : ∀ (x y : α) (q : G.Walk x y), q.IsPath →
        q.length ≤ Nat.find hex - 1 := by
      intro x y q hq
      have hle := hn0spec x y q hq
      have hne := hcon x y q hq
      omega
    exact absurd hnm hnmin
  have hp1 : 1 ≤ p.length := by rw [hplen]; exact hn1
  have huv : u ≠ v := by
    intro e
    subst e
    exact (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hp1).elim
      ((SimpleGraph.Walk.IsPath.nil_iff_eq hpp).mpr rfl)
  have hmax : ∀ (x y : α) (q : G.Walk x y), q.IsPath → q.length ≤ p.length :=
    fun x y q hq => by rw [hplen]; exact hn0spec x y q hq
  refine ⟨u, v, huv,
    deleteConnected_of_longest hconn hpp hp1 hmax,
    deleteConnected_of_longest hconn hpp.reverse
      (by rw [SimpleGraph.Walk.length_reverse]; exact hp1)
      (fun x y q hq => by
        rw [SimpleGraph.Walk.length_reverse]
        exact hmax x y q hq)⟩

/-! ### F12 -/

/-- **F12.** A connected graph of radius at least two has at least four
vertices. -/
theorem four_le_card_of_radius_ge_two {G : SimpleGraph α} (hconn : G.Connected)
    [Nonempty α] (hr : 2 ≤ G.radius.toNat) : 4 ≤ Fintype.card α := by
  by_contra hc
  push_neg at hc
  -- a vertex of eccentricity ≤ 1 exists, forcing radius ≤ 1
  have hrad : ∃ c : α, G.eccent c ≤ 1 := by
    rcases Nat.lt_or_ge (Fintype.card α) 2 with h1 | h2
    · have c : α := Classical.arbitrary (α := α)
      refine ⟨c, ?_⟩
      haveI hsub : Subsingleton α :=
        Fintype.card_le_one_iff_subsingleton.mp (by omega)
      rw [G.eccent_eq_zero_of_subsingleton c]
      exact ENat.coe_le_coe.mpr (Nat.zero_le 1)
    · by_cases hdiam : ∀ w : α, ∀ z : α, G.dist w z ≤ 1
      · have c0 : α := Classical.arbitrary (α := α)
        refine ⟨c0, (SimpleGraph.eccent_le_iff c0 1).mpr ?_⟩
        intro z
        have hco : ((G.dist c0 z : ℕ) : ℕ∞) = G.edist c0 z :=
          (hconn.preconnected c0 z).coe_dist_eq_edist
        rw [← hco]
        exact ENat.coe_le_coe.mpr (hdiam c0 z)
      · push_neg at hdiam
        obtain ⟨w, x, hx⟩ := hdiam
        have hx2' : 2 ≤ G.dist w x := by omega
        obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist w x
        have hq2 : 2 ≤ q.length := by rw [← hq] at hx2'; exact hx2'
        set c := q.getVert 1 with hcdef
        have hw0 : q.getVert 0 = w := SimpleGraph.Walk.getVert_zero q
        have hcwx : c ≠ w := by
          have hne := getVert_ne_of_length_eq_dist hq (i := 0) (j := 1)
            (Nat.zero_le _) (by omega) (by omega)
          rw [hw0, ← hcdef] at hne
          exact hne.symm
        have hcx : c ≠ x := by
          have hne := getVert_ne_of_length_eq_dist hq (i := 1)
            (j := q.length) (by omega) (le_of_eq rfl) (by omega)
          rw [← hcdef, SimpleGraph.Walk.getVert_length] at hne
          exact hne
        have haw : G.Adj w c := by
          have ha : G.Adj (q.getVert 0) (q.getVert 1) :=
            SimpleGraph.Walk.adj_getVert_succ q (by omega)
          rw [hw0, ← hcdef] at ha
          exact ha
        -- every vertex equals w, x, or c (four distinct points would force
        -- the cardinality to be at least four)
        have hcover : ∀ z : α, z = w ∨ z = x ∨ z = c := by
          intro z
          by_contra hz
          push_neg at hz
          have hcard4 : 4 ≤ Fintype.card α := by
            have hsub := Finset.card_le_card (s := ({z, c, x, w} : Finset α))
              (Finset.subset_univ _)
            have hwxn : w ≠ x := by
              intro e
              rw [e, dist_self' hconn x] at hx2'
              omega
            have hzc : z ≠ c := hz.2.2
            have h1 : z ∉ ({c, x, w} : Finset α) := by
              intro hw1
              rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hw1
              rcases hw1 with e | e | e
              · exact hzc e
              · exact hz.2.1 e
              · exact hz.1 e
            have h2 : c ∉ ({x, w} : Finset α) := by
              intro hc2
              rw [Finset.mem_insert, Finset.mem_singleton] at hc2
              rcases hc2 with e | e
              · exact hcx e
              · exact hcwx e
            have h3 : x ∉ ({w} : Finset α) := by
              intro hx3
              rw [Finset.mem_singleton] at hx3
              exact hwxn hx3.symm
            rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
              Finset.card_insert_of_notMem h3, Finset.card_singleton] at hsub
            have huncard : Finset.univ.card = Fintype.card α := rfl
            omega
          omega
        refine ⟨c, (SimpleGraph.eccent_le_iff c 1).mpr ?_⟩
        intro z
        have hco : ((G.dist c z : ℕ) : ℕ∞) = G.edist c z :=
          (hconn.preconnected c z).coe_dist_eq_edist
        rw [← hco]
        refine ENat.coe_le_coe.mpr ?_
        rcases hcover z with e | e
        · have h1 : G.dist c w ≤ 1 := by
            have hle := SimpleGraph.dist_le
              (SimpleGraph.Adj.toWalk haw.symm : G.Walk c w)
            simpa [SimpleGraph.Adj.toWalk] using hle
          rw [e]; omega
        · rcases e with e | e
          · have h1 : G.dist c x = q.length - 1 := by
              have hge := dist_getVert_end_of_length_eq_dist hq
                (i := 1) (by omega)
              rw [hcdef]
              exact hge
            have hL2 : q.length ≤ 2 := by
              obtain ⟨q', hq'⟩ := hconn.exists_walk_length_eq_dist w x
              have hqp' : q'.IsPath := isPath_of_length_eq_dist hconn hq'
              have hlt := hqp'.length_lt
              omega
            rw [e]
            omega
          · rw [e, dist_self' hconn c]
            exact Nat.zero_le _
  obtain ⟨c, hc1⟩ := hrad
  have hne : G.radius ≠ ⊤ := by
    obtain ⟨a, b, hab⟩ := G.exists_edist_eq_radius_of_finite
    rw [← hab]
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected a b)
  have hle : (G.radius.toNat : ℕ∞) ≤ 1 := by
    have hcoe : ((G.radius.toNat : ℕ) : ℕ∞) = G.radius := ENat.coe_toNat hne
    calc (G.radius.toNat : ℕ∞) = G.radius := hcoe
      _ ≤ G.eccent c := G.radius_le_eccent
      _ ≤ 1 := hc1
  have hfin : G.radius.toNat ≤ 1 := ENat.coe_le_coe.mp hle
  omega


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
  have hxvne : x ≠ v := G.ne_of_adj hxv
  have h1 := huep.1
  -- (a) the distance statement
  have htr : G.dist c v ≤ G.dist c x + 1 := by
    have h2 := hconn.dist_triangle (u := c) (v := x) (w := v)
    have hx1 : G.dist x v ≤ 1 := dist_le_one_of_adj hxv
    omega
  have hlt := huep.2 x hxvne
  have hda : G.dist c x + 1 = (G.eccent c).toNat := by omega
  refine ⟨hda, ?_⟩
  -- (b) x is not a cut vertex
  -- a second neighbour y of v with y ≠ x
  obtain ⟨y, hyv, hyx⟩ : ∃ y, G.Adj y v ∧ y ≠ x := by
    by_contra hcon
    push_neg at hcon
    have hsub : G.neighborFinset v ⊆ {x} := by
      intro z hz
      have hz2 := hcon z (SimpleGraph.Adj.symm (G.mem_neighborFinset v z |>.mp hz))
      rw [hz2]
      exact Finset.mem_singleton.mpr rfl
    have h1' : G.degree v ≤ 1 := by
      have hcard : (G.neighborFinset v).card ≤ ({x} : Finset α).card :=
        Finset.card_le_card hsub
      have hsingle : ({x} : Finset α).card = 1 := rfl
      show (G.neighborFinset v).card ≤ 1
      omega
    omega
  have hyne : y ≠ v := G.ne_of_adj hyv
  -- x ≠ c: otherwise the second neighbour y would violate the UEP bounds
  have hxc : x ≠ c := by
    intro e
    have hyc : c ≠ y := fun hcy => hyx (by rw [← hcy, e])
    have hv1 : G.dist c v ≤ 1 := by
      rw [← e]
      exact dist_le_one_of_adj hxv
    have hdy1 : 1 ≤ G.dist c y := one_le_dist_of_ne hconn hyc
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
        rw [← hc1, ← hc2, ht] at hle
        have hle2 : G.dist y x + G.dist x c ≤ G.dist y c :=
          ENat.coe_le_coe.mp hle
        have hdyx : 1 ≤ G.dist y x := one_le_dist_of_ne hconn hyx
        have hdxc : 1 ≤ G.dist x c := one_le_dist_of_ne hconn hxc
        have hsym : G.dist y c = G.dist c y := SimpleGraph.dist_comm
        have hsc2 : G.dist x c = G.dist c x := SimpleGraph.dist_comm
        have hlt2 := huep.2 y hyne
        omega
      refine ⟨(SimpleGraph.Adj.toWalk (SimpleGraph.Adj.symm hyv)).append t, ?_⟩
      intro hc
      rw [SimpleGraph.Walk.support_append, SimpleGraph.Adj.toWalk] at hc
      simp only [List.mem_append, List.mem_cons, List.mem_singleton] at hc
      rcases hc with hc2 | hc2
      · rcases List.mem_cons.mp hc2 with e | e
        · exact hxvne e
        · exact hyx (List.mem_singleton.mp e).symm
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
        rw [← hc1, ← hc2, ht] at hle
        have hle2 : G.dist z x + G.dist x c ≤ G.dist z c :=
          ENat.coe_le_coe.mp hle
        have hdzx : 1 ≤ G.dist z x := one_le_dist_of_ne hconn
          (fun e => hz e)
        have hdxc : 1 ≤ G.dist x c := one_le_dist_of_ne hconn hxc
        have hsc2 : G.dist x c = G.dist c x := SimpleGraph.dist_comm
        have hsym2 : G.dist z c = G.dist c z := SimpleGraph.dist_comm
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


/-! ### 3.5: the closure argument (Fajtlowicz) -/

/-- In a closed vertex set, every walk starting inside ends inside. -/
private theorem walk_end_mem_of_closed {G : SimpleGraph α} {S : Finset α}
    (hS : ∀ u z, u ∈ S → G.Adj u z → z ∈ S) {a b : α} :
    G.Walk a b → a ∈ S → b ∈ S := by
  intro p
  induction p with
  | nil => intro ha; exact ha
  | @cons u v w h t ih =>
      intro ha
      exact ih (hS u v ha h)

/-- **3.5 (Fajtlowicz).** In a vrd graph with a cut vertex, every non-cut
vertex is a leaf. -/
theorem degree_eq_one_of_nonCut_of_hasCut {G : SimpleGraph α}
    (hconn : G.Connected) [Nonempty α] [Nontrivial α]
    (hmono : ∀ z : α, DeleteConnected G z →
      radOn G (Finset.univ.erase z) + 1 ≤ radOn G Finset.univ)
    (hac : ∃ a, IsCut G a) {v : α} (hv : DeleteConnected G v) :
    G.degree v = 1 := by
  classical
  by_contra hdeg
  have hdeg0 : G.degree v ≠ 0 := by
    intro h0
    -- v has a neighbour (a walk of positive length to another vertex)
    obtain ⟨z, hzv⟩ := exists_ne v
    have hdist : 1 ≤ G.dist v z := one_le_dist_of_ne hconn (Ne.symm hzv)
    obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist v z
    cases w with
    | nil =>
        rw [SimpleGraph.Walk.length_nil] at hw
        omega
    | cons h t' =>
        have hpos : 0 < G.degree v := G.degree_pos_iff_exists_adj v |>.mpr ⟨_, h⟩
        omega
  have hdeg2 : 2 ≤ G.degree v := by
    rcases Nat.lt_or_ge (G.degree v) 2 with h | h
    · omega
    · exact h
  -- W := the non-cut vertices
  set W : Finset α := Finset.univ.filter (fun z => DeleteConnected G z)
    with hWdef
  have hWmem : ∀ z, z ∈ W ↔ DeleteConnected G z := by
    intro z
    rw [hWdef]
    simp [Finset.mem_filter, Finset.mem_univ]
  -- S := the W-component of v
  set S : Finset α := Finset.univ.filter
    (fun z => z ∈ W ∧ ConnectsWithin G W v z) with hSdef
  have hSiff : ∀ z, z ∈ S ↔ z ∈ W ∧ ConnectsWithin G W v z := by
    intro z
    rw [hSdef]
    simp [Finset.mem_filter, Finset.mem_univ]
  have hstep : ∀ z ∈ S, ∀ b, G.Adj b z → b ∈ S := by
    intro u hu b hbu
    obtain ⟨huW, hcu⟩ := (hSiff u).mp hu
    by_cases hleaf : G.degree u = 1
    · -- u is a leaf: b is its unique neighbour, the penultimate vertex of
      -- the witnessing v -> u walk
      have huv : u ≠ v := by
        intro e
        rw [e] at hleaf
        omega
      obtain ⟨p, hp⟩ := hcu
      have hpne : ¬p.Nil := by
        cases p with
        | nil => exact fun hnil => huv rfl
        | cons h t => exact SimpleGraph.Walk.not_nil_cons
      have hpen := SimpleGraph.Walk.adj_penultimate hpne
      have hpenW : p.penultimate ∈ W := by
        rw [SimpleGraph.Walk.penultimate]
        exact hp (p.getVert (p.length - 1))
          (SimpleGraph.Walk.getVert_mem_support p (p.length - 1))
      have hbpen : b = p.penultimate :=
        (adj_eq_of_degree_eq_one hleaf (SimpleGraph.Adj.symm hpen)
          (SimpleGraph.Adj.symm hbu)).symm
      refine (hSiff b).mpr ⟨?_, ?_⟩
      · rw [hbpen]
        exact hpenW
      · refine ⟨p.append (SimpleGraph.Adj.toWalk (SimpleGraph.Adj.symm hbu)),
          ?_⟩
        intro t ht
        rw [SimpleGraph.Walk.support_append, List.mem_append] at ht
        rcases ht with h | h
        · exact hp t h
        · rcases List.mem_cons.mp (List.mem_of_mem_tail h) with e | e
          · rw [e]
            exact huW
          · have htb : t = b := List.mem_singleton.mp e
            rw [htb, hbpen]
            exact hpenW
    · -- deg u ≥ 2: F8 gives a UEP centre, and 3.2 makes b a non-cut vertex
      have hncu : DeleteConnected G u := hWmem u |>.mp huW
      have hdeg2u : 2 ≤ G.degree u := by
        rcases Nat.lt_or_ge (G.degree u) 2 with hlt | hge
        · have hne1 : G.degree u ≠ 1 := hleaf
          have hne0 : G.degree u ≠ 0 := by
            intro h0
            obtain ⟨z, hzu⟩ := exists_ne u
            have hdist : 1 ≤ G.dist u z :=
              one_le_dist_of_ne hconn (Ne.symm hzu)
            obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist u z
            cases w with
            | nil =>
                rw [SimpleGraph.Walk.length_nil] at hw
                omega
            | cons h t' =>
                have hpos : 0 < G.degree u :=
                  G.degree_pos_iff_exists_adj u |>.mpr ⟨_, h⟩
                omega
          omega
        · exact hge
      have h2 : 2 ≤ Fintype.card α := by
        by_contra h
        push_neg at h
        haveI : Subsingleton α :=
          Fintype.card_le_one_iff_subsingleton.mp (by omega)
        obtain ⟨z, hzv⟩ := exists_ne (Classical.arbitrary (α := α))
        exact hzv (Subsingleton.elim z (Classical.arbitrary (α := α)))
      obtain ⟨c_u, hcen, huepu⟩ := isUniqueEccentricPoint_of_radOn_erase
        hconn h2 (hmono u hncu)
      have hbnc : DeleteConnected G b :=
        (deleteConnected_of_isUniqueEccentricPoint_neighbor hconn huepu
          hdeg2u hbu).2
      refine (hSiff b).mpr ⟨hWmem b |>.mpr hbnc, ?_⟩
      obtain ⟨p, hp⟩ := hcu
      refine ⟨p.append (SimpleGraph.Adj.toWalk (SimpleGraph.Adj.symm hbu)),
        ?_⟩
      intro t ht
      rw [SimpleGraph.Walk.support_append, List.mem_append] at ht
      rcases ht with h | h
      · exact hp t h
      · rcases List.mem_cons.mp (List.mem_of_mem_tail h) with e | e
        · rw [e]
          exact huW
        · have htb : t = b := List.mem_singleton.mp e
          rw [htb]
          exact hWmem b |>.mpr hbnc
  have hvS : v ∈ S := (hSiff v).mpr
    ⟨hWmem v |>.mpr hv, ⟨SimpleGraph.Walk.nil, by
      intro t ht
      rcases List.mem_cons.mp ht with e | e
      · rw [e]
        exact hWmem v |>.mpr hv
      · exact absurd e (by simp)⟩⟩
  have hclosed : ∀ (u : α), u ∈ S → ∀ (z : α), G.Adj u z → z ∈ S :=
    fun u hu z huz => hstep u hu z (SimpleGraph.Adj.symm huz)
  -- the cut vertex a is neither in W nor in S
  obtain ⟨a, ha⟩ := hac
  have haW : a ∉ W := fun hm => ha ((hWmem a).mp hm)
  have haS : a ∉ S := fun hs => haW ((hSiff a).mp hs).1
  obtain ⟨b, hbS⟩ : ∃ b, b ∉ S := ⟨a, haS⟩
  obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist v b
  have hclosedPi : ∀ (u z : α), u ∈ S → G.Adj u z → z ∈ S := by
    intro u z hu h
    exact hstep u hu z (SimpleGraph.Adj.symm h)
  exact hbS (walk_end_mem_of_closed hclosedPi w hvS)

/-- **3.5b(i).** In a vrd graph with a cut vertex there are two distinct
leaves. -/
theorem exists_two_isLeaf_of_hasCut {G : SimpleGraph α} (hconn : G.Connected)
    [Nonempty α] [Nontrivial α]
    (hmono : ∀ z : α, DeleteConnected G z →
      radOn G (Finset.univ.erase z) + 1 ≤ radOn G Finset.univ)
    (hac : ∃ a, IsCut G a) :
    ∃ x y : α, x ≠ y ∧ G.degree x = 1 ∧ G.degree y = 1 := by
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_two_deleteConnected hconn
  refine ⟨x, y, hxy, ?_, ?_⟩
  · exact degree_eq_one_of_nonCut_of_hasCut hconn hmono hac hx
  · exact degree_eq_one_of_nonCut_of_hasCut hconn hmono hac hy



/-! ### 3.6b: a vertex has at most one leaf neighbour -/

/-- A leaf's only edge is the last one of any walk ending there: the
penultimate vertex of a walk to a leaf is its unique neighbour. -/
private theorem penultimate_eq_of_leaf_end {G : SimpleGraph α} {b u : α}
    (hu : G.degree u = 1) (hub : G.Adj u b) {c : α} (p : G.Walk c u)
    (hpne : ¬ p.Nil) : p.penultimate = b :=
  adj_eq_of_degree_eq_one hu (SimpleGraph.Adj.symm
    (SimpleGraph.Walk.adj_penultimate hpne)) hub

/-- The distance from `c` to a leaf `u` exceeds the distance from `c` to
its neighbour by at least one. -/
private theorem dist_leaf_ge {G : SimpleGraph α} (hconn : G.Connected)
    {b u : α} (hu : G.degree u = 1) (hub : G.Adj u b) {c : α} (hcu : c ≠ u) :
    G.dist c b + 1 ≤ G.dist c u := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist c u
  have hpne : ¬p.Nil := by
    intro hnil
    exact hcu hnil.eq
  have hsu : G.dist c u = p.length := hp.symm
  have hpen : p.penultimate = b :=
    penultimate_eq_of_leaf_end hu hub p hpne
  have hlen : p.dropLast.length = p.length - 1 :=
    SimpleGraph.Walk.length_dropLast p
  have hdrop : G.dist c p.penultimate ≤ p.dropLast.length :=
    SimpleGraph.dist_le (p.dropLast)
  have hbeq : G.dist c b = G.dist c p.penultimate := by rw [hpen]
  have h := SimpleGraph.dist_le (p.dropLast)
  rw [hlen] at h
  omega

/-- **3.6b.** In a vrd graph with `r ≥ 2`, no vertex is adjacent to two
distinct leaves. -/
theorem unique_leaf_neighbor {G : SimpleGraph α} (hconn : G.Connected)
    (hmono : ∀ z : α, DeleteConnected G z →
      radOn G (Finset.univ.erase z) + 1 ≤ radOn G Finset.univ)
    (hr2 : 2 ≤ G.radius.toNat) {b u u' : α}
    (hu : G.degree u = 1) (hub : G.Adj u b)
    (hu' : G.degree u' = 1) (hu'b : G.Adj u' b) : u = u' := by
  by_contra hne
  have hne' : u ≠ u' := hne
  -- deleting a leaf never disconnects the remaining vertices
  have hncu : DeleteConnected G u := by
    intro X Y hX hY
    obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist X Y
    by_cases hum : u ∈ w.support
    · -- decompose at u and splice through the unique leaf edge, skipping u
      obtain ⟨q, r, hqr⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_append.mp hum
      have hqne : ¬q.Nil := fun hnil => hX hnil.eq
      have hrne : ¬r.Nil := fun hnil => hY hnil.eq.symm
      -- r = cons hedge rt (match-pattern); the leaf forces the vertex
      -- after u to be b
      obtain ⟨t2, hedge, rt, hrcons⟩ :=
        SimpleGraph.Walk.exists_eq_cons_of_ne (G := G)
        (u := u) (v := Y) (Ne.symm hY) r
      have hbu : G.Adj u b := hub
      have hrb : t2 = b :=
        adj_eq_of_degree_eq_one hu hedge hbu
      -- splice: q.dropLast (X -> b) ++ rt (b -> Y); both pieces avoid u.
      -- Need q.penultimate = b: it is the leaf property of q's endpoint u.
      have hqpen : q.penultimate = b :=
        penultimate_eq_of_leaf_end hu hub q hqne
      have hpend : q.penultimate = t2 := hqpen.trans hrb.symm
      refine ⟨((q.dropLast).copy rfl hpend).append rt, ?_⟩
      intro hmem
      rw [SimpleGraph.Walk.support_append, List.mem_append,
        SimpleGraph.Walk.support_copy] at hmem
      rcases hmem with h1 | h2
      · -- u ∈ dropLast.support of q, i.e. at a non-final slot of q.support
        rw [SimpleGraph.Walk.support_dropLast hqne] at h1
        have hzu : u ∈ q.support.dropLast := h1
        -- u is q's terminal vertex; the geodesic path property forbids it
        have hpath : w.IsPath := isPath_of_length_eq_dist hconn hw
        have hwn : w.support.Nodup := hpath.support_nodup
        have hqnd : q.support.Nodup := by
          rw [hqr]
          exact hwn.of_append_left
        have huin : u ∈ q.support := by
          rw [SimpleGraph.Walk.support_dropLast hqne] at h1
          exact List.mem_of_mem_dropLast h1
        have hidx1 : q.support.idxOf u = q.support.length - 1 := by
          have hmemL : u ∈ q.support := huin
          have hlt := List.idxOf_lt_length_of_mem hmemL
          have hv := List.getElem_idxOf hmemL
          have hj : q.support[q.support.length - 1] = u := by
            cases q with
            | nil => exact absurd (by simp) hqne
            | cons h' t' =>
                rw [← SimpleGraph.Walk.support_cons] at *
                simp
          have hqnd' := hqnd
          have hkey := (hqnd'.getElem_inj_iff).mp (hj.symm.trans hv)
          rw [hkey] at hlt
          omega
        rw [List.mem_dropLast_iff_idxOf_lt huin] at h1
        omega
      · -- u ∈ rt.support would put u twice in r's support (head + here),
        -- contradicting the geodesic's nodup
        have hrnd : r.support.Nodup := by
          rw [hqr]
          exact hwn.of_append_right
        have hrs : r.support = u :: rt.support := by
          rw [hrcons]
          simp [SimpleGraph.Walk.support_cons]
        have hin : u ∈ r.support := by
          rw [hrs]
          exact List.mem_cons_self .. |>.resolve_right h2
        exact hrnd hin
        have hrs : r.support = hedge.to_target :: rt.support := by
          simp [hrcons, SimpleGraph.Walk.support_cons]
        rw [hrs] at hrnd
        have hmem2 : u ∈ rt.support := h2
        have hhead : u = hedge.to_target := by
          cases rt with
          | nil => exact absurd (by simp : (nil : G.Walk t2 Y).support = []) hrt
          | cons h2' t2' => exact rfl
        exact hrnd (by
          rcases List.mem_cons.mp (by rw [hrs] at *; exact hsub) with e | e
          · rw [hhead] at e; exact e
          · exact e)
      rw [SimpleGraph.Walk.support_append, List.mem_append] at hz
      rcases hz with h1 | h2
      · -- z ∈ q.dropLast.support ⊆ q.support, and z ≠ u
        have hsub : z ∈ q.support := by
          rw [SimpleGraph.Walk.support_dropLast hqne] at h1
          exact List.mem_of_mem_dropLast h1
        have hzw : z ∈ w.support := by
          rw [hqr, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inl hsub
        refine ⟨hzw, ?_⟩
        intro hzu
        -- w is a geodesic, hence a path; u occupies exactly one slot in
        -- q.support (its last element), so it cannot sit in the dropLast
        have hpath : w.IsPath := isPath_of_length_eq_dist hconn hw
        have hwn : w.support.Nodup := hpath.support_nodup
        have hqnd : q.support.Nodup := by
          have hsub' : q.support <+: w.support := by
            rw [hqr, SimpleGraph.Walk.mem_support_append_iff]
            exact List.sublist_append_left _ _
          exact List.Nodup.sublist hsub' hwn
        -- q's support ends with u (q is a walk ending at u)
        have huin : u ∈ q.support := by
          have hdl2 := SimpleGraph.Walk.support_dropLast hqne
          rw [hdl2] at h1
          exact List.mem_of_mem_dropLast h1
        -- last element of q.support is u
        have hlast : q.support.getLastD u = u := by
          cases q with
          | nil => exact absurd (by simp) hqne
          | cons h' t' =>
              rw [← SimpleGraph.Walk.support_cons]
              simp
        have hnd := hqnd
        -- nodup + last = u forces idxOf u = length - 1
        have hidx1 : q.support.idxOf u = q.support.length - 1 := by
          have hmemL : u ∈ q.support := huin
          have hlt := List.idxOf_lt_length_of_mem hmemL
          have hv := List.getElem_idxOf hmemL
          have hj : q.support[q.support.length - 1] = u := by
            cases q with
            | nil => exact absurd (by simp) hqne
            | cons h' t' =>
                rw [← SimpleGraph.Walk.support_cons] at *
                simp
          have := (hnd.getElem_inj_iff).mp (hj.symm.trans hv)
          rw [this] at *
          omega
        have hdl2 := SimpleGraph.Walk.support_dropLast hqne
        rw [hdl2, List.mem_dropLast_iff_idxOf_lt huin] at h1
        omega
      · -- z ∈ rt.support: u is only r's head, not in rt.support
        have hts : rt.support = (SimpleGraph.Walk.cons hedge rt).support.tail := by
          simp [SimpleGraph.Walk.support_cons]
        have hsub : z ∈ (SimpleGraph.Walk.cons hedge rt).support := by
          rw [hts] at h2
          exact List.mem_of_mem_tail h2
        have hzw : z ∈ w.support := by
          rw [hqr, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hsub
        refine ⟨hzw, ?_⟩
        intro hzu
        rw [hzu] at h2
        rw [hts] at h2
        simp [List.mem_cons] at h2
        exact h2 hzu
    · exact ⟨w, hum⟩
  have h2 : 2 ≤ Fintype.card α := by
    have hne' : u ∉ ({u'} : Finset α) := by simp [hne]
    have h1 : ({u, u'} : Finset α).card = 2 := by
      rw [Finset.card_insert_of_notMem hne', Finset.card_singleton]
    have hsub := Finset.card_le_card (s := ({u, u'} : Finset α))
      (Finset.subset_univ _)
    have huncard : Finset.univ.card = Fintype.card α := rfl
    omega
  obtain ⟨c_u, hcen, huepu⟩ := isUniqueEccentricPoint_of_radOn_erase
    hconn h2 (hmono u hncu)
  -- d(c_u, b) = r - 1 and d(c_u, u) = r
  have hdcu : G.dist c_u u = (G.eccent c_u).toNat := huepu.1
  have hdcb : G.dist c_u b + 1 = (G.eccent c_u).toNat := by
    have h1 : G.dist c_u u ≤ G.dist c_u b + 1 := by
      have htr := hconn.dist_triangle (u := c_u) (v := b) (w := u)
      have hb1 : G.dist b u ≤ 1 :=
        dist_le_one_of_adj (SimpleGraph.Adj.symm hub)
      omega
    omega
  -- ecc(c_u) = d(c_u, u) = r ≥ 2
  have hlt2 : 2 ≤ (G.eccent c_u).toNat := by omega
  -- u' also sits at distance ≥ (r-1)+1 from c_u: any c_u-u' walk ends
  -- with the unique leaf edge b-u'
  have hb'u : b ≠ u' := by
    intro e
    rw [e] at hub
    exact hne' (adj_eq_of_degree_eq_one hu' hub (SimpleGraph.Adj.symm hu'b))
  have hb'u2 : u' ≠ b := Ne.symm hb'u
  have hcne : c_u ≠ u' := by
    intro e
    rw [e] at hdcb ⊢
    have hb1 : G.dist b u' ≤ 1 := dist_le_one_of_adj hub'
    have h0 : G.dist u' u' = 0 := dist_self' hconn u'
    have htr := hconn.dist_triangle (u := u') (v := b) (w := u')
    omega
  have hdu' : G.dist c_u b + 1 ≤ G.dist c_u u' :=
    dist_leaf_ge hconn hu' hu'b hcne
  -- final counting: dist c_u b + 1 = ecc, yet dist c_u u' < ecc (UEP) —
  -- contradiction
  have hlt := huepu.2 u' hne'
  omega

end Graffiti84
