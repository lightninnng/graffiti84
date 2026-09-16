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
        exact getVert_inj_of_isPath hp (List.idxOf_lt_length_of_mem
          p.start_mem_support) (Nat.zero_le _) hxg
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
    · refine ⟨Classical.arbitrary (α := α), ?_⟩
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
          have hne := getVert_ne_of_length_eq_dist hq (Nat.zero_le _) hq2
            (by omega)
          rw [hw0] at hne
          exact hne.symm
        have hcx : c ≠ x :=
          getVert_ne_of_length_eq_dist hq (by omega) (Nat.zero_le _) (by omega)
        have haw : G.Adj w c := by
          have ha := SimpleGraph.Walk.adj_getVert_succ q (by omega)
          rw [hw0] at ha
          rw [hcdef] at ha
          exact ha
        -- every vertex equals w, x, or c (four distinct points would force
        -- the cardinality to be at least four)
        have hcover : ∀ z : α, z = w ∨ z = x ∨ z = c := by
          intro z
          by_contra hz
          push_neg at hz
          have hcard4 : 4 ≤ Fintype.card α := by
            have hsub := Finset.card_le_card (s := ({w, x, c, z} : Finset α))
              (Finset.subset_univ _)
            have hwxn : w ≠ x := by
              intro e
              rw [e, dist_self' hconn x] at hx2'
              omega
            have h1 : z ∉ ({w, x, c} : Finset α) := by
              simp only [Finset.mem_insert, Finset.mem_insert,
                Finset.mem_singleton, not_or, hz.1, hz.2.1, hz.2.2]
            have h2 : c ∉ ({w, x} : Finset α) := by simp [hcwx, hcx]
            have h3 : x ∉ ({w} : Finset α) := by simp [hwxn]
            rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
              Finset.card_singleton] at hsub
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
              rw [hcdef]
              exact dist_getVert_end_of_length_eq_dist hq (by omega)
            rw [e, ← hq] at h1
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
    calc (G.radius.toNat : ℕ∞) = G.radius := hcoe.symm
      _ ≤ G.eccent c := G.radius_le_eccent
      _ ≤ 1 := hc1
  have hfin : G.radius.toNat ≤ 1 := ENat.coe_le_coe.mp hle
  omega

end Graffiti84
