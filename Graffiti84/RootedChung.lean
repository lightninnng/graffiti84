import Graffiti84.BasicFacts

/-!
# RootedChung

The rooted Chung lemma (Lemma 2.1 of `docs/full-proof.md`): if deleting the
non-cut vertex `a` lowers the radius by exactly one, the graph contains an
induced path on at least `2r - 1` vertices **containing `a`**.

Batch A: distance infrastructure along geodesics.
-/

namespace Graffiti84

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- On a geodesic walk, every prefix position realizes the distance:
`d(u, getVert i) = i` for `i ≤ length`. -/
theorem dist_getVert_of_length_eq_dist {G : SimpleGraph α}
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v)
    (i : ℕ) (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have hup : (p.take i).length = i := by
    rw [SimpleGraph.Walk.take_length]
    exact Nat.min_eq_left hi
  have hle : G.dist u (p.getVert i) ≤ i := by
    have h := SimpleGraph.dist_le (p.take i)
    rw [hup] at h
    exact h
  rcases Nat.eq_or_lt_of_le hle with h | h
  · exact h
  · exfalso
    have hreach : G.Reachable u (p.getVert i) := (p.take i).reachable
    obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
    have hdroplen : (p.drop i).length = p.length - i :=
      SimpleGraph.Walk.drop_length p i
    have hsplit_len : (q.append (p.drop i)).length
        = q.length + (p.length - i) := by
      rw [SimpleGraph.Walk.length_append, hdroplen]
    have hshort : (q.append (p.drop i)).length < p.length := by
      rw [hsplit_len, hq]
      omega
    have hd := SimpleGraph.dist_le (q.append (p.drop i))
    rw [← hp] at hd
    omega

/-- On a geodesic walk, every suffix position realizes the distance:
`d(getVert i, v) = length - i` for `i ≤ length`. -/
theorem dist_getVert_end_of_length_eq_dist {G : SimpleGraph α}
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v)
    (i : ℕ) (hi : i ≤ p.length) :
    G.dist (p.getVert i) v = p.length - i := by
  have hdroplen : (p.drop i).length = p.length - i :=
    SimpleGraph.Walk.drop_length p i
  have hle : G.dist (p.getVert i) v ≤ p.length - i := by
    have h := SimpleGraph.dist_le (p.drop i)
    rw [hdroplen] at h
    exact h
  rcases Nat.eq_or_lt_of_le hle with h | h
  · exact h
  · exfalso
    have hreach : G.Reachable (p.getVert i) v := (p.drop i).reachable
    obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
    have hup : (p.take i).length = i := by
      rw [SimpleGraph.Walk.take_length]
      exact Nat.min_eq_left hi
    have hsplit_len : ((p.take i).append q).length
        = i + q.length := by
      rw [SimpleGraph.Walk.length_append, hup]
    have hshort : ((p.take i).append q).length < p.length := by
      rw [hsplit_len, hq]
      omega
    have hd := SimpleGraph.dist_le ((p.take i).append q)
    rw [← hp] at hd
    omega

/-- Vertices at distinct positions of a geodesic are distinct. -/
theorem getVert_ne_of_length_eq_dist {G : SimpleGraph α}
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i ≠ j) :
    p.getVert i ≠ p.getVert j := by
  intro heq
  have h1 := dist_getVert_of_length_eq_dist hp i hi
  have h2 := dist_getVert_of_length_eq_dist hp j hj
  rw [← heq] at h2
  exact hij (h1.symm.trans h2)



/-- **Chung context.** If deleting `a` lowers the radius by exactly one
(ambient bookkeeping) and `r >= 2`, there are a centre `v0` of the deletion,
a geodesic `p : v0 -a` of length `r`, its second vertex `v2`, and a vertex
`w` maximizing the distance from `v2`, together with a geodesic
`q : v0 -w` of length at most `r - 1`. -/
theorem chung_context {G : SimpleGraph α} (hconn : G.Connected) {a : α}
    (hr2 : 2 ≤ G.radius.toNat)
    (hdrop : radOn G (Finset.univ.erase a) + 1 ≤ G.radius) :
    ∃ (v₀ v₂ w : α) (p : G.Walk v₀ a) (q : G.Walk v₀ w),
      p.length = G.dist v₀ a ∧
      G.dist v₀ a = G.radius.toNat ∧
      p.getVert 2 = v₂ ∧
      G.dist v₂ a + 2 = G.radius.toNat ∧
      q.length = G.dist v₀ w ∧
      G.dist v₀ w + 1 ≤ G.radius.toNat ∧
      G.radius.toNat ≤ G.dist v₂ w := by
  haveI : Nonempty α := hconn.nonempty
  -- the graph is nontrivial
  haveI : Nontrivial α := by
    by_contra hnt
    have hsub : Subsingleton α := not_nontrivial_iff_subsingleton.mp hnt
    have hzero : ∀ u : α, G.eccent u = 0 := fun u =>
      G.eccent_eq_zero_of_subsingleton u
    have hr0 : G.radius = 0 := by
      have hle : G.radius ≤ G.eccent a := SimpleGraph.radius_le_eccent
      rw [hzero a] at hle
      exact le_antisymm hle bot_le
    have : G.radius.toNat = 0 := by rw [hr0]; rfl
    omega
  obtain ⟨x, hxa⟩ := exists_ne a
  have hex : (Finset.univ.erase a).Nonempty :=
    ⟨x, Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩⟩
  obtain ⟨v₀, hv₀mem, hcmin⟩ := eccOn_eq_radOn_attained hex
  set ρ := radOn G (Finset.univ.erase a) with hρdef
  have hedρ : ∀ y ∈ Finset.univ.erase a, G.edist v₀ y ≤ ρ := fun y hy =>
    (edist_le_eccOn (G := G) (S := Finset.univ.erase a) (c := v₀) hy).trans
      hcmin.le
  -- a has a neighbour
  haveI : Inhabited α := ⟨a⟩
  obtain ⟨nb, hnb⟩ : ∃ y, G.Adj a y := by
    obtain ⟨y, hy⟩ := exists_ne a
    have hne : G.edist a y ≠ ⊤ :=
      SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected a y)
    have hcoe : ((G.edist a y).toNat : ℕ∞) = G.edist a y := ENat.coe_toNat hne
    obtain ⟨qq, hqq⟩ := SimpleGraph.exists_walk_of_edist_eq_coe
      (k := (G.edist a y).toNat) hcoe.symm
    cases qq with
    | nil => exact absurd rfl hy
    | cons h _ => exact ⟨_, h⟩
  have hnbne : nb ≠ a := (G.ne_of_adj hnb).symm
  have hnbedge : G.edist nb a ≤ 1 := by
    have hh := SimpleGraph.edist_le (SimpleGraph.Adj.toWalk hnb.symm : G.Walk nb a)
    simp [SimpleGraph.Adj.toWalk] at hh
    exact hh
  have hnbρ : G.edist v₀ nb ≤ ρ := hedρ nb
    (Finset.mem_erase.mpr ⟨hnbne, Finset.mem_univ nb⟩)
  have hrne : G.radius ≠ ⊤ := by
    obtain ⟨c, y, hcy⟩ := G.exists_edist_eq_radius_of_finite
    rw [← hcy]
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c y)
  have hρtop : ρ ≠ ⊤ := by
    intro h
    rw [h] at hdrop
    exact absurd hdrop (by simp [hrne])
  -- coe bridges
  have hrc : ((G.radius.toNat : ℕ) : ℕ∞) = G.radius := ENat.coe_toNat hrne
  have hρc : ((ρ.toNat : ℕ) : ℕ∞) = ρ := ENat.coe_toNat hρtop
  -- radius = rho + 1
  have hradius : G.radius = ρ + 1 := by
    refine le_antisymm ?_ hdrop
    refine le_trans (SimpleGraph.radius_le_eccent (u := v₀)) ?_
    refine (SimpleGraph.eccent_le_iff v₀ (ρ + 1)).mpr ?_
    intro y
    by_cases hy : y = a
    · rw [hy]
      calc G.edist v₀ a ≤ G.edist v₀ nb + G.edist nb a :=
            SimpleGraph.edist_triangle
        _ ≤ ρ + 1 := add_le_add hnbρ hnbedge
    · exact le_trans (hedρ y (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩))
        le_self_add
  -- d(v0, a) = radius
  have hedva : G.edist v₀ a = G.radius := by
    refine le_antisymm ?_ ?_
    · calc G.edist v₀ a ≤ G.edist v₀ nb + G.edist nb a :=
            SimpleGraph.edist_triangle
      _ ≤ ρ + 1 := add_le_add hnbρ hnbedge
      _ = G.radius := hradius.symm
    · by_contra hcon
      push_neg at hcon
      have heccρ : G.eccent v₀ ≤ ρ := by
        refine (SimpleGraph.eccent_le_iff v₀ ρ).mpr ?_
        intro y
        by_cases hy : y = a
        · rw [hy]
          have h' : G.edist v₀ a < ρ + 1 := by rw [← hradius]; exact hcon
          exact (ENat.lt_add_one_iff hρtop).mp h'
        · exact hedρ y (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩)
      have hle : G.radius ≤ ρ :=
        le_trans (SimpleGraph.radius_le_eccent (u := v₀)) heccρ
      rw [hradius] at hle
      exact absurd ((ENat.add_one_le_iff hρtop).mp hle) (lt_irrefl ρ)
  have hdva : G.dist v₀ a = G.radius.toNat := by
    have hc : ((G.dist v₀ a : ℕ) : ℕ∞) = G.edist v₀ a :=
      (hconn.preconnected v₀ a).coe_dist_eq_edist
    rw [hedva, ← hrc] at hc
    exact ENat.coe_inj.mp hc
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v₀ a
  have hplen : p.length = G.radius.toNat := by rw [hp, hdva]
  set v₂ := p.getVert 2 with hv₂def
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite v₂
  have hdv₂a : G.dist v₂ a + 2 = G.radius.toNat := by
    have hpre := dist_getVert_end_of_length_eq_dist hp 2 (by omega)
    rw [← hv₂def] at hpre
    omega
  have hwne : w ≠ a := by
    intro h
    rw [h] at hw
    have hc2 : ((G.dist v₂ a : ℕ) : ℕ∞) = G.edist v₂ a :=
      (hconn.preconnected v₂ a).coe_dist_eq_edist
    have hlt : G.edist v₂ a < G.radius := by
      rw [← hc2, ← hrc]
      exact ENat.coe_lt_coe.mpr (by omega)
    have hge : G.radius ≤ G.edist v₂ a := by
      refine le_trans (SimpleGraph.radius_le_eccent (u := v₂)) ?_
      rw [hw]
    exact absurd hge (not_le.mpr hlt)
  have hdvw : G.dist v₀ w + 1 ≤ G.radius.toNat := by
    have hc3 : ((G.dist v₀ w : ℕ) : ℕ∞) = G.edist v₀ w :=
      (hconn.preconnected v₀ w).coe_dist_eq_edist
    have hle3 : G.edist v₀ w ≤ ρ := hedρ w
      (Finset.mem_erase.mpr ⟨hwne, Finset.mem_univ w⟩)
    have hpt : ρ.toNat + 1 = G.radius.toNat := by
      apply ENat.coe_inj.mp
      calc ((ρ.toNat + 1 : ℕ) : ℕ∞) = (ρ.toNat : ℕ∞) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
        _ = ρ + 1 := by rw [hρc]
        _ = G.radius := hradius.symm
        _ = ((G.radius.toNat : ℕ) : ℕ∞) := hrc.symm
    have hcoele : (G.dist v₀ w : ℕ∞) ≤ (ρ.toNat : ℕ∞) := by
      rw [hc3, hρc]
      exact hle3
    have : G.dist v₀ w ≤ ρ.toNat := ENat.coe_le_coe.mp hcoele
    omega
  have hdv₂w : G.radius.toNat ≤ G.dist v₂ w := by
    have hc4 : ((G.dist v₂ w : ℕ) : ℕ∞) = G.edist v₂ w :=
      (hconn.preconnected v₂ w).coe_dist_eq_edist
    have hge : G.radius ≤ G.edist v₂ w := by
      refine le_trans (SimpleGraph.radius_le_eccent (u := v₂)) ?_
      rw [hw]
    rw [← hrc] at hge
    rw [← hc4] at hge
    exact ENat.coe_le_coe.mp hge
  obtain ⟨q, hq⟩ := (hconn.preconnected v₀ w).exists_walk_length_eq_dist
  exact ⟨v₀, v₂, w, p, q, hp, hdva, hv₂def, hdv₂a, hq, hdvw, hdv₂w⟩



/-- On a geodesic, the distance between two positions is their separation:
for `i <= j <= length`, `d(getVert i, getVert j) = j - i`. -/
theorem dist_getVert_pair_le {G : SimpleGraph α} (hconn : G.Connected)
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
  have hstart : (p.take j).getVert i = p.getVert i := by
    rw [SimpleGraph.Walk.take_getVert, Nat.min_eq_right hij]
  have hseg : ((p.take j).drop i).length = j - i := by
    rw [SimpleGraph.Walk.drop_length, htakej]
  have hle : G.dist (p.getVert i) (p.getVert j) ≤ j - i := by
    have h := SimpleGraph.dist_le ((p.take j).drop i)
    rw [hseg, hstart] at h
    exact h
  rcases Nat.eq_or_lt_of_le hle with h | h
  · exact h
  · exfalso
    have ht1 := hconn.dist_triangle (u := u) (v := p.getVert i) (w := v)
    have ht2 := hconn.dist_triangle (u := p.getVert i) (v := p.getVert j)
      (w := v)
    rw [dist_getVert_of_length_eq_dist hp i hi] at ht1
    rw [dist_getVert_end_of_length_eq_dist hp i hi,
      dist_getVert_end_of_length_eq_dist hp j hj] at ht2
    omega

/-- **Chung chords.** Given the Chung context, all cross-chords between the
two geodesics are excluded, the exceptional chord `v1 - p1` forces
`m = r - 1`, and the two supports overlap only at `v0`. -/
theorem chung_chords {G : SimpleGraph α} (hconn : G.Connected) {a : α}
    (hr2 : 2 ≤ G.radius.toNat)
    (hdrop : radOn G (Finset.univ.erase a) + 1 ≤ G.radius) :
    ∃ (v₀ v₂ w : α) (p : G.Walk v₀ a) (q : G.Walk v₀ w),
      p.length = G.radius.toNat ∧ G.dist v₀ a = G.radius.toNat ∧
      q.length + 1 ≤ p.length ∧ 2 ≤ p.length ∧
      p.getVert 2 = v₂ ∧ p.length ≤ G.dist v₂ w ∧
      (∀ i j, i ≤ q.length → j ≤ p.length → 2 ≤ j →
        ¬ G.Adj (q.getVert i) (p.getVert j)) ∧
      (∀ i, 2 ≤ i → i ≤ q.length → ¬ G.Adj (p.getVert 1) (q.getVert i)) ∧
      (1 ≤ q.length → G.Adj (p.getVert 1) (q.getVert 1) →
        q.length + 1 = p.length) ∧
      (∀ i j, 1 ≤ i → i ≤ p.length → 1 ≤ j → j ≤ q.length →
        p.getVert i = q.getVert j → False) := by
  obtain ⟨v₀, v₂, w, p, q, hp, hdva, hv₂, hdv₂a, hq, hdvw, hdv₂w⟩ :=
    chung_context hconn hr2 hdrop
  have hed1 : ∀ x y : α, G.Adj x y → G.dist x y ≤ 1 := fun x y hh => by
    have h' := SimpleGraph.dist_le (SimpleGraph.Adj.toWalk hh)
    simpa [SimpleGraph.Adj.toWalk] using h'
  have h12 : G.dist (p.getVert 2) (p.getVert 1) = 1 := by
    rw [SimpleGraph.dist_comm]
    exact dist_getVert_pair_le hconn hp 1 2 (by omega) (by omega)
  have hdv₂w' : G.radius.toNat ≤ G.dist (p.getVert 2) w := by
    rw [hv₂]
    exact hdv₂w
  haveI : Nonempty α := hconn.nonempty
  have hmle : q.length + 1 ≤ G.radius.toNat := by rw [hq]; exact hdvw
  have hrle : G.radius.toNat ≤ p.length := (hp.trans hdva).symm.le
  refine ⟨v₀, v₂, w, p, q, hp.trans hdva, hdva, ?_, ?_, hv₂,
    (hp.trans hdva).le.trans hdv₂w, ?_, ?_, ?_, ?_⟩
  · exact by rw [hq, hp, hdva]; exact hdvw
  · exact le_trans hr2 hrle
  · -- (7a): no q_i - v_j chord for j >= 2
    intro i j him hjr h2j hadj
    have hchain : G.radius.toNat ≤ (j - 2) + (1 + (q.length - i)) := by
      calc G.radius.toNat ≤ G.dist (p.getVert 2) w := hdv₂w'
        _ ≤ G.dist (p.getVert 2) (p.getVert j) + G.dist (p.getVert j) w :=
            hconn.dist_triangle (u := p.getVert 2) (v := p.getVert j)
              (w := w)
        _ = (j - 2) + G.dist (p.getVert j) w := by
            simp only [dist_getVert_pair_le hconn hp 2 j (by omega) hjr]
        _ ≤ (j - 2) + (G.dist (p.getVert j) (q.getVert i)
              + G.dist (q.getVert i) w) := by
            exact add_le_add le_rfl
              (hconn.dist_triangle (u := p.getVert j) (v := q.getVert i)
                (w := w))
        _ ≤ (j - 2) + (1 + (q.length - i)) := by
            have h1 := hed1 (p.getVert j) (q.getVert i) hadj.symm
            have h2 := dist_getVert_end_of_length_eq_dist hq i him
            omega
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
    have hchain : G.radius.toNat ≤ 1 + (1 + (q.length - i)) := by
      calc G.radius.toNat ≤ G.dist (p.getVert 2) w := hdv₂w'
        _ ≤ G.dist (p.getVert 2) (p.getVert 1) + G.dist (p.getVert 1) w :=
            hconn.dist_triangle (u := p.getVert 2) (v := p.getVert 1)
              (w := w)
        _ ≤ 1 + (G.dist (p.getVert 1) (q.getVert i)
              + G.dist (q.getVert i) w) := by
            exact add_le_add h12.le
              (hconn.dist_triangle (u := p.getVert 1) (v := q.getVert i)
                (w := w))
        _ ≤ 1 + (1 + (q.length - i)) := by
            have h1 := hed1 (p.getVert 1) (q.getVert i) hadj
            have h2 := dist_getVert_end_of_length_eq_dist hq i him
            omega
    omega
  · -- (7c): the chord v1 - p1 forces m = r - 1 (m >= 1 assumed: for
    -- m = 0 the vertex q.getVert 1 is junk and the "chord" is vacuous)
    intro h1m hadj
    have hchain : G.radius.toNat ≤ 1 + (1 + (q.length - 1)) := by
      calc G.radius.toNat ≤ G.dist (p.getVert 2) w := hdv₂w'
        _ ≤ G.dist (p.getVert 2) (p.getVert 1) + G.dist (p.getVert 1) w :=
            hconn.dist_triangle (u := p.getVert 2) (v := p.getVert 1)
              (w := w)
        _ ≤ 1 + (G.dist (p.getVert 1) (q.getVert 1)
              + G.dist (q.getVert 1) w) := by
            exact add_le_add h12.le
              (hconn.dist_triangle (u := p.getVert 1) (v := q.getVert 1)
                (w := w))
        _ ≤ 1 + (1 + (q.length - 1)) := by
            have h1 := hed1 (p.getVert 1) (q.getVert 1) hadj
            have h2 := dist_getVert_end_of_length_eq_dist hq 1 (by omega)
            omega
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
          _ ≤ 1 + G.dist (q.getVert 1) w := by
              have h0 := hconn.dist_triangle (u := p.getVert 2)
                (v := p.getVert 1) (w := w)
              rw [h12] at h0
              rw [heq] at h0
              exact h0
          _ = 1 + (q.length - 1) := by
              rw [dist_getVert_end_of_length_eq_dist hq 1 (by omega)]
      omega
    · -- i >= 2
      have hchain : G.radius.toNat ≤ (i - 2) + (q.length - i) := by
        calc G.radius.toNat ≤ G.dist (p.getVert 2) w := hdv₂w'
          _ ≤ G.dist (p.getVert 2) (p.getVert i) + G.dist (p.getVert i) w :=
              hconn.dist_triangle (u := p.getVert 2) (v := p.getVert i)
                (w := w)
          _ = (i - 2) + G.dist (p.getVert i) w := by
              simp only [dist_getVert_pair_le hconn hp 2 i (by omega) hir]
          _ = (i - 2) + G.dist (q.getVert i) w := by rw [heq]
          _ = (i - 2) + (q.length - i) := by
              rw [dist_getVert_end_of_length_eq_dist hq i hjm]
      omega


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
    haveI : Inhabited α := ⟨x⟩
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
      · right; omega
      · left; omega


private lemma idxOf_reverse_mem {β : Type*} [BEq β] [LawfulBEq β] :
    ∀ (l : List β), l.Nodup → ∀ (x : β), x ∈ l →
      List.idxOf x l.reverse + List.idxOf x l = l.length - 1 := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons h r ih =>
      intro hnd x hx
      obtain ⟨hnhr, hnr⟩ := List.nodup_cons.mp hnd
      by_cases hxe : x = h
      · subst hxe
        rw [List.reverse_cons,
          List.idxOf_append_of_notMem (fun hc => hnhr (by
            simpa using hc)),
          List.idxOf_cons_self, List.idxOf_cons_self,
          List.length_reverse, List.length_cons]
        omega
      · have hxr : x ∈ r := by
          by_contra hc
          rw [List.mem_cons] at hx
          rcases hx with h1 | h2
          · exact hxe h1
          · exact hc h2
        have hrec := ih hnr x hxr
        have hxrev : x ∈ r.reverse := by
          rw [List.mem_reverse]; exact hxr
        rw [List.reverse_cons,
          List.idxOf_append_of_mem hxrev,
          List.idxOf_cons_ne r (fun e => hxe e.symm)]
        simp only [List.length_cons, List.length_reverse]
        omega

end Graffiti84
