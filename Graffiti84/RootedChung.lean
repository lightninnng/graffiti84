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
      q.length = G.dist v₀ w ∧
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
  refine ⟨v₀, v₂, w, p, q, hp.trans hdva, hdva, hq, ?_, ?_, hv₂,
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
          List.idxOf_cons_ne r (fun e => hxe e.symm),
          Nat.succ_eq_add_one]
        have hL : 1 ≤ r.length := List.length_pos_of_mem hxr
        have key := hrec
        simp only [List.length_cons] at key ⊢
        omega


private lemma idxOf_tail_succ {β : Type*} [BEq β] [LawfulBEq β] :
    ∀ (l : List β), l.Nodup → ∀ (x : β), x ∈ l.tail →
      List.idxOf x l.tail + 1 = List.idxOf x l := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons h r ih =>
      intro hnd x hx
      obtain ⟨hnhr, hnr⟩ := List.nodup_cons.mp hnd
      have hne : x ≠ h := by
        intro e
        rw [e] at hx
        exact hnhr (by simpa using hx)
      have hstep : List.idxOf x (h :: r) = (List.idxOf x r) + 1 :=
        List.idxOf_cons_ne r (fun e => hne e.symm)
      rw [hstep]
      rfl


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
      have hne := getVert_ne_of_length_eq_dist hq hjle (Nat.zero_le q.length)
        (by omega)
      rw [SimpleGraph.Walk.getVert_zero] at hne
      exact hne (hxgq.trans hxg.symm)
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
    have hv₂₀ : G.dist v₂ v₀ = 2 := by
      rw [← hv₂, SimpleGraph.dist_comm]
      exact dist_getVert_of_length_eq_dist hpgeo 2 h2
    have ht := hconn.dist_triangle (u := v₂) (v := v₀) (w := w)
    rw [hv₂₀, ← hq] at ht
    have horder : r ≤ 2 + q.length := by
      calc r = p.length := hp.symm
        _ ≤ G.dist v₂ w := hpw
        _ ≤ 2 + q.length := ht
    omega


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
  have hv₁ : p.snd = p.getVert 1 := by
    rw [SimpleGraph.Walk.snd_eq_support_getElem_one hpnn,
      SimpleGraph.Walk.getVert_eq_support_getElem p (by omega)]
  have hq1 : q.snd = q.getVert 1 := by
    rw [SimpleGraph.Walk.snd_eq_support_getElem_one hqnn,
      SimpleGraph.Walk.getVert_eq_support_getElem q (by omega)]
  have hadj' : G.Adj p.snd q.snd := by rw [hv₁, hq1]; exact hadj
  have hElen : (SimpleGraph.Adj.toWalk hadj').length = 1 := by
    simp [SimpleGraph.Adj.toWalk]
  set R := (p.tail.reverse.append (SimpleGraph.Adj.toWalk hadj')).append q.tail
    with hRdef
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
      have hne := getVert_ne_of_length_eq_dist hpgeo hile (Nat.zero_le p.length)
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
  have hq1ninTT : ¬ (q.getVert 1 ∈ q.support.tail.tail) := by
    intro hc
    have h1 := idxOf_tail_succ q.support.tail hqN.tail (q.getVert 1) hc
    have h2 := idxOf_tail_succ q.support hqN (q.getVert 1)
      (List.mem_of_mem_tail hc)
    omega
  have hQge : ∀ x ∈ q.getVert 1 :: q.support.tail.tail,
      1 ≤ q.support.idxOf x := by
    intro x hx
    rcases List.mem_cons.mp hx with e | hx3
    · rw [e]; omega
    · have h2t := idxOf_tail_succ q.support.tail hqN.tail x hx3
      have h2c := idxOf_tail_succ q.support hqN x (List.mem_of_mem_tail hx3)
      omega
  -- index positions in the spliced support
  have hPpos : ∀ x ∈ p.support.tail,
      R.support.idxOf x = r - p.support.idxOf x := by
    intro x hx
    have hxr : x ∈ p.support.tail.reverse := List.mem_reverse.mpr hx
    rw [hsupR, List.idxOf_append_of_mem hxr]
    have h1 := idxOf_reverse_mem p.support.tail hpN.tail x hx
    have h2b := idxOf_tail_succ p.support hpN x hx
    have h4 : p.support.tail.length = r := by
      rw [List.length_tail, hplen]
      omega
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
      omega
    rcases List.mem_cons.mp hx with e | hx3
    · subst e
      rw [List.idxOf_cons_self]
      omega
    · have hne : ¬ (q.getVert 1 = x) := fun ec => hq1ninTT (ec ▸ hx3)
      rw [List.idxOf_cons_ne _ hne]
      have h2t := idxOf_tail_succ q.support.tail hqN.tail x hx3
      have h2c := idxOf_tail_succ q.support hqN x (List.mem_of_mem_tail hx3)
      omega
  have hdisj2 : List.Disjoint p.support.tail.reverse
      (q.getVert 1 :: q.support.tail.tail) := by
    intro x hx1 hx2
    exact hcore2 x (List.mem_reverse.mp hx1) (hQmem x hx2)
  have hLnd : R.support.Nodup := by
    rw [hsupR]
    exact (List.nodup_reverse.mpr hpN.tail).append
      (List.nodup_cons.mpr ⟨hq1ninTT, hqN.tail.tail⟩) hdisj2
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
      have hge := hQge v hv2
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
      have hpge : 1 ≤ p.support.idxOf v := by
        have := idxOf_tail_succ p.support hpN v hv1
        omega
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
  obtain ⟨v₀, v₂, w, p, q, hp, hdva, hq, hmle, h2, hv₂, hpw, h7a, h7b, h7c,
    hover⟩ := chung_chords hconn hr2 hdrop
  have hpgeo : p.length = G.dist v₀ a := hp.trans hdva.symm
  rcases Nat.eq_zero_or_pos q.length with hm0 | h1m
  · -- m = 0: r = 2 and the geodesic p alone spans 2r - 1 vertices
    have h2' : 2 ≤ p.length := by rw [hp]; exact hr2
    have hv₂₀ : G.dist v₂ v₀ = 2 := by
      rw [← hv₂, SimpleGraph.dist_comm]
      exact dist_getVert_of_length_eq_dist hpgeo 2 h2'
    have ht : G.dist v₂ w ≤ 2 := by
      have htr := hconn.dist_triangle (u := v₂) (v := v₀) (w := w)
      rw [hv₂₀] at htr
      cases q with
      | nil => rw [SimpleGraph.dist_self] at htr; omega
      | cons h' t' =>
        rw [SimpleGraph.Walk.length_cons] at hm0
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

end Graffiti84
