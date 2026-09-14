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
      refine le_trans SimpleGraph.radius_le_eccent ?_
      rw [hw]
    exact absurd hge (not_le.mpr hlt)
  have hdvw : G.dist v₀ w + 1 ≤ G.radius.toNat := by
    have hc3 : ((G.dist v₀ w : ℕ) : ℕ∞) = G.edist v₀ w :=
      (hconn.preconnected v₀ w).coe_dist_eq_edist
    have hle3 : G.edist v₀ w ≤ ρ := hedρ w
      (Finset.mem_erase.mpr ⟨hwne, Finset.mem_univ w⟩)
    have hpt : ρ.toNat + 1 = G.radius.toNat := by
      have hfull : ((ρ.toNat + 1 : ℕ) : ℕ∞) = ((G.radius.toNat : ℕ) : ℕ∞) := by
        rw [Nat.cast_add, Nat.cast_one, ← hρc, ← hradius, hrc]
      exact ENat.coe_inj.mp hfull
    have hcoele : (G.dist v₀ w : ℕ∞) ≤ (ρ.toNat : ℕ∞) := by
      rw [hc3, hρc]
      exact hle3
    have : G.dist v₀ w ≤ ρ.toNat := ENat.coe_le_coe.mp hcoele
    omega
  have hdv₂w : G.radius.toNat ≤ G.dist v₂ w := by
    have hc4 : ((G.dist v₂ w : ℕ) : ℕ∞) = G.edist v₂ w :=
      (hconn.preconnected v₂ w).coe_dist_eq_edist
    have hge : G.radius ≤ G.edist v₂ w := by
      refine le_trans SimpleGraph.radius_le_eccent ?_
      rw [hw]
    rw [← hrc] at hge
    rw [← hc4] at hge
    exact ENat.coe_le_coe.mp hge
  obtain ⟨q, hq⟩ := (hconn.preconnected v₀ w).exists_walk_length_eq_dist
  exact ⟨v₀, v₂, w, p, q, hp, hdva, hv₂def, hdv₂a, hq, hdvw, hdv₂w⟩

end Graffiti84
