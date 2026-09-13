import Mathlib

/-!
# BasicFacts

Foundational layer for the Graffiti84 proof (Phase 1 of `docs/full-proof.md`).

We use a *set-relative deletion framework*: instead of forming the subgraph
`G - v` (whose Mathlib version changes the vertex type), we keep the ambient
graph `G` and restrict quantification to a vertex set `S`.  Distances are
ambient `G`-distances; this is faithful to the paper because every radius
claim about `G - v` is used via distance bounds among the surviving vertices.

* `eccOn G S c` : eccentricity of `c` restricted to `S`;
* `radOn G S`   : radius restricted to `S` (`S = univ` gives `r(G)`,
  `S = univ.erase v` gives `r(G - v)`);
* `DeleteConnected G v` : every two vertices other than `v` are joined by a
  walk avoiding `v` (paper: "`G - v` is connected");
* `IsCut G v` : `v` is a cut vertex.

Facts proved here (numbering of `docs/full-proof.md`):
F3  `radOn_le_radOn_erase_add_one`   — radius drops by at most one;
F6  `one_add_eccent_parent_le_eccOn` — `1 + ecc(p) ≤ ecc(leaf)` (leaf not central);
F11 `isCut_of_isLeaf`                — the neighbour of a leaf is a cut vertex;
F9  `isUniqueEccentricPoint_unique`  — a vertex has at most one UEP.
-/

namespace Graffiti84

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Definitions -/

/-- Eccentricity of `c` restricted to a vertex set `S`. -/
noncomputable def eccOn (G : SimpleGraph α) (S : Finset α) (c : α) : ℕ∞ :=
  ⨆ x ∈ S, G.edist c x

/-- Radius of `G` restricted to a vertex set `S`. -/
noncomputable def radOn (G : SimpleGraph α) (S : Finset α) : ℕ∞ :=
  ⨅ c ∈ S, eccOn G S c

/-- Every two vertices other than `v` are joined by a walk avoiding `v`:
the paper's "`G - v` is connected". -/
def DeleteConnected (G : SimpleGraph α) (v : α) : Prop :=
  ∀ x y : α, x ≠ v → y ≠ v → ∃ w : G.Walk x y, v ∉ w.support

/-- `v` is a cut vertex of `G`. -/
def IsCut (G : SimpleGraph α) (v : α) : Prop :=
  ¬ DeleteConnected G v

/-! ## eccOn / radOn basics -/

lemma edist_le_eccOn {G : SimpleGraph α} {S : Finset α} {c x : α} (hx : x ∈ S) :
    G.edist c x ≤ eccOn G S c :=
  le_iSup₂ (f := fun i (_ : i ∈ S) => G.edist c i) x hx

lemma eccOn_le {G : SimpleGraph α} {S : Finset α} {c : α} {k : ℕ∞}
    (h : ∀ x ∈ S, G.edist c x ≤ k) : eccOn G S c ≤ k := iSup₂_le h

lemma radOn_le_eccOn {G : SimpleGraph α} {S : Finset α} {c : α} (hc : c ∈ S) :
    radOn G S ≤ eccOn G S c := iInf₂_le c hc

/-- The restricted radius is attained by some centre. -/
lemma eccOn_eq_radOn_attained {G : SimpleGraph α} {S : Finset α} (hS : S.Nonempty) :
    ∃ c ∈ S, eccOn G S c = radOn G S := by
  obtain ⟨c0, hc0⟩ := hS
  haveI : Nonempty {x // x ∈ S} := ⟨⟨c0, hc0⟩⟩
  obtain ⟨m, hm⟩ := Finite.exists_min (f := fun c : {x // x ∈ S} => eccOn G S c)
  exact ⟨m, m.property, le_antisymm (le_iInf₂ fun c hc => hm ⟨c, hc⟩)
    (iInf₂_le m.val m.property)⟩

/-- Bridging: `eccOn` over all vertices is Mathlib's eccentricity. -/
lemma eccOn_univ_eq_eccent {G : SimpleGraph α} {c : α} :
    eccOn G Finset.univ c = G.eccent c := by
  simp [eccOn, SimpleGraph.eccent]

/-- Bridging: `radOn` over all vertices is Mathlib's radius. -/
lemma radOn_univ_eq_radius {G : SimpleGraph α} :
    radOn G Finset.univ = G.radius := by
  simp [radOn, SimpleGraph.radius, eccOn_univ_eq_eccent]

/-! ## Walk-distance helpers -/

/-- `d(u, w) ≤ d(u, v) + 1` when `u` reaches `v` and `v ∼ w`. -/
lemma edist_le_add_edge {G : SimpleGraph α} {u v w : α}
    (hR : G.Reachable u v) (hvw : G.Adj v w) :
    G.edist u w ≤ G.edist u v + 1 := by
  have hne : G.edist u v ≠ ⊤ := SimpleGraph.edist_ne_top_iff_reachable.mpr hR
  have hcoe : ((G.edist u v).toNat : ℕ∞) = G.edist u v := ENat.coe_toNat hne
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe
    (k := (G.edist u v).toNat) hcoe.symm
  have h1 : (SimpleGraph.Adj.toWalk hvw).length = 1 := by
    simp [SimpleGraph.Adj.toWalk]
  have hlen : (p.append (SimpleGraph.Adj.toWalk hvw)).length
      = (G.edist u v).toNat + 1 := by
    rw [SimpleGraph.Walk.length_append, hp, h1]
  calc G.edist u w ≤ ((p.append (SimpleGraph.Adj.toWalk hvw)).length : ℕ∞) :=
      SimpleGraph.edist_le _
  _ = ((G.edist u v).toNat + 1 : ℕ∞) := by rw [hlen]; norm_cast
  _ = G.edist u v + 1 := by rw [← hcoe]; simp

/-- A vertex of degree one has at most one neighbour. -/
lemma adj_eq_of_degree_eq_one {G : SimpleGraph α} {z a b : α}
    (hdeg : G.degree z = 1) (ha : G.Adj z a) (hb : G.Adj z b) : a = b := by
  have hcard : (G.neighborFinset z).card = 1 := by simpa using hdeg
  rw [Finset.card_eq_one] at hcard
  obtain ⟨c, hc⟩ := hcard
  have e1 : a ∈ G.neighborFinset z := by simpa using ha
  have e2 : b ∈ G.neighborFinset z := by simpa using hb
  rw [hc] at e1 e2
  simp only [Finset.mem_singleton] at e1 e2
  exact e1.trans e2.symm

/-- A graph on at least three vertices has a vertex outside any given pair. -/
lemma exists_ne_pair_of_three {a b : α} (hn3 : 3 ≤ Fintype.card α) :
    ∃ t : α, t ≠ a ∧ t ≠ b := by
  by_contra hall
  have hall' : ∀ t : α, t = a ∨ t = b := by
    intro t
    by_cases h1 : t = a
    · exact Or.inl h1
    by_cases h2 : t = b
    · exact Or.inr h2
    exact absurd ⟨t, h1, h2⟩ hall
  have hsub : (Finset.univ : Finset α) ⊆ {a, b} := by
    intro x _
    rcases hall' x with h | h
    · simp [h]
    · simp [h]
  have hcard := Finset.card_le_card hsub
  have hcard2 : Fintype.card α = (Finset.univ : Finset α).card := rfl
  by_cases hab : a = b
  · have hc1 : ({a, b} : Finset α).card = 1 := by rw [hab]; simp
    omega
  · have hc2 : ({a, b} : Finset α).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    omega

/-! ## F3: the radius drops by at most one -/

/-- **F3.** Deleting one vertex from the set lowers the restricted radius by
at most one, provided the deleted vertex has a neighbour left in the set. -/
lemma radOn_le_radOn_erase_add_one {G : SimpleGraph α} {S : Finset α} {v : α}
    (hv : v ∈ S) (hconn : G.Connected)
    (hw : ∃ w ∈ S, w ≠ v ∧ G.Adj v w) :
    radOn G S ≤ radOn G (S.erase v) + 1 := by
  by_cases hSe : (S.erase v).Nonempty
  · obtain ⟨c, hc, hcmin⟩ := eccOn_eq_radOn_attained hSe
    have hmem : c ∈ S := (S.mem_erase.mp hc).2
    refine le_trans (iInf₂_le c hmem) ?_
    rw [← hcmin]
    refine eccOn_le ?_
    intro x hx
    by_cases hxv : x = v
    · obtain ⟨w, hws, hwne, hwadj⟩ := hw
      have hR : G.Reachable c w := hconn.preconnected c w
      have hwse : w ∈ S.erase v := Finset.mem_erase.mpr ⟨hwne, hws⟩
      have h5 : G.edist c w ≤ eccOn G (S.erase v) c := edist_le_eccOn hwse
      calc G.edist c x = G.edist c v := by rw [hxv]
      _ ≤ G.edist c w + 1 := edist_le_add_edge hR hwadj.symm
      _ ≤ eccOn G (S.erase v) c + 1 := add_le_add h5 (le_refl 1)
    · have hx' : x ∈ S.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
      calc G.edist c x ≤ eccOn G (S.erase v) c := edist_le_eccOn hx'
      _ ≤ eccOn G (S.erase v) c + 1 := le_self_add
  · -- S = {v}, whose restricted radius is 0
    have hS : S = {v} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨hv, fun x hx => ?_⟩
      by_contra hxv
      exact hSe ⟨x, Finset.mem_erase.mpr ⟨hxv, hx⟩⟩
    subst hS
    have hr0 : radOn G {v} = 0 := by
      have h0 : eccOn G {v} v = 0 := by
        simp only [eccOn, Finset.iSup_singleton]
        refine le_antisymm ?_ bot_le
        exact SimpleGraph.edist_le SimpleGraph.Walk.nil
      have h1 := radOn_le_eccOn (G := G) (S := ({v} : Finset α)) (c := v)
        (Finset.mem_singleton.mpr rfl)
      rw [h0] at h1
      exact le_antisymm h1 bot_le
    have he : (({v} : Finset α).erase v) = ∅ := by simp
    have htop : radOn G (({v} : Finset α).erase v) = ⊤ := by
      rw [he]; simp [radOn]
    rw [htop, hr0]
    simp

/-! ## F6: a leaf is not central -/

/-- If `z` is a leaf with neighbour `p` in a connected graph, then
`d(z, y) = 1 + d(p, y)` for every `y ≠ z`. -/
lemma edist_leaf_eq {G : SimpleGraph α} (hconn : G.Connected) {z p y : α}
    (hdeg : G.degree z = 1) (hzp : G.Adj z p) (hy : y ≠ z) :
    G.edist z y = 1 + G.edist p y := by
  have hne : G.edist p y ≠ ⊤ :=
    SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected p y)
  have hcoe : ((G.edist p y).toNat : ℕ∞) = G.edist p y := ENat.coe_toNat hne
  obtain ⟨q, hq⟩ := SimpleGraph.exists_walk_of_edist_eq_coe
    (k := (G.edist p y).toNat) hcoe.symm
  have hup : G.edist z y ≤ 1 + G.edist p y := by
    have hlen : (SimpleGraph.Walk.cons hzp q).length = 1 + (G.edist p y).toNat := by
      rw [SimpleGraph.Walk.length_cons, hq]; omega
    calc G.edist z y ≤ ((SimpleGraph.Walk.cons hzp q).length : ℕ∞) :=
        SimpleGraph.edist_le _
    _ = ((1 + (G.edist p y).toNat : ℕ) : ℕ∞) := by rw [hlen]
    _ = 1 + G.edist p y := by rw [← hcoe]; simp
  have hdown : 1 + G.edist p y ≤ G.edist z y := by
    refine le_iInf fun w => ?_
    cases w with
    | nil => exact absurd rfl hy
    | @cons _ x _ h w' =>
      have hxp : x = p := adj_eq_of_degree_eq_one hdeg h hzp
      subst hxp
      calc (1 : ℕ∞) + G.edist x y ≤ 1 + w'.length :=
          add_le_add_left (SimpleGraph.edist_le w') _
      _ = ((SimpleGraph.Walk.cons h w').length : ℕ∞) := by
          rw [SimpleGraph.Walk.length_cons]; simp
  exact le_antisymm hup hdown

/-- **F6.** If `z` is a leaf with neighbour `p` in a connected graph on at
least three vertices, then `1 + ecc(p) ≤ ecc(z)`; in particular `z` is not
central (combine with `radius_le_eccent`). -/
lemma one_add_eccent_parent_le_eccOn {G : SimpleGraph α} (hconn : G.Connected)
    {z p : α} (hdeg : G.degree z = 1) (hzp : G.Adj z p)
    (hn3 : 3 ≤ Fintype.card α) :
    (1 : ℕ∞) + G.eccent p ≤ eccOn G Finset.univ z := by
  haveI : Nonempty α := ⟨p⟩
  obtain ⟨y, hymax⟩ := Finite.exists_max (f := fun x : α => G.edist p x)
  have heccy : G.eccent p = G.edist p y := by
    rw [SimpleGraph.eccent]
    exact le_antisymm (iSup_le hymax) (le_iSup y)
  by_cases hyz : y = z
  · -- the parent's farthest vertex is the leaf itself: ecc(p) = 1
    subst hyz
    have hecc1 : G.eccent p = 1 := by
      rw [heccy]
      have htw : (SimpleGraph.Adj.toWalk hzp).length = 1 := by
        simp [SimpleGraph.Adj.toWalk]
      have h2 : G.edist p z ≤ ((SimpleGraph.Adj.toWalk hzp).length : ℕ∞) :=
        SimpleGraph.edist_le (SimpleGraph.Adj.toWalk hzp)
      rw [htw] at h2
      exact le_antisymm h2 (Order.one_le_iff_pos.mpr
        (SimpleGraph.edist_pos_of_ne (G.ne_of_adj hzp).symm))
    obtain ⟨t, htz, htp⟩ := exists_ne_pair_of_three hn3
    calc (1 : ℕ∞) + G.eccent p = 2 := by rw [hecc1]; norm_num
    _ = 1 + 1 := rfl
    _ ≤ 1 + G.edist p t := add_le_add_left
        (Order.one_le_iff_pos.mpr (SimpleGraph.edist_pos_of_ne htp)) _
    _ = G.edist z t := (edist_leaf_eq hconn hdeg hzp htz).symm
    _ ≤ eccOn G Finset.univ z := edist_le_eccOn (Finset.mem_univ t)
  · calc (1 : ℕ∞) + G.eccent p = 1 + G.edist p y := by rw [heccy]
    _ = G.edist z y := (edist_leaf_eq hconn hdeg hzp hyz).symm
    _ ≤ eccOn G Finset.univ z := edist_le_eccOn (Finset.mem_univ y)

/-- Corollary of F6: a leaf is not central. -/
lemma radius_lt_eccOn_of_isLeaf {G : SimpleGraph α} (hconn : G.Connected)
    {z p : α} (hdeg : G.degree z = 1) (hzp : G.Adj z p)
    (hn3 : 3 ≤ Fintype.card α) :
    (1 : ℕ∞) + G.radius ≤ eccOn G Finset.univ z :=
  le_trans (add_le_add_left G.radius_le_eccent _)
    (one_add_eccent_parent_le_eccOn hconn hdeg hzp hn3)

/-! ## F11: the neighbour of a leaf is a cut vertex -/

/-- **F11.** If `z` is a leaf with neighbour `p` in a graph on at least three
vertices, then `p` is a cut vertex. -/
lemma isCut_of_isLeaf {G : SimpleGraph α} {z p : α}
    (hdeg : G.degree z = 1) (hzp : G.Adj z p)
    (hzn : z ≠ p) (hn3 : 3 ≤ Fintype.card α) : IsCut G p := by
  intro hdel
  obtain ⟨t, htz, htp⟩ := exists_ne_pair_of_three hn3
  obtain ⟨w, hw⟩ := hdel z t hzn htp
  cases w with
  | nil => exact htz rfl
  | cons h w' =>
    have hxp := adj_eq_of_degree_eq_one hdeg h hzp
    subst hxp
    refine hw ?_
    cases w' with
    | nil => simp
    | cons h2 w2 => simp

/-! ## F9: a vertex has at most one unique eccentric point -/

/-- `x` is the unique eccentric point of `c`: it is eccentric from `c`, and no
other vertex is as far from `c`. -/
def IsUniqueEccentricPoint (G : SimpleGraph α) (c x : α) : Prop :=
  G.dist c x = (G.eccent c).toNat ∧
    ∀ y : α, y ≠ x → G.dist c y < (G.eccent c).toNat

lemma isUniqueEccentricPoint_unique {G : SimpleGraph α} {c x x' : α}
    (h : IsUniqueEccentricPoint G c x) (h' : IsUniqueEccentricPoint G c x') :
    x = x' := by
  by_contra hne
  have hlt := h.2 x' (fun hh => hne (by rw [hh]))
  exact absurd h'.1 hlt

end Graffiti84
