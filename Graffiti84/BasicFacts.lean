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
          add_le_add_right (SimpleGraph.edist_le w') 1
      _ = ((SimpleGraph.Walk.cons h w').length : ℕ∞) := by
          rw [SimpleGraph.Walk.length_cons]; simp [Nat.add_comm]
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
    exact le_antisymm (iSup_le hymax) (le_iSup (f := fun i => G.edist p i) y)
  by_cases hyz : y = z
  · -- the parent's farthest vertex is the leaf itself: ecc(p) = 1
    rw [hyz] at heccy
    have hecc1 : G.eccent p = 1 := by
      rw [heccy]
      have htw : (SimpleGraph.Adj.toWalk hzp.symm).length = 1 := by
        simp [SimpleGraph.Adj.toWalk]
      have h2 : G.edist p z ≤ ((SimpleGraph.Adj.toWalk hzp.symm).length : ℕ∞) :=
        SimpleGraph.edist_le (SimpleGraph.Adj.toWalk hzp.symm)
      rw [htw] at h2
      exact le_antisymm h2 (Order.one_le_iff_pos.mpr
        (SimpleGraph.edist_pos_of_ne (G.ne_of_adj hzp).symm))
    obtain ⟨t, htz, htp⟩ := exists_ne_pair_of_three hn3
    have hpt : (1 : ℕ∞) ≤ G.edist p t :=
      Order.one_le_iff_pos.mpr (SimpleGraph.edist_pos_of_ne htp.symm)
    calc (1 : ℕ∞) + G.eccent p = 2 := by rw [hecc1]; norm_num
    _ = 1 + 1 := rfl
    _ ≤ 1 + G.edist p t := add_le_add (le_refl 1) hpt
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
  le_trans (add_le_add_right G.radius_le_eccent 1)
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
  rw [h'.1] at hlt
  exact absurd hlt (lt_irrefl _)


/-! ## Batch 2: walk toolkit and the UEP criterion (F7, F8, F5) -/

/-- Prepending an edge costs at most one: `d(u, w) <= 1 + d(v, w)` when
`u ~ v` and `v` reaches `w`. -/
lemma edist_le_add_edge_prepend {G : SimpleGraph α} {u v w : α}
    (huv : G.Adj u v) (hR : G.Reachable v w) :
    G.edist u w ≤ 1 + G.edist v w := by
  have h1 : G.edist w u ≤ G.edist w v + 1 :=
    edist_le_add_edge hR.symm huv.symm
  have h2 : G.edist w u = G.edist u w :=
    SimpleGraph.edist_comm (u := w) (v := u)
  have h3 : G.edist w v = G.edist v w :=
    SimpleGraph.edist_comm (u := w) (v := v)
  calc G.edist u w = G.edist w u := h2.symm
  _ ≤ G.edist w v + 1 := h1
  _ = G.edist v w + 1 := by rw [h3]
  _ = 1 + G.edist v w := (add_comm (G.edist v w) 1)

/-- Any walk through `v` is at least as long as the two geodesic legs. -/
lemma edist_add_edist_le_of_mem_support {G : SimpleGraph α} {u v w : α}
    {p : G.Walk u w} (hpv : v ∈ p.support) :
    G.edist u v + G.edist v w ≤ (p.length : ℕ∞) := by
  induction p with
  | @nil a =>
      have hvu : v = a := by simpa using hpv
      subst hvu
      simp [SimpleGraph.edist_self]
  | @cons u x w h q ih =>
      have hmem : v ∈ (SimpleGraph.Walk.cons h q).support := hpv
      rw [SimpleGraph.Walk.support_cons] at hmem
      rcases List.mem_cons.mp hmem with rfl | hpv'
      · simp only [SimpleGraph.edist_self, zero_add]
        exact SimpleGraph.edist_le (SimpleGraph.Walk.cons h q)
      · have hsum := ih hpv'
        have hfin : ((q.length : ℕ) : ℕ∞) < ⊤ := ENat.coe_lt_top _
        have hne : G.edist x v ≠ ⊤ := by
          intro hc
          rw [hc] at hsum
          simp at hsum
        have hr : G.Reachable x v := SimpleGraph.edist_ne_top_iff_reachable.mp hne
        have hpre : G.edist u v ≤ 1 + G.edist x v := edist_le_add_edge_prepend h hr
        have step1 : G.edist u v + G.edist v w ≤ (1 + G.edist x v) + G.edist v w :=
          add_le_add_left hpre (G.edist v w)
        have step2 : (1 + G.edist x v) + G.edist v w ≤ 1 + ((q.length : ℕ) : ℕ∞) := by
          rw [add_assoc]
          exact add_le_add_right hsum 1
        calc G.edist u v + G.edist v w ≤
            ((1 + G.edist x v) + G.edist v w : ℕ∞) := step1
        _ ≤ 1 + ((q.length : ℕ) : ℕ∞) := le_trans step2 (le_refl _)
        _ ≤ ((q.length + 1 : ℕ) : ℕ∞) := by
            exact_mod_cast (show (1 : ℕ) + q.length ≤ q.length + 1 from by omega)
        _ = ((SimpleGraph.Walk.cons h q).length : ℕ∞) := by
            rw [SimpleGraph.Walk.length_cons]

/-- Bridging: in a connected graph, `dist < ecc.toNat` upgrades to an
`ENat`-strict bound. -/
lemma edist_lt_eccent_of_dist_lt {G : SimpleGraph α} (hconn : G.Connected)
    {c x : α} (hlt : G.dist c x < (G.eccent c).toNat) :
    G.edist c x < G.eccent c := by
  have hne : G.eccent c ≠ ⊤ := by
    obtain ⟨t, ht⟩ := G.exists_edist_eq_eccent_of_finite c
    intro h
    rw [← ht] at h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t) h
  have hcoe : ((G.eccent c).toNat : ℕ∞) = G.eccent c := ENat.coe_toNat hne
  have hd : ((G.dist c x : ℕ) : ℕ∞) = G.edist c x := by
    show (((G.edist c x).toNat : ℕ) : ℕ∞) = _
    exact ENat.coe_toNat
      (SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c x))
  calc G.edist c x = ((G.dist c x : ℕ) : ℕ∞) := hd.symm
  _ < ((G.eccent c).toNat : ℕ∞) := by exact_mod_cast hlt
  _ = G.eccent c := hcoe

/-- The distance from a centre to its unique eccentric point is the full
eccentricity. -/
lemma edist_eq_eccent_of_isUniqueEccentricPoint {G : SimpleGraph α}
    (hconn : G.Connected) {c v : α} (huep : IsUniqueEccentricPoint G c v) :
    G.edist c v = G.eccent c := by
  have hne : G.eccent c ≠ ⊤ := by
    obtain ⟨t, ht⟩ := G.exists_edist_eq_eccent_of_finite c
    intro h
    rw [← ht] at h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t) h
  have hcoe : ((G.eccent c).toNat : ℕ∞) = G.eccent c := ENat.coe_toNat hne
  have hd : ((G.dist c v : ℕ) : ℕ∞) = G.edist c v := by
    show (((G.edist c v).toNat : ℕ) : ℕ∞) = _
    exact ENat.coe_toNat
      (SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c v))
  rw [← hcoe, ← hd, huep.1]

/-- A vertex is central iff it realizes the graph radius. -/
def IsCentral (G : SimpleGraph α) (v : α) : Prop :=
  G.eccent v = G.radius

/-! ### F7: the drop half of the criterion -/

/-- **F7 (drop).** If a centre has the unique eccentric point `v`, then `G - v`
is connected. -/
lemma deleteConnected_of_isUniqueEccentricPoint {G : SimpleGraph α}
    (hconn : G.Connected) {c v : α} (huep : IsUniqueEccentricPoint G c v) :
    DeleteConnected G v := by
  have hcv : G.edist c v = G.eccent c :=
    edist_eq_eccent_of_isUniqueEccentricPoint hconn huep
  have hlt : ∀ {w : α}, w ≠ v → G.edist c w < G.eccent c := by
    intro w hw
    exact edist_lt_eccent_of_dist_lt hconn (huep.2 w hw)
  have hne : G.eccent c ≠ ⊤ := by
    obtain ⟨t, ht⟩ := G.exists_edist_eq_eccent_of_finite c
    intro h
    rw [← ht] at h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t) h
  have hcoee : ((G.eccent c).toNat : ℕ∞) = G.eccent c := ENat.coe_toNat hne
  intro x y hx hy
  -- every geodesic from c to w ≠ v avoids v
  have havoid : ∀ {w : α}, w ≠ v → ∃ q : G.Walk c w, v ∈ q.support → False := by
    intro w hw
    have hco1 : ((G.edist c v).toNat : ℕ∞) = G.edist c v :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected c v))
    have hco2 : ((G.edist v w).toNat : ℕ∞) = G.edist v w :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected v w))
    have hcw : ((G.edist c w).toNat : ℕ∞) = G.edist c w :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected c w))
    have hvw : ((G.edist v w).toNat : ℕ∞) = G.edist v w :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected v w))
    obtain ⟨q, hq⟩ := SimpleGraph.exists_walk_of_edist_eq_coe
      (k := (G.edist c w).toNat) hcw.symm
    refine ⟨q, fun hpv => ?_⟩
    have hsum := edist_add_edist_le_of_mem_support (p := q) hpv
    rw [hq] at hsum
    have hnat1 : (1 : ℕ) ≤ (G.edist v w).toNat := by
      refine ENat.coe_le_coe.mp ?_
      rw [hvw]
      exact Order.one_le_iff_pos.mpr
        (SimpleGraph.edist_pos_of_ne (Ne.symm hw))
    have hnat2 : ((G.edist c v).toNat + (G.edist v w).toNat : ℕ)
        ≤ (G.edist c w).toNat := by
      refine ENat.coe_le_coe.mp ?_
      push_cast
      rw [hco1, hco2]
      exact hsum
    have hnat3 : (G.edist c w).toNat < (G.eccent c).toNat := by
      refine ENat.coe_lt_coe.mp ?_
      rw [hcw, hcoee]
      exact hlt hw
    have hnat4 : (G.edist c v).toNat = (G.eccent c).toNat := by rw [hcv]
    omega
  obtain ⟨qx, hxq⟩ := havoid hx
  obtain ⟨qy, hyq⟩ := havoid hy
  refine ⟨qx.reverse.append qy, ?_⟩
  intro hv
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse] at hv
  simp only [List.mem_reverse] at hv
  rcases hv with h | h
  · exact hxq h
  · exact hyq h

lemma radOn_erase_add_one_le_of_isUniqueEccentricPoint {G : SimpleGraph α}
    (hconn : G.Connected) {c v : α} (hnt : Nontrivial α) (hc : IsCentral G c)
    (huep : IsUniqueEccentricPoint G c v) :
    radOn G (Finset.univ.erase v) + 1 ≤ radOn G Finset.univ := by
  have hcv : G.edist c v = G.eccent c :=
    edist_eq_eccent_of_isUniqueEccentricPoint hconn huep
  have hcne : c ≠ v := by
    intro h
    rw [h] at hcv
    simp [SimpleGraph.edist_self] at hcv
    exact SimpleGraph.eccent_ne_zero v hcv.symm
  have hmem : c ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨hcne, Finset.mem_univ c⟩
  have hsup : ∃ y ∈ Finset.univ.erase v,
      eccOn G (Finset.univ.erase v) c = G.edist c y := by
    obtain ⟨c0, hc0⟩ : (Finset.univ.erase v).Nonempty :=
      ⟨c, Finset.mem_erase.mpr ⟨hcne, Finset.mem_univ c⟩⟩
    haveI : Nonempty {x // x ∈ Finset.univ.erase v} := ⟨⟨c0, hc0⟩⟩
    obtain ⟨m, hm⟩ := Finite.exists_max
      (f := fun x : {x // x ∈ Finset.univ.erase v} => G.edist c x)
    exact ⟨m, m.property, le_antisymm (iSup₂_le fun x hx => hm ⟨x, hx⟩)
      (le_iSup₂ (f := fun i (_ : i ∈ Finset.univ.erase v) => G.edist c i)
        m.val m.property)⟩
  obtain ⟨y, hy, hyc⟩ := hsup
  have hyv : y ≠ v := (Finset.univ.mem_erase.mp hy).1
  have hstep_ne_top : G.eccent c ≠ ⊤ := by
    obtain ⟨t, ht⟩ := G.exists_edist_eq_eccent_of_finite c
    intro h
    rw [← ht] at h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t) h
  have hstep : eccOn G (Finset.univ.erase v) c + 1 ≤ G.eccent c := by
    rw [hyc]
    have hlt : G.edist c y < G.eccent c :=
      edist_lt_eccent_of_dist_lt hconn (huep.2 y hyv)
    exact (ENat.add_one_le_iff' (hn := hstep_ne_top)
      (m := G.edist c y)).mpr hlt
  calc radOn G (Finset.univ.erase v) + 1
      ≤ eccOn G (Finset.univ.erase v) c + 1 :=
        add_le_add (radOn_le_eccOn hmem) (le_refl 1)
  _ ≤ G.eccent c := hstep
  _ = radOn G Finset.univ := by
      rw [radOn_univ_eq_radius, ← hc]


/-! ### F8: the converse half of the criterion -/

/-- **F8 (converse).** If deleting `v` lowers the full radius by exactly one
(in the ambient-distance bookkeeping), the centre of the deleted graph is a
central vertex of `G` whose unique eccentric point is `v`. -/
lemma isUniqueEccentricPoint_of_radOn_erase {G : SimpleGraph α}
    (hconn : G.Connected) {v : α} (h2 : 2 ≤ Fintype.card α)
    (hmono : radOn G (Finset.univ.erase v) + 1 ≤ radOn G Finset.univ) :
    ∃ c, IsCentral G c ∧ IsUniqueEccentricPoint G c v := by
  haveI : Nontrivial α := by
    by_contra hnt
    have hall2 : ∀ w : α, w = v := by
      intro w
      by_contra hw
      exact hnt ⟨v, w, fun hh => hw hh.symm⟩
    have hsub : (Finset.univ : Finset α) = {v} :=
      Finset.eq_singleton_iff_unique_mem.2
        ⟨Finset.mem_univ v, fun x _ => hall2 x⟩
    have hcard2 : Fintype.card α = (Finset.univ : Finset α).card := rfl
    rw [hcard2, hsub] at h2
    simp at h2
  obtain ⟨x, hx⟩ := exists_ne v
  have hSe : (Finset.univ.erase v).Nonempty :=
    ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩⟩
  obtain ⟨c, hc, hcmin⟩ := eccOn_eq_radOn_attained hSe
  have hcne : c ≠ v := (Finset.univ.mem_erase.mp hc).1
  obtain ⟨w, hwadj⟩ : ∃ w, G.Adj v w := by
    have hne : G.edist v x ≠ ⊤ :=
      SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected v x)
    have hcoe : ((G.edist v x).toNat : ℕ∞) = G.edist v x := ENat.coe_toNat hne
    obtain ⟨q, hq⟩ := SimpleGraph.exists_walk_of_edist_eq_coe
      (k := (G.edist v x).toNat) hcoe.symm
    cases q with
    | nil => exact absurd rfl hx
    | cons h _ => exact ⟨_, h⟩
  have hwne : w ≠ v := (G.ne_of_adj hwadj).symm
  have hwse : w ∈ Finset.univ.erase v := Finset.mem_erase.mpr
    ⟨hwne, Finset.mem_univ w⟩
  have hw' : G.edist c w ≤ radOn G (Finset.univ.erase v) :=
    (edist_le_eccOn (G := G) (S := Finset.univ.erase v) (c := c) hwse).trans
      (le_of_eq hcmin)
  -- the eccentricity of c is at most ρ + 1
  have hecc : G.eccent c ≤ radOn G (Finset.univ.erase v) + 1 := by
    rw [← eccOn_univ_eq_eccent]
    refine eccOn_le (G := G) (S := Finset.univ) (c := c) (k := _) ?_
    intro x _
    by_cases hxv : x = v
    · calc G.edist c x = G.edist c v := by rw [hxv]
      _ ≤ G.edist c w + 1 := edist_le_add_edge (hconn.preconnected c w) hwadj.symm
      _ ≤ radOn G (Finset.univ.erase v) + 1 := add_le_add hw' (le_refl 1)
    · exact le_trans (le_trans (edist_le_eccOn
        (G := G) (S := Finset.univ.erase v) (c := c)
        (Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩)) (le_of_eq hcmin))
        (le_self_add)
  have heccne : G.eccent c ≠ ⊤ := by
    obtain ⟨t, ht⟩ := G.exists_edist_eq_eccent_of_finite c
    intro h
    rw [← ht] at h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t) h
  have hcoee : ((G.eccent c).toNat : ℕ∞) = G.eccent c := ENat.coe_toNat heccne
  -- c is central, and radius = restricted radius + 1
  have hradius : G.radius = radOn G (Finset.univ.erase v) + 1 :=
    le_antisymm (le_trans SimpleGraph.radius_le_eccent hecc)
      (hmono.trans (le_of_eq radOn_univ_eq_radius))
  have hcen : IsCentral G c :=
    le_antisymm (le_trans hecc (le_of_eq hradius.symm))
      SimpleGraph.radius_le_eccent
  have heq : G.eccent c = radOn G (Finset.univ.erase v) + 1 :=
    hcen.trans hradius
  have hρne : radOn G (Finset.univ.erase v) ≠ ⊤ := by
    intro h
    rw [h] at heq
    simp at heq
    exact heccne heq
  refine ⟨c, hcen, ?_, fun y hy => ?_⟩
  · -- dist c v = ecc.toNat
    have hc3 : ((G.edist c v).toNat : ℕ∞) = G.edist c v :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected c v))
    have hed : G.edist c v = G.eccent c := by
      refine le_antisymm ?_ ?_
      · calc G.edist c v ≤ G.edist c w + 1 :=
            edist_le_add_edge (hconn.preconnected c w) hwadj.symm
        _ ≤ radOn G (Finset.univ.erase v) + 1 := add_le_add hw' (le_refl 1)
        _ = G.eccent c := heq.symm
      · -- ecc c ≤ edist c v: otherwise all vertices are within ρ of c
        by_contra hcon
        push_neg at hcon
        rw [heq] at hcon
        have hallv : ∀ x : α, G.edist c x
            ≤ radOn G (Finset.univ.erase v) := by
          intro x
          by_cases hxv : x = v
          · rw [hxv]
            have hcoV : ((G.edist c v).toNat : ℕ∞) = G.edist c v :=
              ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
                (hconn.preconnected c v))
            rw [← hcoV] at hcon
            rw [← hcoV]
            exact ENat.lt_add_one_iff' (hm := ENat.coe_ne_top _) |>.mp hcon
          · exact (edist_le_eccOn
              (G := G) (S := Finset.univ.erase v) (c := c)
              (Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩)).trans
              (le_of_eq hcmin)
        have hsmall : G.eccent c ≤ radOn G (Finset.univ.erase v) := by
          rw [← eccOn_univ_eq_eccent]
          refine eccOn_le (G := G) (S := Finset.univ) (c := c) (k := _)
            (fun x _ => hallv x)
        rw [heq] at hsmall
        exact absurd (ENat.add_one_le_iff hρne |>.mp hsmall) (lt_irrefl _)
    have hdist : G.dist c v = (G.edist c v).toNat := rfl
    rw [hdist]
    exact congrArg ENat.toNat hed
  · -- dist c y < ecc.toNat for y ≠ v
    have hdy : G.edist c y ≤ radOn G (Finset.univ.erase v) :=
      (edist_le_eccOn (G := G) (S := Finset.univ.erase v) (c := c)
        (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩)).trans (le_of_eq hcmin)
    have hcoe1 : ((G.dist c y : ℕ) : ℕ∞) = G.edist c y := by
      show (((G.edist c y).toNat : ℕ) : ℕ∞) = _
      exact ENat.coe_toNat
        (SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c y))
    have hfin : G.edist c y ≠ ⊤ :=
      SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c y)
    have hstep : G.edist c y + 1 ≤ G.eccent c := by
      rw [heq]
      exact add_le_add hdy (le_refl 1)
    have hlt : G.edist c y < G.eccent c :=
      ENat.add_one_le_iff (hm := hfin) (n := G.eccent c) |>.mp hstep
    refine ENat.coe_lt_coe.mp ?_
    rw [hcoe1, hcoee]
    exact hlt

/-! ### F5: deleting a leaf never raises the radius -/

/-- **F5.** If `z` is a leaf of a connected graph on at least three vertices,
then the radius restricted to the remaining vertices is at most the full
radius. -/
lemma radOn_erase_le_radOn_of_isLeaf {G : SimpleGraph α} (hconn : G.Connected)
    {z p : α} (hdeg : G.degree z = 1) (hzp : G.Adj z p)
    (hn3 : 3 ≤ Fintype.card α) :
    radOn G (Finset.univ.erase z) ≤ radOn G Finset.univ := by
  haveI : Nonempty α := ⟨z⟩
  obtain ⟨c, hc, hcmin⟩ := eccOn_eq_radOn_attained
    (G := G) (S := Finset.univ) (hS := Finset.univ_nonempty)
  have hcen : G.eccent c = G.radius := by
    rw [← eccOn_univ_eq_eccent, hcmin, radOn_univ_eq_radius]
  have hcz : c ≠ z := by
    haveI : Nonempty α := ⟨z⟩
    intro h
    rw [h] at hcen
    have hcor := radius_lt_eccOn_of_isLeaf hconn hdeg hzp hn3
    rw [eccOn_univ_eq_eccent (c := z), hcen] at hcor
    have hfin : G.radius ≠ ⊤ := by
      have h1 : G.radius ≤ G.eccent c := SimpleGraph.radius_le_eccent
      obtain ⟨t, ht⟩ := G.exists_edist_eq_eccent_of_finite c
      intro h
      rw [← ht, h] at h1
      exact absurd (eq_top_iff.mpr h1)
        (SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t))
    have hcoer : ((G.radius).toNat : ℕ∞) = G.radius := ENat.coe_toNat hfin
    have hnat : (1 : ℕ) + (G.radius).toNat ≤ (G.radius).toNat := by
      refine ENat.coe_le_coe.mp ?_
      have hstep : (((1 : ℕ) + (G.radius).toNat : ℕ) : ℕ∞) = 1 + G.radius := by
        rw [Nat.cast_add, hcoer]
        simp
      rw [hstep, hcoer]
      exact hcor
    omega
  have hmem : c ∈ Finset.univ.erase z := Finset.mem_erase.mpr ⟨hcz, Finset.mem_univ c⟩
  calc radOn G (Finset.univ.erase z) ≤ eccOn G (Finset.univ.erase z) c :=
      radOn_le_eccOn hmem
  _ ≤ eccOn G Finset.univ c := by
      refine eccOn_le (G := G) (S := Finset.univ.erase z) (c := c) (k := _) ?_
      intro x hx
      exact edist_le_eccOn (Finset.mem_univ x)
  _ = radOn G Finset.univ := by
      rw [eccOn_univ_eq_eccent, hcen, ← radOn_univ_eq_radius]


/-! ### The largest induced tree number t(G) -/

/-- `S` induces a connected subgraph: any two of its vertices are joined by a
walk staying inside `S`. -/
def ConnectsWithin (G : SimpleGraph α) (S : Finset α) (a b : α) : Prop :=
  ∃ w : G.Walk a b, ∀ z ∈ w.support, z ∈ S

/-- `S` induces a forest: no nontrivial cycle stays inside `S`. -/
def AcyclicWithin (G : SimpleGraph α) (S : Finset α) : Prop :=
  ∀ a : α, ∀ w : G.Walk a a,
    (∀ z ∈ w.support, z ∈ S) → w.length = 0 ∨ ¬ w.IsCycle

/-- `S` induces a tree: connected within `S`, and no cycle within `S`
(the empty and singleton sets count as trees here). -/
def IsInducedTree (G : SimpleGraph α) (S : Finset α) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, ConnectsWithin G S a b) ∧ AcyclicWithin G S

/-- The largest order of an induced tree. -/
noncomputable def treeNumber (G : SimpleGraph α) : ℕ :=
  (Finset.univ.filter (fun S : Finset α => IsInducedTree G S)).sup
    (fun S => S.card)

/-- **F14 (heredity).** Induced trees avoiding `v` are bounded by `t(G)`;
this is the ambient form of `t(G - v) ≤ t(G)`. -/
lemma treeNumber_mono_erase {G : SimpleGraph α} {v : α} :
    (Finset.univ.filter (fun S : Finset α =>
      IsInducedTree G S ∧ S ⊆ Finset.univ.erase v)).sup (fun S => S.card)
      ≤ treeNumber G := by
  refine Finset.sup_le ?_
  intro S hS
  obtain ⟨-, htree, -⟩ := Finset.mem_filter.mp hS
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ S, htree⟩)


/-! ### Batch 3b: geodesic structure (F1, F2, potential-function acyclicity) -/

/-- **F1a.** A walk realizing the distance has no repeated vertex: any repeat
could be cut out, shortening the walk below the distance. -/
theorem isPath_of_length_eq_dist {G : SimpleGraph α} (hconn : G.Connected)
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v) :
    p.IsPath := by
  rw [SimpleGraph.Walk.isPath_def, List.nodup_iff_count_le_one]
  intro z
  by_contra h1
  push_neg at h1
  have hm : z ∈ p.support := List.count_pos_iff.mp (by omega)
  have hsup : p.support = (p.takeUntil z hm).support ++
      (p.dropUntil z hm).support.tail := by
    conv_lhs => rw [← SimpleGraph.Walk.take_spec p hm]
    exact SimpleGraph.Walk.support_append _ _
  have hc1 : (p.takeUntil z hm).support.count z = 1 :=
    SimpleGraph.Walk.count_support_takeUntil_eq_one p hm
  have hcount : p.support.count z = 1 + (p.dropUntil z hm).support.tail.count z := by
    rw [hsup, List.count_append, hc1]
  have hrest : z ∈ (p.dropUntil z hm).support.tail :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨r, hrmem, hrlen⟩ :
      ∃ r : G.Walk z v, z ∈ r.support ∧ r.length < (p.dropUntil z hm).length := by
    cases hd : p.dropUntil z hm with
    | nil => rw [hd] at hrest; exact absurd hrest (by simp)
    | @cons z' x v'' h r =>
        rw [hd, SimpleGraph.Walk.support_cons, List.tail_cons] at hrest
        refine ⟨r.dropUntil z hrest, SimpleGraph.Walk.start_mem_support _, ?_⟩
        have h1 : (SimpleGraph.Walk.cons h r).length = r.length + 1 :=
          SimpleGraph.Walk.length_cons h r
        have h2 : (r.dropUntil z hrest).length = r.length - r.support.idxOf z :=
          SimpleGraph.Walk.length_dropUntil r hrest
        have h3 : r.support.idxOf z < r.support.length :=
          List.idxOf_lt_length_of_mem hrest
        rw [SimpleGraph.Walk.length_support] at h3
        rw [h1]
        omega
  have hq : (p.dropUntil z hm).length = p.length - p.support.idxOf z :=
    SimpleGraph.Walk.length_dropUntil p hm
  set w := (p.takeUntil z hm).append r with hwdef
  have hwlen : w.length = p.support.idxOf z + r.length := by
    rw [hwdef, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_takeUntil]
  have hrdist : G.dist u v ≤ w.length := SimpleGraph.dist_le w
  have hil := List.idxOf_lt_length_of_mem hm
  rw [SimpleGraph.Walk.length_support] at hil
  omega

/-- **F1b (chord exclusion).** If two vertices of a geodesic walk's support
are adjacent in `G`, their positions in the support differ by exactly one. -/
theorem geodesic_adj_support_succ {G : SimpleGraph α} (hconn : G.Connected)
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v)
    {a b : α} (ha : a ∈ p.support) (hb : b ∈ p.support) (hadj : G.Adj a b) :
    p.support.idxOf a + 1 = p.support.idxOf b ∨
      p.support.idxOf b + 1 = p.support.idxOf a := by
  by_cases hle : p.support.idxOf a ≤ p.support.idxOf b
  · left
    by_contra hne
    have hbmem : p.support.idxOf b ≤ p.length := by
      have := List.idxOf_lt_length_of_mem hb
      rw [SimpleGraph.Walk.length_support] at this
      omega
    have hna : a ≠ b := G.ne_of_adj hadj
    have hidx : p.support.idxOf a ≠ p.support.idxOf b := by
      intro heq
      exact hna ((SimpleGraph.Walk.getVert_support_idxOf p ha).symm.trans
        (heq ▸ SimpleGraph.Walk.getVert_support_idxOf p hb))
    have hib : p.support.idxOf a + 2 ≤ p.support.idxOf b := by
      by_contra hc
      push_neg at hc
      rcases Nat.eq_or_lt_of_le hc with h1' | h1'
      · exact hne (by omega)
      · exact hidx (le_antisymm hle (by omega))
    set w := ((p.takeUntil a ha).append (SimpleGraph.Adj.toWalk hadj)).append
      (p.dropUntil b hb) with hwdef
    have hwlen : w.length =
        p.support.idxOf a + 1 + (p.length - p.support.idxOf b) := by
      rw [hwdef, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_takeUntil, SimpleGraph.Walk.length_dropUntil]
      simp [SimpleGraph.Adj.toWalk]
    have hrdist : G.dist u v ≤ w.length := SimpleGraph.dist_le w
    omega
  · right
    by_contra hne
    have hle' : p.support.idxOf b ≤ p.support.idxOf a := (Nat.not_le.mp hle).le
    have hamem : p.support.idxOf a ≤ p.length := by
      have := List.idxOf_lt_length_of_mem ha
      rw [SimpleGraph.Walk.length_support] at this
      omega
    have hnb : b ≠ a := (G.ne_of_adj hadj).symm
    have hidx : p.support.idxOf b ≠ p.support.idxOf a := by
      intro heq
      exact hnb ((SimpleGraph.Walk.getVert_support_idxOf p hb).symm.trans
        (heq ▸ SimpleGraph.Walk.getVert_support_idxOf p ha))
    have hia : p.support.idxOf b + 2 ≤ p.support.idxOf a := by
      by_contra hc
      push_neg at hc
      rcases Nat.eq_or_lt_of_le hc with h1' | h1'
      · exact hne (by omega)
      · exact hidx (le_antisymm hle' (by omega))
    set w := ((p.takeUntil b hb).append (SimpleGraph.Adj.toWalk hadj.symm)).append
      (p.dropUntil a ha) with hwdef
    have hwlen : w.length =
        p.support.idxOf b + 1 + (p.length - p.support.idxOf a) := by
      rw [hwdef, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_takeUntil, SimpleGraph.Walk.length_dropUntil]
      simp [SimpleGraph.Adj.toWalk]
    have hrdist : G.dist u v ≤ w.length := SimpleGraph.dist_le w
    omega

end Graffiti84
