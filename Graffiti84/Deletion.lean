import Graffiti84.RootedChung

/-!
# Actual induced-subgraph radii

`radOn` restricts the ambient metric. It is only a lower bound on the
radius of the induced subgraph. These bridges allow genuine deletion-radius
hypotheses to be used by the existing UEP and rooted Chung lemmas.
-/

namespace Graffiti84

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma edist_le_induce_edist (G : SimpleGraph α) (S : Finset α)
    (x y : {v // v ∈ S}) :
    G.edist x.val y.val ≤ (G.induce (S : Set α)).edist x y := by
  refine le_iInf fun p => ?_
  have hle := SimpleGraph.edist_le
    (p.map (SimpleGraph.Embedding.induce (S : Set α)).toHom)
  rw [SimpleGraph.Walk.length_map] at hle
  exact hle

lemma eccOn_le_induce_eccent (G : SimpleGraph α) (S : Finset α)
    (c : {v // v ∈ S}) :
    eccOn G S c.val ≤ (G.induce (S : Set α)).eccent c := by
  refine eccOn_le fun x hx => ?_
  exact le_trans (edist_le_induce_edist G S c ⟨x, hx⟩)
    (G.induce (S : Set α)).edist_le_eccent

lemma radOn_le_induce_radius (G : SimpleGraph α) (S : Finset α) :
    radOn G S ≤ (G.induce (S : Set α)).radius := by
  rw [SimpleGraph.radius]
  refine le_iInf fun c => ?_
  exact le_trans (radOn_le_eccOn c.property) (eccOn_le_induce_eccent G S c)

/-- The converse radius-drop criterion with the actual deleted graph. -/
theorem isUniqueEccentricPoint_of_induce_radius_drop {G : SimpleGraph α}
    (hconn : G.Connected) {v : α} (h2 : 2 ≤ Fintype.card α)
    (hdrop : (G.induce (↑(Finset.univ.erase v) : Set α)).radius + 1 ≤ G.radius) :
    ∃ c, IsCentral G c ∧ IsUniqueEccentricPoint G c v := by
  apply isUniqueEccentricPoint_of_radOn_erase hconn h2
  rw [radOn_univ_eq_radius]
  exact le_trans (add_le_add (radOn_le_induce_radius G _) (le_refl 1)) hdrop

/-- Rooted Chung with a genuine vertex-deletion radius hypothesis. -/
theorem rooted_chung_of_induce_radius_drop {G : SimpleGraph α}
    (hconn : G.Connected) {a : α} (hr2 : 2 ≤ G.radius.toNat)
    (hdrop : (G.induce (↑(Finset.univ.erase a) : Set α)).radius + 1 ≤ G.radius) :
    ∃ S : Finset α, IsInducedTree G S ∧ a ∈ S ∧
      2 * G.radius.toNat - 1 ≤ S.card := by
  apply rooted_chung hconn hr2
  exact le_trans (add_le_add (radOn_le_induce_radius G _) (le_refl 1)) hdrop

/-- A shortest walk contained in an induced subgraph retains its length there. -/
lemma induce_edist_eq_of_shortest_walk {G : SimpleGraph α} {S : Finset α}
    (x y : {v // v ∈ S}) (p : G.Walk x.val y.val)
    (hp : (p.length : ℕ∞) = G.edist x.val y.val)
    (hmem : ∀ z ∈ p.support, z ∈ S) :
    (G.induce (S : Set α)).edist x y = G.edist x.val y.val := by
  refine le_antisymm ?_ (edist_le_induce_edist G S x y)
  have hlen : (p.induce (S : Set α) hmem).length = p.length := by
    have hm := SimpleGraph.Walk.length_map
      (SimpleGraph.Embedding.induce (S : Set α)).toHom (p.induce (S : Set α) hmem)
    rw [SimpleGraph.Walk.map_induce] at hm
    exact hm.symm
  let q : (G.induce (S : Set α)).Walk x y :=
    (p.induce (S : Set α) hmem).copy (Subtype.ext rfl) (Subtype.ext rfl)
  calc
    (G.induce (S : Set α)).edist x y ≤ (q.length : ℕ∞) := SimpleGraph.edist_le q
    _ = (p.length : ℕ∞) := by
      dsimp only [q]
      rw [SimpleGraph.Walk.length_copy, hlen]
    _ = G.edist x.val y.val := hp

/-- F7 for the actual deleted graph, not merely the restricted ambient metric. -/
theorem induce_radius_drop_of_central_uep {G : SimpleGraph α} [Nontrivial α]
    (hconn : G.Connected) {c v : α}
    (hc : IsCentral G c) (huep : IsUniqueEccentricPoint G c v) :
    (G.induce (↑(Finset.univ.erase v) : Set α)).radius + 1 ≤ G.radius := by
  have hcv := edist_eq_eccent_of_isUniqueEccentricPoint hconn huep
  have hcne : c ≠ v := by
    intro h
    rw [h, SimpleGraph.edist_self] at hcv
    exact G.eccent_ne_zero v hcv.symm
  let S : Finset α := Finset.univ.erase v
  let cS : {x // x ∈ S} := ⟨c, Finset.mem_erase.mpr ⟨hcne, Finset.mem_univ c⟩⟩
  have hmetric : ∀ x : {x // x ∈ S},
      (G.induce (S : Set α)).edist cS x = G.edist c x.val := by
    intro x
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_edist c x.val
    apply induce_edist_eq_of_shortest_walk cS x p hp
    intro z hz
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ z⟩
    intro hzv
    have hsum := edist_add_edist_le_of_mem_support (p := p) (hzv ▸ hz)
    have hle : G.edist c v ≤ G.edist c x.val := by
      calc
        G.edist c v ≤ G.edist c v + G.edist v x.val := le_self_add
        _ ≤ (p.length : ℕ∞) := hsum
        _ = G.edist c x.val := hp
    rw [hcv] at hle
    have hxv : x.val ≠ v := (Finset.mem_erase.mp x.property).1
    exact (not_le_of_gt (edist_lt_eccent_of_dist_lt hconn (huep.2 x.val hxv))) hle
  obtain ⟨x, hx⟩ := (G.induce (S : Set α)).exists_edist_eq_eccent_of_finite cS
  have hetop : G.eccent c ≠ ⊤ := by
    obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite c
    rw [← hw]
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c w)
  have hxv : x.val ≠ v := (Finset.mem_erase.mp x.property).1
  calc
    (G.induce (S : Set α)).radius + 1 ≤ (G.induce (S : Set α)).eccent cS + 1 :=
      add_le_add (G.induce (S : Set α)).radius_le_eccent (le_refl 1)
    _ = G.edist c x.val + 1 := by rw [← hx, hmetric]
    _ ≤ G.eccent c := (ENat.add_one_le_iff' (hn := hetop)).mpr
      (edist_lt_eccent_of_dist_lt hconn (huep.2 x.val hxv))
    _ = G.radius := hc

/-- Deleting a leaf preserves the metric on the surviving vertices. -/
theorem induce_edist_eq_of_isLeaf {G : SimpleGraph α} (hconn : G.Connected)
    {u : α} (hu : G.degree u = 1)
    (x y : {v // v ∈ Finset.univ.erase u}) :
    (G.induce (↑(Finset.univ.erase u) : Set α)).edist x y = G.edist x.val y.val := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x.val y.val
  have havoid := path_avoids_leaf hu (isPath_of_length_eq_dist hconn hp)
    (Finset.mem_erase.mp x.property).1 (Finset.mem_erase.mp y.property).1
  apply induce_edist_eq_of_shortest_walk x y p
  · rw [hp]
    exact ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
      (hconn.preconnected x.val y.val))
  · intro z hz
    exact Finset.mem_erase.mpr ⟨fun hzu => havoid (hzu ▸ hz), Finset.mem_univ z⟩

/-- For leaf deletion, unlike general deletion, restricted and induced
eccentricities agree. -/
theorem eccOn_erase_eq_induce_eccent_of_isLeaf {G : SimpleGraph α}
    (hconn : G.Connected) {u : α} (hu : G.degree u = 1)
    (c : {v // v ∈ Finset.univ.erase u}) :
    eccOn G (Finset.univ.erase u) c.val =
      (G.induce (↑(Finset.univ.erase u) : Set α)).eccent c := by
  refine le_antisymm (eccOn_le_induce_eccent G _ c) ?_
  rw [SimpleGraph.eccent]
  refine iSup_le fun x => ?_
  rw [induce_edist_eq_of_isLeaf hconn hu c x]
  exact edist_le_eccOn x.property

/-- The ambient deletion radius equals the actual deletion radius for leaves. -/
theorem radOn_erase_eq_induce_radius_of_isLeaf {G : SimpleGraph α}
    (hconn : G.Connected) {u : α} (hu : G.degree u = 1) :
    radOn G (Finset.univ.erase u) =
      (G.induce (↑(Finset.univ.erase u) : Set α)).radius := by
  refine le_antisymm (radOn_le_induce_radius G _) ?_
  unfold radOn
  refine le_iInf₂ fun c hc => ?_
  rw [eccOn_erase_eq_induce_eccent_of_isLeaf hconn hu ⟨c, hc⟩]
  exact (G.induce (↑(Finset.univ.erase u) : Set α)).radius_le_eccent

/-- The walk-based deletion predicate agrees with actual induced connectivity. -/
theorem connected_induce_erase_iff {G : SimpleGraph α} [Nontrivial α] (v : α) :
    (G.induce (↑(Finset.univ.erase v) : Set α)).Connected ↔ DeleteConnected G v := by
  let S : Finset α := Finset.univ.erase v
  let f := (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom
  constructor
  · intro hconn x y hx hy
    let xS : {z // z ∈ S} := ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩⟩
    let yS : {z // z ∈ S} := ⟨y, Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩⟩
    obtain ⟨p⟩ := hconn.preconnected xS yS
    refine ⟨p.map f, ?_⟩
    intro hmem
    rw [SimpleGraph.Walk.support_map f p] at hmem
    obtain ⟨z, _, hz⟩ := List.mem_map.mp hmem
    exact (Finset.mem_erase.mp z.property).1 hz
  · intro hdel
    obtain ⟨x, hx⟩ := exists_ne v
    haveI : Nonempty {z // z ∈ S} :=
      ⟨⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩⟩⟩
    refine ⟨?_, inferInstance⟩
    intro x y
    obtain ⟨p, hp⟩ := hdel x.val y.val
      (Finset.mem_erase.mp x.property).1 (Finset.mem_erase.mp y.property).1
    refine ⟨p.induce (S : Set α) ?_⟩
    intro z hz
    exact Finset.mem_erase.mpr ⟨fun hzv => hp (hzv ▸ hz), Finset.mem_univ z⟩

/-- The original graph's radius is at most the actual deleted radius plus one. -/
theorem radius_le_induce_radius_add_one {G : SimpleGraph α} [Nontrivial α]
    (hconn : G.Connected) (v : α) :
    G.radius ≤ (G.induce (↑(Finset.univ.erase v) : Set α)).radius + 1 := by
  obtain ⟨w, hvw⟩ := hconn.preconnected.exists_adj_of_nontrivial v
  have h := radOn_le_radOn_erase_add_one (Finset.mem_univ v) hconn
    ⟨w, Finset.mem_univ w, hvw.ne.symm, hvw⟩
  rw [radOn_univ_eq_radius] at h
  exact le_trans h (add_le_add (radOn_le_induce_radius G _) (le_refl 1))

/-- Deleting a leaf does not increase the actual radius (at least three vertices). -/
theorem induce_radius_le_of_isLeaf {G : SimpleGraph α} (hconn : G.Connected)
    {u a : α} (hu : G.degree u = 1) (hua : G.Adj u a)
    (hn3 : 3 ≤ Fintype.card α) :
    (G.induce (↑(Finset.univ.erase u) : Set α)).radius ≤ G.radius := by
  rw [← radOn_erase_eq_induce_radius_of_isLeaf hconn hu]
  simpa only [radOn_univ_eq_radius] using radOn_erase_le_radOn_of_isLeaf hconn hu hua hn3

end Graffiti84
