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

end Graffiti84
