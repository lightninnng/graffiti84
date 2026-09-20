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
  simpa using SimpleGraph.edist_le
    (p.map (SimpleGraph.Embedding.induce (S : Set α)).toHom)

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

end Graffiti84
