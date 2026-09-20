import Graffiti84.BasicFacts

namespace Graffiti84

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A tree induced inside an induced subgraph is induced in the original graph. -/
theorem isInducedTree_image_induce {G : SimpleGraph α} {S : Finset α}
    {T : Finset {v // v ∈ S}} (hT : IsInducedTree (G.induce (S : Set α)) T) :
    IsInducedTree G (T.image Subtype.val) := by
  let f := (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom
  constructor
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨p, hp⟩ := hT.1 a' ha' b' hb'
    refine ⟨(p.map f).copy rfl rfl, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map f p] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact Finset.mem_image.mpr ⟨w, hp w hw, rfl⟩
  · intro a p hp
    right
    intro hcycle
    have hmem : ∀ z ∈ p.support, z ∈ S := by
      intro z hz
      obtain ⟨w, _, hw⟩ := Finset.mem_image.mp (hp z hz)
      exact hw ▸ w.property
    let q := p.induce (S : Set α) hmem
    have hmap : q.map f = p := SimpleGraph.Walk.map_induce p hmem
    have hq : q.IsCycle := SimpleGraph.Walk.IsCycle.of_map (f := f) (by
      rw [hmap]
      exact hcycle)
    have hinside : ∀ z ∈ q.support, z ∈ T := by
      intro z hz
      have hzmap : z.val ∈ (q.map f).support := by
        rw [SimpleGraph.Walk.support_map f q]
        exact List.mem_map.mpr ⟨z, hz, rfl⟩
      rw [hmap] at hzmap
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp (hp z.val hzmap)
      have he : w = z := Subtype.ext hwz
      exact he ▸ hw
    rcases hT.2 _ q hinside with hzero | hnot
    · have := hq.three_le_length
      omega
    · exact hnot hq

/-- The largest induced-tree order is monotone under taking induced subgraphs. -/
theorem treeNumber_induce_le (G : SimpleGraph α) (S : Finset α) :
    treeNumber (G.induce (S : Set α)) ≤ treeNumber G := by
  unfold treeNumber
  refine Finset.sup_le fun T hT => ?_
  have ht := (Finset.mem_filter.mp hT).2
  have himage := isInducedTree_image_induce ht
  have hcard : (T.image Subtype.val).card = T.card :=
    Finset.card_image_of_injective T Subtype.val_injective
  rw [← hcard]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, himage⟩)

end Graffiti84
