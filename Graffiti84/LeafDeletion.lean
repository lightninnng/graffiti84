import Graffiti84.LeafCore

namespace Graffiti84

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- An original leaf remains a leaf in any induced graph retaining its neighbour. -/
theorem degree_one_induce_of_isLeaf {G : SimpleGraph α} {S : Finset α}
    {u a : α} (hu : G.degree u = 1) (hua : G.Adj u a)
    (huS : u ∈ S) (haS : a ∈ S) :
    (G.induce (S : Set α)).degree ⟨u, huS⟩ = 1 := by
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨⟨a, haS⟩, hua, ?_⟩
  intro z hz
  apply Subtype.ext
  exact (adj_eq_of_degree_eq_one (G := G) hu hua hz).symm

/-- Adding back an attached vertex preserves non-cutness away from its parent. -/
theorem deleteConnected_lift_leaf {G : SimpleGraph α} {u a : α}
    (hua : G.Adj u a) (w : {v // v ∈ Finset.univ.erase u}) (hwa : w.val ≠ a)
    (hw : DeleteConnected (G.induce (↑(Finset.univ.erase u) : Set α)) w) :
    DeleteConnected G w.val := by
  let S : Finset α := Finset.univ.erase u
  have attach : ∀ x, x ≠ w.val → ∃ z : {v // v ∈ S}, z ≠ w ∧
      ∃ p : G.Walk x z.val, w.val ∉ p.support := by
    intro x hxw
    by_cases hxu : x = u
    · subst x
      refine ⟨⟨a, Finset.mem_erase.mpr ⟨hua.ne.symm, Finset.mem_univ a⟩⟩,
        fun he => hwa (congrArg Subtype.val he).symm, hua.toWalk, ?_⟩
      simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false]
      exact not_or.mpr ⟨hxw.symm, hwa⟩
    · refine ⟨⟨x, Finset.mem_erase.mpr ⟨hxu, Finset.mem_univ x⟩⟩,
        fun he => hxw (congrArg Subtype.val he), SimpleGraph.Walk.nil, ?_⟩
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hxw.symm
  intro x y hx hy
  obtain ⟨b, hbw, p, hp⟩ := attach x hx
  obtain ⟨c, hcw, r, hr⟩ := attach y hy
  obtain ⟨q, hq⟩ := hw b c hbw hcw
  let f := (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom
  let qG : G.Walk b.val c.val := (q.map f).copy rfl rfl
  have hqG : w.val ∉ qG.support := by
    intro hm
    dsimp only [qG] at hm
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map f q] at hm
    obtain ⟨z, hz, he⟩ := List.mem_map.mp hm
    exact hq ((Subtype.ext he : z = w) ▸ hz)
  refine ⟨(p.append qG).append r.reverse, ?_⟩
  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  exact not_or.mpr ⟨not_or.mpr ⟨hp, hqG⟩, hr⟩

/-- When deleting a leaf preserves radius, central UEP witnesses at surviving
vertices transfer to the actual deleted graph. -/
theorem central_uep_after_leaf_deletion {G : SimpleGraph α} (hconn : G.Connected)
    (hn3 : 3 ≤ Fintype.card α) {u : α} (hu : G.degree u = 1)
    (hrad : (G.induce (↑(Finset.univ.erase u) : Set α)).radius = G.radius)
    (w : {v // v ∈ Finset.univ.erase u}) {c : α}
    (hc : IsCentral G c) (hcw : IsUniqueEccentricPoint G c w.val) :
    ∃ d, IsCentral (G.induce (↑(Finset.univ.erase u) : Set α)) d ∧
      IsUniqueEccentricPoint (G.induce (↑(Finset.univ.erase u) : Set α)) d w := by
  have hcS := central_mem_nonleafSet hconn hn3 hc
  have hcu : c ≠ u := by
    intro he
    exact mem_nonleafSet.mp hcS (he.symm ▸ hu)
  let H := G.induce (↑(Finset.univ.erase u) : Set α)
  let d : {v // v ∈ Finset.univ.erase u} :=
    ⟨c, Finset.mem_erase.mpr ⟨hcu, Finset.mem_univ c⟩⟩
  have hmetric : ∀ x, H.edist d x = G.edist c x.val :=
    fun x => induce_edist_eq_of_isLeaf hconn hu d x
  have hdist : ∀ x, H.dist d x = G.dist c x.val :=
    fun x => congrArg ENat.toNat (hmetric x)
  have hcentral : IsCentral H d := by
    apply le_antisymm _ H.radius_le_eccent
    rw [SimpleGraph.eccent]
    refine iSup_le fun x => ?_
    rw [hmetric, hrad, ← hc]
    exact G.edist_le_eccent
  refine ⟨d, hcentral, ?_, ?_⟩
  · rw [hdist, hcw.1, hc, show H.eccent d = H.radius from hcentral, hrad]
  · intro x hxw
    have hne : x.val ≠ w.val := fun he => hxw (Subtype.ext he)
    have hlt := hcw.2 x.val hne
    rw [hdist, show H.eccent d = H.radius from hcentral, hrad, ← hc]
    exact hlt

end Graffiti84
