import Graffiti84.InducedTree
import Graffiti84.EndBlocks

namespace Graffiti84

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Attaching a vertex with just one neighbour in an induced tree preserves it. -/
theorem isInducedTree_insert_of_unique_neighbor {G : SimpleGraph α}
    {S : Finset α} {u a : α} (hS : IsInducedTree G S) (ha : a ∈ S)
    (hua : G.Adj u a) (hunique : ∀ z ∈ S, G.Adj u z → z = a) :
    IsInducedTree G (insert u S) := by
  have reach : ∀ z ∈ insert u S, ConnectsWithin G (insert u S) z a := by
    intro z hz
    rcases Finset.mem_insert.mp hz with he | hzS
    · subst z
      refine ⟨hua.toWalk, ?_⟩
      intro z hz
      simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with he | he
      · rw [he]; exact Finset.mem_insert_self _ _
      · rw [he]; exact Finset.mem_insert_of_mem ha
    · obtain ⟨p, hp⟩ := hS.1 z hzS a ha
      exact ⟨p, fun x hx => Finset.mem_insert_of_mem (hp x hx)⟩
  constructor
  · intro x hx y hy
    obtain ⟨p, hp⟩ := reach x hx
    obtain ⟨q, hq⟩ := reach y hy
    refine ⟨p.append q.reverse, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hz
    exact hz.elim (hp z) (hq z)
  · intro x p hp
    right
    intro hcycle
    have havoid : u ∉ p.support := by
      intro hu
      let q := p.rotate u hu
      have hq : q.IsCycle := hcycle.rotate hu
      have hins : ∀ z ∈ q.support, z ∈ insert u S := by
        intro z hz
        exact hp z ((p.mem_support_rotate_iff u hu).mp hz)
      have hadj1 : G.Adj u q.snd := q.adj_snd hq.not_nil
      have hadj2 : G.Adj u q.penultimate := (q.adj_penultimate hq.not_nil).symm
      have hsnd : q.snd ∈ S := (Finset.mem_insert.mp
        (hins q.snd (q.getVert_mem_support 1))).resolve_left hadj1.ne.symm
      have hpen : q.penultimate ∈ S := (Finset.mem_insert.mp
        (hins q.penultimate (q.getVert_mem_support (q.length - 1)))).resolve_left hadj2.ne.symm
      exact hq.snd_ne_penultimate ((hunique _ hsnd hadj1).trans (hunique _ hpen hadj2).symm)
    have hins : ∀ z ∈ p.support, z ∈ S := by
      intro z hz
      exact (Finset.mem_insert.mp (hp z hz)).resolve_left (fun he => havoid (he ▸ hz))
    rcases hS.2 x p hins with hzero | hnot
    · have := hcycle.three_le_length
      omega
    · exact hnot hcycle

theorem connected_induce_of_isInducedTree {G : SimpleGraph α} {S : Finset α}
    (hS : IsInducedTree G S) (hne : S.Nonempty) : (G.induce (S : Set α)).Connected := by
  obtain ⟨a, ha⟩ := hne
  haveI : Nonempty {v // v ∈ S} := ⟨⟨a, ha⟩⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨p, hp⟩ := hS.1 x.val x.property y.val y.property
  exact ⟨(p.induce (S : Set α) hp).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

theorem exists_maximum_induced_tree (G : SimpleGraph α) :
    ∃ S, IsInducedTree G S ∧ S.card = treeNumber G := by
  have he : IsInducedTree G ∅ := by
    constructor
    · intro x hx; exact (Finset.notMem_empty x hx).elim
    · intro x p hp
      exact (Finset.notMem_empty x (hp x p.start_mem_support)).elim
  have hne : (Finset.univ.filter (fun S : Finset α => IsInducedTree G S)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_mem_eq_sup _ hne (fun S : Finset α => S.card)
  exact ⟨S, (Finset.mem_filter.mp hS).2, hmax.symm⟩

/-- If every neighbour of `x` can reach a fixed surviving vertex without
passing through `x`, then `x` is non-cut. -/
lemma deleteConnected_of_neighbors_reach {G : SimpleGraph α} (hconn : G.Connected)
    {x t : α} (hreach : ∀ y, G.Adj x y → ∃ p : G.Walk y t, x ∉ p.support) :
    DeleteConnected G x := by
  have reach : ∀ a, a ≠ x → ∃ p : G.Walk a t, x ∉ p.support := by
    intro a hax
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a x
    have hpne : ¬p.Nil := fun he => hax he.eq
    have hpath := isPath_of_length_eq_dist hconn hp
    have havoid : x ∉ p.dropLast.support := by
      intro hx
      have hnd := hpath.support_nodup
      rw [← SimpleGraph.Walk.support_dropLast_concat hpne] at hnd
      exact (List.nodup_append'.mp hnd).2.2 hx (List.mem_singleton.mpr rfl)
    obtain ⟨q, hq⟩ := hreach p.penultimate (p.adj_penultimate hpne).symm
    refine ⟨p.dropLast.append q, ?_⟩
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact not_or.mpr ⟨havoid, hq⟩
  intro a b ha hb
  obtain ⟨p, hp⟩ := reach a ha
  obtain ⟨q, hq⟩ := reach b hb
  refine ⟨p.append q.reverse, ?_⟩
  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
    List.mem_reverse]
  exact not_or.mpr ⟨hp, hq⟩

/-- A non-cut vertex of a maximum induced tree is non-cut in the whole graph. -/
theorem noncut_of_maximum_induced_tree {G : SimpleGraph α} (hconn : G.Connected)
    {S : Finset α} (hS : IsInducedTree G S) (hmax : S.card = treeNumber G)
    (x t : {v // v ∈ S}) (hxt : x ≠ t)
    (hx : DeleteConnected (G.induce (S : Set α)) x) : DeleteConnected G x.val := by
  let f := (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom
  have inside : ∀ z : {v // v ∈ S}, z ≠ x →
      ∃ p : G.Walk z.val t.val, x.val ∉ p.support := by
    intro z hzx
    obtain ⟨p, hp⟩ := hx z t hzx hxt.symm
    refine ⟨(p.map f).copy rfl rfl, ?_⟩
    intro hm
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map f p] at hm
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hm
    exact hp ((Subtype.ext he : w = x) ▸ hw)
  apply deleteConnected_of_neighbors_reach hconn (t := t.val)
  intro y hxy
  by_cases hyS : y ∈ S
  · exact inside ⟨y, hyS⟩ (fun he => hxy.ne (congrArg Subtype.val he).symm)
  · by_cases hother : ∃ z ∈ S, z ≠ x.val ∧ G.Adj y z
    · obtain ⟨z, hzS, hzx, hyz⟩ := hother
      obtain ⟨p, hp⟩ := inside ⟨z, hzS⟩ (fun he => hzx (congrArg Subtype.val he))
      refine ⟨SimpleGraph.Walk.cons hyz p, ?_⟩
      rw [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact not_or.mpr ⟨hxy.ne, hp⟩
    · have huniq : ∀ z ∈ S, G.Adj y z → z = x.val := by
        intro z hz hyz
        by_contra hne
        exact hother ⟨z, hz, hne, hyz⟩
      have ht := isInducedTree_insert_of_unique_neighbor hS x.property hxy.symm huniq
      have hbound : (insert y S).card ≤ treeNumber G :=
        Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
      rw [Finset.card_insert_of_notMem hyS, ← hmax] at hbound
      omega

/-- A maximum induced tree in a nontrivial connected graph contains two
distinct vertices that are non-cut in the original graph. -/
theorem exists_maximum_tree_two_noncut {G : SimpleGraph α} [Nontrivial α]
    (hconn : G.Connected) :
    ∃ S : Finset α, IsInducedTree G S ∧ S.card = treeNumber G ∧
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ DeleteConnected G x ∧ DeleteConnected G y := by
  obtain ⟨S, hS, hmax⟩ := exists_maximum_induced_tree G
  obtain ⟨u⟩ := hconn.nonempty
  obtain ⟨v, hvu⟩ := exists_ne u
  have hpos := hconn.pos_dist_of_ne hvu.symm
  have ht := treeNumber_ge_dist_add_one hconn u v
  have hcard : 2 ≤ S.card := by omega
  haveI : Nontrivial {v // v ∈ S} := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa using (show 1 < S.card by omega))
  have hH := connected_induce_of_isInducedTree hS (Finset.card_pos.mp (by omega))
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_two_deleteConnected hH
  refine ⟨S, hS, hmax, x.val, x.property, y.val, y.property,
    fun he => hxy (Subtype.ext he), ?_, ?_⟩
  · exact noncut_of_maximum_induced_tree hconn hS hmax x y hxy hx
  · exact noncut_of_maximum_induced_tree hconn hS hmax y x hxy.symm hy

end Graffiti84
