import Graffiti84.Deletion
import Graffiti84.EndBlocks

namespace Graffiti84

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The vertices remaining after simultaneously removing all leaves. -/
noncomputable def nonleafSet (G : SimpleGraph α) : Finset α :=
  Finset.univ.filter (fun v => G.degree v ≠ 1)

lemma mem_nonleafSet {G : SimpleGraph α} {v : α} :
    v ∈ nonleafSet G ↔ G.degree v ≠ 1 := by
  simp [nonleafSet]

lemma leaf_parent_mem_nonleafSet {G : SimpleGraph α} (hconn : G.Connected)
    (hn3 : 3 ≤ Fintype.card α) {u a : α} (hu : G.degree u = 1) (hua : G.Adj u a) :
    a ∈ nonleafSet G := by
  apply mem_nonleafSet.mpr
  intro ha
  exact isCut_of_isLeaf hu hua hua.ne hn3 (deleteConnected_of_isLeaf hconn ha)

/-- Every path between non-leaves stays in the non-leaf core. -/
lemma path_mem_nonleafSet {G : SimpleGraph α}
    {x y : α} (hx : x ∈ nonleafSet G) (hy : y ∈ nonleafSet G)
    {p : G.Walk x y} (hp : p.IsPath) : ∀ z ∈ p.support, z ∈ nonleafSet G := by
  intro z hz
  apply mem_nonleafSet.mpr
  intro hleaf
  have hxz : x ≠ z := by
    intro he
    exact mem_nonleafSet.mp hx (he.symm ▸ hleaf)
  have hyz : y ≠ z := by
    intro he
    exact mem_nonleafSet.mp hy (he.symm ▸ hleaf)
  exact path_avoids_leaf hleaf hp hxz hyz hz

/-- Simultaneous leaf deletion preserves all distances in the core. -/
theorem nonleaf_induce_edist {G : SimpleGraph α} (hconn : G.Connected)
    (x y : {v // v ∈ nonleafSet G}) :
    (G.induce (nonleafSet G : Set α)).edist x y = G.edist x.val y.val := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x.val y.val
  apply induce_edist_eq_of_shortest_walk x y p
  · rw [hp]
    exact ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
      (hconn.preconnected x.val y.val))
  · exact path_mem_nonleafSet x.property y.property (isPath_of_length_eq_dist hconn hp)

theorem nonleaf_induce_connected {G : SimpleGraph α} (hconn : G.Connected)
    (hS : (nonleafSet G).Nonempty) : (G.induce (nonleafSet G : Set α)).Connected := by
  obtain ⟨c, hc⟩ := hS
  haveI : Nonempty {v // v ∈ nonleafSet G} := ⟨⟨c, hc⟩⟩
  refine ⟨?_⟩
  intro x y
  apply SimpleGraph.edist_ne_top_iff_reachable.mp
  rw [nonleaf_induce_edist hconn]
  exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected x.val y.val)

/-- A central vertex is not a leaf in a graph on at least three vertices. -/
lemma central_mem_nonleafSet {G : SimpleGraph α} (hconn : G.Connected)
    (hn3 : 3 ≤ Fintype.card α) {c : α} (hc : IsCentral G c) : c ∈ nonleafSet G := by
  apply mem_nonleafSet.mpr
  intro hleaf
  obtain ⟨a, hca⟩ := (G.degree_pos_iff_exists_adj c).mp (by omega)
  have h := radius_lt_eccOn_of_isLeaf hconn hleaf hca hn3
  rw [eccOn_univ_eq_eccent, hc, add_comm] at h
  have hrtop : G.radius ≠ ⊤ := by
    obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite c
    rw [← hc, ← hw]
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c w)
  exact (lt_irrefl G.radius) ((ENat.add_one_le_iff' (hn := hrtop)).mp h)

/-- Deleting all leaves lowers the radius by at most one. -/
theorem radius_le_nonleaf_radius_add_one {G : SimpleGraph α} (hconn : G.Connected)
    (hn3 : 3 ≤ Fintype.card α) (hS : (nonleafSet G).Nonempty) :
    G.radius ≤ (G.induce (nonleafSet G : Set α)).radius + 1 := by
  obtain ⟨c₀, hc₀⟩ := hS
  haveI : Nonempty {v // v ∈ nonleafSet G} := ⟨⟨c₀, hc₀⟩⟩
  obtain ⟨c, hc⟩ := (G.induce (nonleafSet G : Set α)).exists_eccent_eq_radius
  have hdist : ∀ x : {v // v ∈ nonleafSet G},
      G.edist c.val x.val ≤ (G.induce (nonleafSet G : Set α)).radius := by
    intro x
    rw [← nonleaf_induce_edist hconn c x, ← hc]
    exact (G.induce (nonleafSet G : Set α)).edist_le_eccent
  apply le_trans (G.radius_le_eccent (u := c.val))
  rw [SimpleGraph.eccent]
  refine iSup_le fun x => ?_
  by_cases hx : x ∈ nonleafSet G
  · exact le_trans (hdist ⟨x, hx⟩) le_self_add
  · have hleaf : G.degree x = 1 := by
      by_contra hn
      exact hx (mem_nonleafSet.mpr hn)
    obtain ⟨a, hxa⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
    have ha := leaf_parent_mem_nonleafSet hconn hn3 hleaf hxa
    calc
      G.edist c.val x ≤ G.edist c.val a + 1 :=
        edist_le_add_edge (hconn.preconnected c.val a) hxa.symm
      _ ≤ (G.induce (nonleafSet G : Set α)).radius + 1 :=
        add_le_add (hdist ⟨a, ha⟩) (le_refl 1)

/-- In the radius-decreasing setting, simultaneous leaf deletion lowers
the actual radius by exactly one. -/
theorem radius_eq_nonleaf_radius_add_one {G : SimpleGraph α} (hconn : G.Connected)
    (hn3 : 3 ≤ Fintype.card α) {u : α} (hu : G.degree u = 1)
    (hdrop : radOn G (Finset.univ.erase u) + 1 ≤ G.radius) :
    G.radius = (G.induce (nonleafSet G : Set α)).radius + 1 := by
  obtain ⟨c, hc, hcu⟩ := isUniqueEccentricPoint_of_radOn_erase hconn (by omega)
    (by simpa only [radOn_univ_eq_radius] using hdrop)
  have hcS := central_mem_nonleafSet hconn hn3 hc
  let cS : {v // v ∈ nonleafSet G} := ⟨c, hcS⟩
  refine le_antisymm (radius_le_nonleaf_radius_add_one hconn hn3 ⟨c, hcS⟩) ?_
  obtain ⟨x, hx⟩ := (G.induce (nonleafSet G : Set α)).exists_edist_eq_eccent_of_finite cS
  have hxu : x.val ≠ u := by
    intro he
    exact mem_nonleafSet.mp x.property (he.symm ▸ hu)
  have hetop : G.eccent c ≠ ⊤ := by
    obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite c
    rw [← hw]
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c w)
  calc
    (G.induce (nonleafSet G : Set α)).radius + 1 ≤
        (G.induce (nonleafSet G : Set α)).eccent cS + 1 :=
      add_le_add (G.induce (nonleafSet G : Set α)).radius_le_eccent (le_refl 1)
    _ = G.edist c x.val + 1 := by rw [← hx, nonleaf_induce_edist hconn]; rfl
    _ ≤ G.eccent c := (ENat.add_one_le_iff' (hn := hetop)).mpr
      (edist_lt_eccent_of_dist_lt hconn (hcu.2 x.val hxu))
    _ = G.radius := hc

/-- Every core vertex is a cut vertex in a vrd graph with a cut vertex. -/
lemma isCut_of_mem_nonleafSet {G : SimpleGraph α} [Nontrivial α]
    (hconn : G.Connected)
    (hmono : ∀ z, DeleteConnected G z →
      radOn G (Finset.univ.erase z) + 1 ≤ radOn G Finset.univ)
    (hcut : ∃ a, IsCut G a) {w : α} (hw : w ∈ nonleafSet G) : IsCut G w := by
  haveI : Nonempty α := ⟨w⟩
  intro hdel
  exact mem_nonleafSet.mp hw (degree_eq_one_of_nonCut_of_hasCut hconn hmono hcut hdel)

/-- A non-cut vertex of the core has a leaf attached in the original graph. -/
theorem core_noncut_has_leaf {G : SimpleGraph α} [Nontrivial α]
    (hconn : G.Connected) (hn3 : 3 ≤ Fintype.card α)
    (hmono : ∀ z, DeleteConnected G z →
      radOn G (Finset.univ.erase z) + 1 ≤ radOn G Finset.univ)
    (hcut : ∃ a, IsCut G a) (w : {v // v ∈ nonleafSet G})
    (hw : DeleteConnected (G.induce (nonleafSet G : Set α)) w) :
    ∃ u, G.degree u = 1 ∧ G.Adj u w.val := by
  by_contra hbad
  have hno : ∀ u, G.degree u = 1 → ¬G.Adj u w.val := by
    intro u hu huw
    exact hbad ⟨u, hu, huw⟩
  have attach : ∀ x, x ≠ w.val → ∃ a : {v // v ∈ nonleafSet G}, a ≠ w ∧
      ∃ p : G.Walk x a.val, w.val ∉ p.support := by
    intro x hxw
    by_cases hx : x ∈ nonleafSet G
    · refine ⟨⟨x, hx⟩, fun he => hxw (congrArg Subtype.val he),
        SimpleGraph.Walk.nil, ?_⟩
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hxw.symm
    · have hleaf : G.degree x = 1 := by
        by_contra hn
        exact hx (mem_nonleafSet.mpr hn)
      obtain ⟨a, hxa⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
      have ha := leaf_parent_mem_nonleafSet hconn hn3 hleaf hxa
      have haw : a ≠ w.val := by
        intro he
        exact hno x hleaf (he ▸ hxa)
      refine ⟨⟨a, ha⟩, fun he => haw (congrArg Subtype.val he), hxa.toWalk, ?_⟩
      simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false]
      exact not_or.mpr ⟨hxw.symm, haw.symm⟩
  apply isCut_of_mem_nonleafSet hconn hmono hcut w.property
  intro x y hx hy
  obtain ⟨a, haw, p, hp⟩ := attach x hx
  obtain ⟨b, hbw, r, hr⟩ := attach y hy
  obtain ⟨q, hq⟩ := hw a b haw hbw
  let f := (SimpleGraph.Embedding.induce (G := G) (nonleafSet G : Set α)).toHom
  have hqmap : w.val ∉ (q.map f).support := by
    intro hm
    rw [SimpleGraph.Walk.support_map f q] at hm
    obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hm
    exact hq ((Subtype.ext hzw : z = w) ▸ hz)
  refine ⟨(p.append (q.map f)).append r.reverse, ?_⟩
  intro hm
  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] at hm
  exact hm.elim (fun h => h.elim hp hqmap) hr

end Graffiti84
