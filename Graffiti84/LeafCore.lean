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
    _ = G.edist c x.val + 1 := by rw [← hx, nonleaf_induce_edist hconn]
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
  let qG : G.Walk a.val b.val := (q.map f).copy rfl rfl
  have hqmap : w.val ∉ qG.support := by
    intro hm
    dsimp only [qG] at hm
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map f q] at hm
    obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hm
    exact hq ((Subtype.ext hzw : z = w) ▸ hz)
  refine ⟨(p.append qG).append r.reverse, ?_⟩
  intro hm
  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] at hm
  exact hm.elim (fun h => h.elim hp hqmap) hr

/-- A vertex on the penultimate distance layer is non-cut when the unique
farthest vertex has a neighbour other than it. -/
lemma deleteConnected_of_uep_penultimate {G : SimpleGraph α} (hconn : G.Connected)
    {c u z : α} (hu : IsUniqueEccentricPoint G c u)
    (hd : G.dist c z + 1 = (G.eccent c).toNat)
    (halt : ∃ w, G.Adj u w ∧ w ≠ z) : DeleteConnected G z := by
  have reach : ∀ x, x ≠ z → x ≠ u → ∃ p : G.Walk x c, z ∉ p.support := by
    intro x hxz hxu
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x c
    refine ⟨p, ?_⟩
    intro hz
    have hsum := edist_add_edist_le_of_mem_support (p := p) hz
    rw [← (hconn.preconnected x z).coe_dist_eq_edist,
      ← (hconn.preconnected z c).coe_dist_eq_edist, hp] at hsum
    have hnat : G.dist x z + G.dist z c ≤ G.dist x c := ENat.coe_le_coe.mp hsum
    have hpos := hconn.pos_dist_of_ne hxz
    have hzsym : G.dist z c = G.dist c z := SimpleGraph.dist_comm
    have hxsym : G.dist x c = G.dist c x := SimpleGraph.dist_comm
    have hlt := hu.2 x hxu
    omega
  have allreach : ∀ x, x ≠ z → ∃ p : G.Walk x c, z ∉ p.support := by
    intro x hxz
    by_cases hxu : x = u
    · subst x
      obtain ⟨w, huw, hwz⟩ := halt
      obtain ⟨p, hp⟩ := reach w hwz huw.ne.symm
      refine ⟨SimpleGraph.Walk.cons huw p, ?_⟩
      rw [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact not_or.mpr ⟨hxz.symm, hp⟩
    · exact reach x hxz hxu
  intro x y hx hy
  obtain ⟨p, hp⟩ := allreach x hx
  obtain ⟨q, hq⟩ := allreach y hy
  refine ⟨p.append q.reverse, ?_⟩
  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
    List.mem_reverse]
  exact not_or.mpr ⟨hp, hq⟩

/-- Peeling all leaves preserves the radius-decreasing property. This is
the induction step needed for the direct Case A tree bound. -/
theorem nonleaf_core_radius_decreasing {G : SimpleGraph α} [Nontrivial α]
    (hconn : G.Connected) (hr2 : 2 ≤ G.radius.toNat)
    (hmono : ∀ z, DeleteConnected G z →
      radOn G (Finset.univ.erase z) + 1 ≤ radOn G Finset.univ)
    (hcut : ∃ a, IsCut G a) (w : {v // v ∈ nonleafSet G})
    (hw : DeleteConnected (G.induce (nonleafSet G : Set α)) w) :
    radOn (G.induce (nonleafSet G : Set α)) (Finset.univ.erase w) + 1 ≤
      radOn (G.induce (nonleafSet G : Set α)) Finset.univ := by
  haveI : Nonempty α := ⟨w.val⟩
  have hn3 : 3 ≤ Fintype.card α := by
    have := four_le_card_of_radius_ge_two hconn hr2
    omega
  obtain ⟨u, hu, huw⟩ := core_noncut_has_leaf hconn hn3 hmono hcut w hw
  have hudrop := hmono u (deleteConnected_of_isLeaf hconn hu)
  obtain ⟨c, hc, hcu⟩ := isUniqueEccentricPoint_of_radOn_erase hconn (by omega) hudrop
  have hcS := central_mem_nonleafSet hconn hn3 hc
  let H := G.induce (nonleafSet G : Set α)
  let cS : {v // v ∈ nonleafSet G} := ⟨c, hcS⟩
  haveI : Nonempty {v // v ∈ nonleafSet G} := ⟨w⟩
  have hH : H.Connected := nonleaf_induce_connected hconn ⟨c, hcS⟩
  have hHtop : H.radius ≠ ⊤ := by
    obtain ⟨x, y, hxy⟩ := H.exists_edist_eq_radius_of_finite
    rw [← hxy]
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hH.preconnected x y)
  have hR : G.radius = H.radius + 1 := radius_eq_nonleaf_radius_add_one hconn hn3 hu
    (by simpa only [radOn_univ_eq_radius] using hudrop)
  have hRn : G.radius.toNat = H.radius.toNat + 1 := by
    rw [hR, ENat.toNat_add hHtop (by simp)]
    simp
  have hmetric : ∀ x : {v // v ∈ nonleafSet G}, H.dist cS x = G.dist c x.val := by
    intro x
    exact congrArg ENat.toNat (nonleaf_induce_edist hconn cS x)
  have hcw : G.dist c w.val + 1 = G.radius.toNat := by
    have hlt := hcu.2 w.val huw.ne.symm
    have htri := hconn.dist_triangle (u := c) (v := w.val) (w := u)
    have hedge : G.dist w.val u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huw.symm
    have hdcu := hcu.1
    rw [hc] at hlt hdcu
    omega
  have hstrict : ∀ x : {v // v ∈ nonleafSet G}, x ≠ w → H.dist cS x < H.radius.toNat := by
    intro x hxw
    have hxu : x.val ≠ u := by
      intro he
      exact mem_nonleafSet.mp x.property (he.symm ▸ hu)
    have hlt := hcu.2 x.val hxu
    rw [hc] at hlt
    rw [hmetric]
    by_contra hnot
    have hdist : G.dist c x.val + 1 = (G.eccent c).toNat := by
      rw [hc]
      omega
    have hwx : w.val ≠ x.val := by
      intro he
      exact hxw (Subtype.ext he.symm)
    have hnc := deleteConnected_of_uep_penultimate hconn hcu hdist ⟨w.val, huw, hwx⟩
    exact isCut_of_mem_nonleafSet hconn hmono hcut x.property hnc
  have hdw : H.dist cS w = H.radius.toNat := by rw [hmetric]; omega
  have hecc : H.eccent cS ≤ H.radius := by
    rw [SimpleGraph.eccent]
    refine iSup_le fun x => ?_
    have hnat : H.dist cS x ≤ H.radius.toNat := by
      by_cases hx : x = w
      · subst x; exact le_of_eq hdw
      · exact le_of_lt (hstrict x hx)
    rw [← (hH.preconnected cS x).coe_dist_eq_edist, ← ENat.coe_toNat hHtop]
    exact ENat.coe_le_coe.mpr hnat
  have hcH : IsCentral H cS := le_antisymm hecc H.radius_le_eccent
  haveI : Nontrivial {v // v ∈ nonleafSet G} := ⟨cS, w, by
    intro he
    rw [he, SimpleGraph.dist_self] at hdw
    omega⟩
  apply radOn_erase_add_one_le_of_isUniqueEccentricPoint hH inferInstance hcH
  constructor
  · simpa only [show H.eccent cS = H.radius from hcH] using hdw
  · intro x hx
    simpa only [show H.eccent cS = H.radius from hcH] using hstrict x hx

end Graffiti84
