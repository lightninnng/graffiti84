import Graffiti84.RadiusCriticalStructure
import Graffiti84.CaseB
import Graffiti84.Deletion
import Graffiti84.InducedTree
import Graffiti84.CaseA
import Graffiti84.LeafDeletion
import Mathlib

/-!
# Strong leaf lemma

A finite connected graph with a leaf has an induced tree on at least twice
its radius many vertices. The proof uses induction on the vertex count,
Case A's direct leaf peeling, and Case B's rooted induced-tree construction.
All deletions below use actual induced graphs; `Deletion` supplies the
bridges to the ambient-distance `radOn` lemmas.
-/

namespace Graffiti84

universe u

open Classical
open SimpleGraph

/--
F13 (geodesic count): for `s, l >= 1`, a geodesic of the core block with all
full-length pendant paths already yields `(s+1)(l+1) >= 2(s+l)` vertices.
This is the count used by the simplified proof (Corollary 3.B in
`docs/full-proof.md`); the ESS-based count of the original draft is gone.
-/
theorem tip_tree_count
    {s l : ℕ} (hs : 1 ≤ s) (hl : 1 ≤ l) :
    2 * (s + l) ≤ (s + 1) * (l + 1) := by
  nlinarith [hs, hl]

/--
If one already has an induced path/tree witness on `2r-1` old vertices and
adds a genuinely new leaf, the resulting order is at least `2r`.
-/
theorem add_leaf_count {r n : ℕ}
    (h : 2 * r - 1 ≤ n) :
    2 * r ≤ n + 1 := by
  omega

/--
Elementary reduction used in the minimal-counterexample proof:
if a smaller leaf graph has radius at least `r`, its `2*radius` tree bound
is already enough for the original target.
-/
theorem smaller_radius_bound_mono
    {r r' t : ℕ}
    (hrr : r ≤ r')
    (ht : 2 * r' ≤ t) :
    2 * r ≤ t := by
  omega

/-- A cycle cannot contain a degree-one vertex. -/
lemma leaf_not_mem_cycle {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {u x : α} (hu : G.degree u = 1)
    {p : G.Walk x x} (hp : p.IsCycle) : u ∉ p.support := by
  intro hmem
  have hc := hp.rotate hmem
  exact hc.snd_ne_penultimate
    (adj_eq_of_degree_eq_one hu
      ((p.rotate u hmem).adj_snd hc.not_nil)
      ((p.rotate u hmem).adj_penultimate hc.not_nil).symm)

/-- Adding a leaf adjacent to a vertex of an induced tree preserves the tree. -/
theorem isInducedTree_insert_leaf {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {S : Finset α} {u a : α}
    (hS : IsInducedTree G S) (ha : a ∈ S)
    (hu : G.degree u = 1) (hua : G.Adj u a) :
    IsInducedTree G (insert u S) := by
  have to_a : ∀ z ∈ insert u S, ConnectsWithin G (insert u S) z a := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzu | hzS
    · subst z
      refine ⟨hua.toWalk, ?_⟩
      intro z hz
      simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with hz | hz
      · rw [hz]; exact Finset.mem_insert_self u S
      · rw [hz]; exact Finset.mem_insert_of_mem ha
    · obtain ⟨p, hp⟩ := hS.1 z hzS a ha
      exact ⟨p, fun w hw => Finset.mem_insert_of_mem (hp w hw)⟩
  constructor
  · intro x hx y hy
    obtain ⟨p, hp⟩ := to_a x hx
    obtain ⟨q, hq⟩ := to_a y hy
    refine ⟨p.append q.reverse, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hz
    exact hz.elim (hp z) (hq z)
  · intro x p hp
    right
    intro hcycle
    have havoid := leaf_not_mem_cycle hu hcycle
    have hinside : ∀ z ∈ p.support, z ∈ S := by
      intro z hz
      rcases Finset.mem_insert.mp (hp z hz) with hzu | hzS
      · exact (havoid (hzu ▸ hz)).elim
      · exact hzS
    rcases hS.2 x p hinside with hzero | hnot
    · have := hcycle.three_le_length
      omega
    · exact hnot hcycle

/-- The graph-level counting step at the end of Case B. -/
theorem treeNumber_ge_of_rooted_tree_and_leaf {α : Type*} [Fintype α]
    [DecidableEq α] {G : SimpleGraph α} {S : Finset α} {u a : α} {r : ℕ}
    (hS : IsInducedTree G S) (ha : a ∈ S) (huS : u ∉ S)
    (hu : G.degree u = 1) (hua : G.Adj u a) (hcard : 2 * r - 1 ≤ S.card) :
    2 * r ≤ treeNumber G := by
  have ht := isInducedTree_insert_leaf hS ha hu hua
  have hbound : (insert u S).card ≤ treeNumber G :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
  rw [Finset.card_insert_of_notMem huS] at hbound
  omega

/-- Case B assembled in the original graph, with explicit hypotheses on the
deleted graph supplied by the vertex-count induction in `leafLemma`. -/
theorem leaf_bound_of_caseB {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} (hconn : G.Connected) {u a : α}
    (hu : G.degree u = 1) (hua : G.Adj u a) (hr2 : 2 ≤ G.radius.toNat)
    (hrad : (G.induce (↑(Finset.univ.erase u) : Set α)).radius = G.radius)
    (hdeg : ∀ v : {v // v ∈ Finset.univ.erase u},
      2 ≤ (G.induce (↑(Finset.univ.erase u) : Set α)).degree v)
    (hdrop : ∀ v : {v // v ∈ Finset.univ.erase u}, v.val ≠ a →
      DeleteConnected (G.induce (↑(Finset.univ.erase u) : Set α)) v →
      radOn (G.induce (↑(Finset.univ.erase u) : Set α)) (Finset.univ.erase v) + 1 ≤
        (G.induce (↑(Finset.univ.erase u) : Set α)).radius) :
    2 * G.radius.toNat ≤ treeNumber G := by
  let H := G.induce (↑(Finset.univ.erase u) : Set α)
  let aH : {v // v ∈ Finset.univ.erase u} :=
    ⟨a, Finset.mem_erase.mpr ⟨hua.ne.symm, Finset.mem_univ a⟩⟩
  haveI : Nontrivial α := ⟨u, a, hua.ne⟩
  have hH : H.Connected := (connected_induce_erase_iff u).mpr
    (deleteConnected_of_isLeaf hconn hu)
  haveI : Nontrivial {v // v ∈ Finset.univ.erase u} :=
    SimpleGraph.nontrivial_of_degree_ne_zero (G := H) (v := aH)
      (by
        intro hzero
        have hh : 2 ≤ H.degree aH := hdeg aH
        rw [hzero] at hh
        omega)
  obtain ⟨T, hT, haT, hcard⟩ := rooted_tree_of_drop_except hH aH
    (by simpa only [H, hrad] using hr2) hdeg (by
      intro v hva hv
      apply hdrop v _ hv
      intro he
      exact hva (Subtype.ext he))
  have htree : IsInducedTree G (T.image Subtype.val) := isInducedTree_image_induce hT
  have haS : a ∈ T.image Subtype.val := Finset.mem_image.mpr ⟨aH, haT, rfl⟩
  have huS : u ∉ T.image Subtype.val := by
    intro hm
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
    exact (Finset.mem_erase.mp v.property).1 hv
  apply treeNumber_ge_of_rooted_tree_and_leaf htree haS huS hu hua
  rw [Finset.card_image_of_injective T Subtype.val_injective]
  simpa only [H, hrad] using hcard


lemma finite_radius_of_connected {β : Type*} [Fintype β] [Nonempty β]
    {F : SimpleGraph β} (hF : F.Connected) : F.radius ≠ ⊤ := by
  obtain ⟨x, y, hxy⟩ := F.exists_edist_eq_radius_of_finite
  rw [← hxy]
  exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hF.preconnected x y)

lemma enat_add_one_le_of_toNat_lt {a b : ℕ∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : a.toNat < b.toNat) : a + 1 ≤ b := by
  have hh : (a.toNat : ℕ∞) + 1 ≤ (b.toNat : ℕ∞) := by
    exact_mod_cast (show a.toNat + 1 ≤ b.toNat by omega)
  simpa only [ENat.coe_toNat ha, ENat.coe_toNat hb] using hh

set_option backward.isDefEq.respectTransparency false in
/-- Every finite connected graph with a leaf has an induced tree of order at least twice its radius. -/
theorem leafLemma {α : Type u} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hG : G.Connected) (hleaf : ∃ u, G.degree u = 1) :
    2 * G.radius.toNat ≤ treeNumber G := by
  classical
  have main : ∀ n, ∀ (β : Type u) [Fintype β] [DecidableEq β] [Nontrivial β]
      (F : SimpleGraph β), Fintype.card β = n → F.Connected →
      (∃ u, F.degree u = 1) → 2 * F.radius.toNat ≤ treeNumber F := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro β _ _ _ F hn hF hleafF
      by_cases hr2 : 2 ≤ F.radius.toNat
      · by_contra hbad
        have hbad' : treeNumber F < 2 * F.radius.toNat := Nat.lt_of_not_ge hbad
        obtain ⟨u, hu⟩ := hleafF
        obtain ⟨a, hua⟩ := (F.degree_pos_iff_exists_adj u).mp (by omega)
        have hn3 : 3 ≤ Fintype.card β := by
          have := four_le_card_of_radius_ge_two hF hr2
          omega
        have hcut : IsCut F a := isCut_of_isLeaf hu hua hua.ne hn3
        have hFtop := finite_radius_of_connected hF
        have small : ∀ v : β, Fintype.card {x // x ∈ Finset.univ.erase v} < n := by
          intro v
          have hh := Finset.card_lt_card (Finset.erase_ssubset (Finset.mem_univ v))
          simpa only [Fintype.card_coe, Finset.card_univ, hn] using hh
        have drop : ∀ v, v ≠ u → DeleteConnected F v →
            radOn F (Finset.univ.erase v) + 1 ≤ radOn F Finset.univ := by
          intro v hvu hv
          have hva : v ≠ a := fun he => hcut (he ▸ hv)
          let D := F.induce (↑(Finset.univ.erase v) : Set β)
          let uD : {x // x ∈ Finset.univ.erase v} :=
            ⟨u, Finset.mem_erase.mpr ⟨hvu.symm, Finset.mem_univ u⟩⟩
          have huD : D.degree uD = 1 := degree_one_induce_of_isLeaf hu hua
            uD.property (Finset.mem_erase.mpr ⟨hva.symm, Finset.mem_univ a⟩)
          haveI : Nontrivial {x // x ∈ Finset.univ.erase v} :=
            SimpleGraph.nontrivial_of_degree_ne_zero (G := D) (v := uD) (by rw [huD]; omega)
          have hD : D.Connected := (connected_induce_erase_iff v).mpr hv
          have hIH := ih _ (small v) {x // x ∈ Finset.univ.erase v} D rfl hD ⟨uD, huD⟩
          have ht := treeNumber_induce_le F (Finset.univ.erase v)
          have hrlt : D.radius.toNat < F.radius.toNat := by omega
          have hd := enat_add_one_le_of_toNat_lt (finite_radius_of_connected hD) hFtop hrlt
          rw [radOn_univ_eq_radius]
          exact le_trans (add_le_add (radOn_le_induce_radius F _) (le_refl 1)) hd
        let H := F.induce (↑(Finset.univ.erase u) : Set β)
        have hH : H.Connected := (connected_induce_erase_iff u).mpr
          (deleteConnected_of_isLeaf hF hu)
        haveI : Nonempty {x // x ∈ Finset.univ.erase u} := hH.nonempty
        have hHtop := finite_radius_of_connected hH
        have hradle : H.radius ≤ F.radius := induce_radius_le_of_isLeaf hF hu hua hn3
        by_cases hrlt : H.radius.toNat < F.radius.toNat
        · have hd := enat_add_one_le_of_toNat_lt hHtop hFtop hrlt
          have hmono : ∀ v, DeleteConnected F v →
              radOn F (Finset.univ.erase v) + 1 ≤ radOn F Finset.univ := by
            intro v hv
            by_cases he : v = u
            · subst v
              rw [radOn_univ_eq_radius]
              exact le_trans (add_le_add (radOn_le_induce_radius F _) (le_refl 1)) hd
            · exact drop v he hv
          exact hbad (vrd_cut_tree_bound hF hmono ⟨a, hcut⟩)
        · have hradNat : H.radius.toNat = F.radius.toNat := by
            have hh := ENat.toNat_le_toNat hradle hFtop
            omega
          have hrad : H.radius = F.radius := by
            rw [← ENat.coe_toNat hHtop, ← ENat.coe_toNat hFtop, hradNat]
          obtain ⟨x, y, hxy⟩ := H.exists_edist_eq_radius_of_finite
          have hdxy : H.dist x y = H.radius.toNat := congrArg ENat.toNat hxy
          haveI : Nontrivial {x // x ∈ Finset.univ.erase u} := ⟨x, y, by
            intro he
            rw [he, SimpleGraph.dist_self] at hdxy
            omega⟩
          have hdeg : ∀ v, 2 ≤ H.degree v := by
            intro v
            have hp := hH.preconnected.degree_pos_of_nontrivial v
            by_contra hh
            have hv : H.degree v = 1 := by omega
            have hIH := ih _ (small u) {x // x ∈ Finset.univ.erase u} H rfl hH ⟨v, hv⟩
            have ht := treeNumber_induce_le F (Finset.univ.erase u)
            omega
          have hdropH : ∀ v : {x // x ∈ Finset.univ.erase u}, v.val ≠ a →
              DeleteConnected H v → radOn H (Finset.univ.erase v) + 1 ≤ H.radius := by
            intro v hva hv
            have hvF := deleteConnected_lift_leaf hua v hva hv
            have hd := drop v.val (Finset.mem_erase.mp v.property).1 hvF
            obtain ⟨c, hc, hcv⟩ := isUniqueEccentricPoint_of_radOn_erase hF (by omega) hd
            obtain ⟨d, hd, hdv⟩ := central_uep_after_leaf_deletion hF hn3 hu hrad v hc hcv
            simpa only [radOn_univ_eq_radius] using
              radOn_erase_add_one_le_of_isUniqueEccentricPoint hH inferInstance hd hdv
          exact hbad (leaf_bound_of_caseB hF hu hua hr2 hrad hdeg hdropH)
      · have hh := radius_add_one_le_treeNumber hF
        omega
  exact main (Fintype.card α) α G rfl hG hleaf

end Graffiti84
