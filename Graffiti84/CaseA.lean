import Graffiti84.LeafCore
import Graffiti84.MaximalTree

namespace Graffiti84

open Classical

universe u

/-- Case A's induced-tree bound, proved directly by peeling leaves.
No corona classification or block decomposition is assumed. -/
set_option backward.isDefEq.respectTransparency false in
theorem vrd_cut_tree_bound {α : Type u} [Fintype α] [DecidableEq α] [Nontrivial α]
    {G : SimpleGraph α} (hconn : G.Connected)
    (hmono : ∀ z, DeleteConnected G z →
      radOn G (Finset.univ.erase z) + 1 ≤ radOn G Finset.univ)
    (hcut : ∃ a, IsCut G a) : 2 * G.radius.toNat ≤ treeNumber G := by
  have main : ∀ n, ∀ (β : Type u) [Fintype β] [DecidableEq β] [Nontrivial β]
      (F : SimpleGraph β), Fintype.card β = n → F.Connected →
      (∀ z, DeleteConnected F z →
        radOn F (Finset.univ.erase z) + 1 ≤ radOn F Finset.univ) →
      (∃ a, IsCut F a) → 2 * F.radius.toNat ≤ treeNumber F := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro β _ _ _ F hn hF hdrop hcutF
      haveI : Nonempty β := hF.nonempty
      by_cases hr2 : 2 ≤ F.radius.toNat
      · have hn3 : 3 ≤ Fintype.card β := by
          have := four_le_card_of_radius_ge_two hF hr2
          omega
        obtain ⟨u, _, _, hu, _⟩ := exists_two_isLeaf_of_hasCut hF hdrop hcutF
        obtain ⟨a, hua⟩ := (F.degree_pos_iff_exists_adj u).mp (by omega)
        have ha := leaf_parent_mem_nonleafSet hF hn3 hu hua
        let H := F.induce (nonleafSet F : Set β)
        haveI : Nonempty {v // v ∈ nonleafSet F} := ⟨⟨a, ha⟩⟩
        have hH : H.Connected := nonleaf_induce_connected hF ⟨a, ha⟩
        have hHtop : H.radius ≠ ⊤ := by
          obtain ⟨x, y, hxy⟩ := H.exists_edist_eq_radius_of_finite
          rw [← hxy]
          exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hH.preconnected x y)
        have hrad : F.radius = H.radius + 1 := radius_eq_nonleaf_radius_add_one hF hn3 hu
          (by simpa only [radOn_univ_eq_radius] using hdrop u (deleteConnected_of_isLeaf hF hu))
        have hradNat : F.radius.toNat = H.radius.toNat + 1 := by
          rw [hrad, ENat.toNat_add hHtop (by simp)]
          simp
        obtain ⟨x₀, y₀, hxy₀⟩ := H.exists_edist_eq_radius_of_finite
        have hdxy : H.dist x₀ y₀ = H.radius.toNat := congrArg ENat.toNat hxy₀
        haveI : Nontrivial {v // v ∈ nonleafSet F} := ⟨x₀, y₀, by
          intro he
          rw [he, SimpleGraph.dist_self] at hdxy
          omega⟩
        have hproper : nonleafSet F ⊂ Finset.univ := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
          intro he
          have huS : u ∈ nonleafSet F := by rw [he]; exact Finset.mem_univ u
          exact mem_nonleafSet.mp huS hu
        have hsmall : Fintype.card {v // v ∈ nonleafSet F} < n := by
          have hlt := Finset.card_lt_card hproper
          simpa only [Fintype.card_coe, Finset.card_univ, hn] using hlt
        have hmonoH : ∀ w, DeleteConnected H w →
            radOn H (Finset.univ.erase w) + 1 ≤ radOn H Finset.univ :=
          fun w hw => nonleaf_core_radius_decreasing hF hr2 hdrop hcutF w hw
        have leaf_out : ∀ (T : Finset {v // v ∈ nonleafSet F}) (v : β),
            F.degree v = 1 → v ∉ T.image Subtype.val := by
          intro T v hv hm
          obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hm
          exact mem_nonleafSet.mp w.property (hw.symm ▸ hv)
        by_cases hcutH : ∃ w, IsCut H w
        · have hIH := ih _ hsmall {v // v ∈ nonleafSet F} H rfl hH hmonoH hcutH
          obtain ⟨T, hT, hTmax, x, hx, y, hy, hxy, hnx, hny⟩ :=
            exists_maximum_tree_two_noncut hH
          obtain ⟨v, hv, hvx⟩ := core_noncut_has_leaf hF hn3 hdrop hcutF x hnx
          obtain ⟨w, hw, hwy⟩ := core_noncut_has_leaf hF hn3 hdrop hcutF y hny
          have hvw : v ≠ w := by
            intro he
            have hvy : F.Adj v y.val := he.symm ▸ hwy
            exact hxy (Subtype.ext (adj_eq_of_degree_eq_one (G := F) hv hvx hvy))
          have htree := isInducedTree_image_induce (G := F) (S := nonleafSet F) hT
          have hb := treeNumber_add_two_leaves htree hv hw hvx hwy
            (Finset.mem_image.mpr ⟨x, hx, rfl⟩) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
            (leaf_out T v hv) (leaf_out T w hw) hvw
          rw [Finset.card_image_of_injective T Subtype.val_injective, hTmax] at hb
          omega
        · have hnc : ∀ w, DeleteConnected H w := by
            intro w
            by_contra hw
            exact hcutH ⟨w, hw⟩
          obtain ⟨T, hT, hTmax⟩ := exists_maximum_induced_tree H
          have htree := isInducedTree_image_induce (G := F) (S := nonleafSet F) hT
          have hcover : ∀ x ∈ T.image Subtype.val,
              ∃ v, F.degree v = 1 ∧ F.Adj v x ∧ v ∉ T.image Subtype.val := by
            intro x hx
            obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx
            obtain ⟨v, hv, hvw⟩ := core_noncut_has_leaf hF hn3 hdrop hcutF w (hnc w)
            exact ⟨v, hv, hvw, leaf_out T v hv⟩
          have hb := treeNumber_double_of_leaf_neighbors htree hcover
          rw [Finset.card_image_of_injective T Subtype.val_injective, hTmax] at hb
          have hgeod := radius_add_one_le_treeNumber hH
          omega
      · have hgeod := radius_add_one_le_treeNumber hF
        omega
  exact main (Fintype.card α) α G rfl hconn hmono hcut

end Graffiti84
