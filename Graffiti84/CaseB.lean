import Graffiti84.EndBlocks
import Graffiti84.RadiusCriticalStructure

namespace Graffiti84

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Having central UEP witnesses for all but one vertex forces every vertex
to be central. The proof uses finite injectivity, then symmetry of distance. -/
theorem isCentral_all_of_uep_except {G : SimpleGraph α} (a : α)
    (huep : ∀ v, v ≠ a → ∃ c, IsCentral G c ∧ IsUniqueEccentricPoint G c v) :
    ∀ b, IsCentral G b := by
  intro b
  by_contra hb
  let f : α → α := fun v => if h : v = a then b else (huep v h).choose
  have hfa : f a = b := by simp [f]
  have hfc : ∀ v, v ≠ a → IsCentral G (f v) := by
    intro v hv
    simpa only [f, dif_neg hv] using (huep v hv).choose_spec.1
  have hfu : ∀ v, v ≠ a → IsUniqueEccentricPoint G (f v) v := by
    intro v hv
    simpa only [f, dif_neg hv] using (huep v hv).choose_spec.2
  have hfne : ∀ v, v ≠ a → f v ≠ b := by
    intro v hv he
    exact hb (he ▸ hfc v hv)
  have hinj : Function.Injective f := by
    intro v w he
    by_cases hv : v = a
    · have hw : w = a := by
        by_contra hw
        exact hfne w hw (he.symm.trans ((congrArg f hv).trans hfa))
      exact hv.trans hw.symm
    · by_cases hw : w = a
      · exact (hfne v hv (he.trans ((congrArg f hw).trans hfa))).elim
      · have hw' : IsUniqueEccentricPoint G (f v) w := he.symm ▸ hfu w hw
        exact isUniqueEccentricPoint_unique (hfu v hv) hw'
  have hsurj := Finite.surjective_of_injective hinj
  have hother : ∀ y, y ≠ b → IsCentral G y := by
    intro y hy
    obtain ⟨v, hv⟩ := hsurj y
    have hva : v ≠ a := by
      intro h
      exact hy (hv.symm.trans ((congrArg f h).trans hfa))
    exact hv ▸ hfc v hva
  apply hb
  change G.eccent b = G.radius
  refine le_antisymm ?_ G.radius_le_eccent
  rw [SimpleGraph.eccent]
  refine iSup_le fun y => ?_
  by_cases hy : y = b
  · simp [hy]
  · calc
      G.edist b y = G.edist y b := G.edist_comm
      _ ≤ G.eccent y := G.edist_le_eccent
      _ = G.radius := hother y hy

set_option maxHeartbeats 800000 in
/-- The exceptional vertex also has a central UEP witness. -/
theorem central_uep_of_uep_except {G : SimpleGraph α} [Nontrivial α]
    (hconn : G.Connected) (a : α)
    (huep : ∀ v, v ≠ a → ∃ c, IsCentral G c ∧ IsUniqueEccentricPoint G c v) :
    ∃ c, IsCentral G c ∧ IsUniqueEccentricPoint G c a := by
  have hcentral : ∀ v, G.eccent v = G.radius := isCentral_all_of_uep_except a huep
  have hr : 0 < G.radius.toNat := by
    have hp := eccNat_pos_of_connected_nontrivial hconn a
    simpa only [eccNat, hcentral a] using hp
  let D : SimpleGraph α := {
    Adj := fun x y => G.dist x y = G.radius.toNat
    symm := ⟨by intro x y h; simpa only [SimpleGraph.dist_comm] using h⟩
    loopless := ⟨by intro x h; simp only [SimpleGraph.dist_self] at h; omega⟩ }
  have hpos : ∀ v, 1 ≤ D.degree v := by
    intro v
    obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite v
    have hd : D.Adj v w := by
      change G.dist v w = G.radius.toNat
      change (G.edist v w).toNat = G.radius.toNat
      rw [hw, hcentral v]
    exact D.degree_pos_iff_exists_adj v |>.mpr ⟨w, hd⟩
  have hother : ∀ v, v ≠ a → ∃ c, D.Adj v c ∧ D.degree c = 1 := by
    intro v hv
    obtain ⟨c, hc, hcv⟩ := huep v hv
    have hdcv : D.Adj c v := by
      change G.dist c v = G.radius.toNat
      rw [hcv.1, hc]
    refine ⟨c, hdcv.symm, SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ?_⟩
    refine ⟨v, hdcv, ?_⟩
    intro w hw
    by_contra hwv
    have hlt := hcv.2 w hwv
    change G.dist c w = G.radius.toNat at hw
    rw [hc] at hlt
    omega
  obtain ⟨c, hac, hc1⟩ := degree_one_neighbor_of_all_other D a hpos hother
  refine ⟨c, hcentral c, ?_, ?_⟩
  · change G.dist c a = (G.eccent c).toNat
    have hca : D.Adj c a := hac.symm
    change G.dist c a = G.radius.toNat at hca
    simpa only [hcentral c] using hca
  · intro y hya
    have hetop : G.eccent c ≠ ⊤ := by
      obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite c
      rw [← hw]
      exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c w)
    have hle : G.dist c y ≤ (G.eccent c).toNat :=
      ENat.toNat_le_toNat G.edist_le_eccent hetop
    have hne : G.dist c y ≠ (G.eccent c).toNat := by
      intro he
      have hcy : D.Adj c y := by
        change G.dist c y = G.radius.toNat
        simpa only [hcentral c] using he
      exact hya (adj_eq_of_degree_eq_one hc1 hac.symm hcy).symm
    omega

/-- Case B's rooted tree, with its non-cut/radius-drop hypotheses explicit. -/
theorem rooted_tree_of_drop_except {G : SimpleGraph α} [Nontrivial α]
    (hconn : G.Connected) (a : α) (hr2 : 2 ≤ G.radius.toNat)
    (hdeg : ∀ v, 2 ≤ G.degree v)
    (hdrop : ∀ v, v ≠ a → DeleteConnected G v →
      radOn G (Finset.univ.erase v) + 1 ≤ G.radius) :
    ∃ S : Finset α, IsInducedTree G S ∧ a ∈ S ∧
      2 * G.radius.toNat - 1 ≤ S.card := by
  have hnc := deleteConnected_all_of_drop_except hconn a hdeg hdrop
  have hu : ∀ v, v ≠ a → ∃ c, IsCentral G c ∧ IsUniqueEccentricPoint G c v := by
    intro v hv
    apply isUniqueEccentricPoint_of_radOn_erase hconn Fintype.one_lt_card
    simpa only [radOn_univ_eq_radius] using hdrop v hv (hnc v)
  obtain ⟨c, hc, hca⟩ := central_uep_of_uep_except hconn a hu
  apply rooted_chung hconn hr2
  simpa only [radOn_univ_eq_radius] using
    radOn_erase_add_one_le_of_isUniqueEccentricPoint hconn inferInstance hc hca

end Graffiti84
