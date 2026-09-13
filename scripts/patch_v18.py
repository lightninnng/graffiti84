# -*- coding: utf-8 -*-
"""v18: apply the lost v17 fixes (blocks 4,6,7,8,9,10,11)."""
import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()
applied = []


def rep(tag, old, new):
    global s
    assert old in s, 'NOT FOUND [' + tag + ']: ' + old[:90]
    s = s.replace(old, new)
    applied.append(tag)


# 4. F7a: hoist hco1/hco2 inside havoid
rep('hoist', """    intro w hw
    have hcw : ((G.edist c w).toNat : \u2115\u221e) = G.edist c w :=""",
    """    intro w hw
    have hco1 : ((G.edist c v).toNat : \u2115\u221e) = G.edist c v :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected c v))
    have hco2 : ((G.edist v w).toNat : \u2115\u221e) = G.edist v w :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected v w))
    have hcw : ((G.edist c w).toNat : \u2115\u221e) = G.edist c w :=""")

# 6. F7b: Nontrivial hypothesis
rep('f7b-nt', """lemma radOn_erase_add_one_le_of_isUniqueEccentricPoint {G : SimpleGraph \u03b1}
    (hconn : G.Connected) {c v : \u03b1} (hc : IsCentral G c)
    (huep : IsUniqueEccentricPoint G c v) :""",
    """lemma radOn_erase_add_one_le_of_isUniqueEccentricPoint {G : SimpleGraph \u03b1}
    (hconn : G.Connected) {c v : \u03b1} (hnt : Nontrivial \u03b1) (hc : IsCentral G c)
    (huep : IsUniqueEccentricPoint G c v) :""")

# 7. F8 middle+tail rewrite
b1 = s.index("  have hw' : G.edist c w")
b2 = s.index('/-! ### F5: deleting a leaf never raises the radius -/')
mid = """  have hw' : G.edist c w \u2264 radOn G (Finset.univ.erase v) :=
    (edist_le_eccOn (G := G) (S := Finset.univ.erase v) (c := c) hwse).trans
      (le_of_eq hcmin)
  -- the eccentricity of c is at most \u03c1 + 1
  have hecc : G.eccent c \u2264 radOn G (Finset.univ.erase v) + 1 := by
    rw [\u2190 eccOn_univ_eq_eccent]
    refine eccOn_le (G := G) (S := Finset.univ) (c := c) (k := _) ?_
    intro x _
    by_cases hxv : x = v
    \u00b7 calc G.edist c x = G.edist c v := by rw [hxv]
      _ \u2264 G.edist c w + 1 := edist_le_add_edge (hconn.preconnected c w) hw.symm
      _ \u2264 radOn G (Finset.univ.erase v) + 1 := add_le_add hw' (le_refl 1)
    \u00b7 exact le_trans (edist_le_eccOn
        (G := G) (S := Finset.univ.erase v) (c := c)
        (Finset.mem_erase.mpr \u27e8hxv, Finset.mem_univ x\u27e9)) (le_of_eq hcmin)
  have heccne : G.eccent c \u2260 \u22a4 := by
    obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
    intro h
    rw [\u2190 ht] at h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t) h
  have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat heccne
  -- c is central, and radius = restricted radius + 1
  have hradius : G.radius = radOn G (Finset.univ.erase v) + 1 :=
    le_antisymm (le_trans SimpleGraph.radius_le_eccent hecc)
      (hmono.trans (le_of_eq radOn_univ_eq_radius))
  have hcen : IsCentral G c := le_antisymm hecc SimpleGraph.radius_le_eccent
  have heq : G.eccent c = radOn G (Finset.univ.erase v) + 1 := by
    rw [hc, hradius]
  have h\u03c1ne : radOn G (Finset.univ.erase v) \u2260 \u22a4 := by
    intro h
    rw [h] at heq
    simp at heq
    exact heccne heq
  refine \u27e8c, hcen, ?_, fun y hy => ?_\u27e9
  \u00b7 -- dist c v = ecc.toNat
    have hc3 : ((G.edist c v).toNat : \u2115\u221e) = G.edist c v :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected c v))
    have hed : G.edist c v = G.eccent c := by
      refine le_antisymm ?_ ?_
      \u00b7 calc G.edist c v \u2264 G.edist c w + 1 :=
            edist_le_add_edge (hconn.preconnected c w) hw.symm
        _ \u2264 radOn G (Finset.univ.erase v) + 1 := add_le_add hw' (le_refl 1)
        _ = G.eccent c := heq.symm
      \u00b7 intro hcon
        have hallv : \u2200 x : \u03b1, G.edist c x
            \u2264 radOn G (Finset.univ.erase v) := by
          intro x
          by_cases hxv : x = v
          \u00b7 rw [hxv]; exact hcon
          \u00b7 exact (edist_le_eccOn
              (G := G) (S := Finset.univ.erase v) (c := c)
              (Finset.mem_erase.mpr \u27e8hxv, Finset.mem_univ x\u27e9)).trans
              (le_of_eq hcmin)
        have hsmall : G.eccent c \u2264 radOn G (Finset.univ.erase v) := by
          rw [\u2190 eccOn_univ_eq_eccent]
          exact eccOn_le (G := G) (S := Finset.univ) (c := c) (k := _) hallv
        rw [heq] at hsmall
        exact absurd (ENat.add_one_le_iff h\u03c1ne |>.mp hsmall) (lt_irrefl _)
    refine Nat.cast_injective ?_
    have hd' : ((G.dist c v : \u2115) : \u2115\u221e) = G.edist c v := by
      show (((G.edist c v).toNat : \u2115) : \u2115\u221e) = _
      exact ENat.coe_toNat
        (SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c v))
    rw [hd', hcoee]
    exact hed
  \u00b7 -- dist c y < ecc.toNat for y \u2260 v
    have hdy : G.edist c y \u2264 radOn G (Finset.univ.erase v) :=
      (edist_le_eccOn (G := G) (S := Finset.univ.erase v) (c := c)
        (Finset.mem_erase.mpr \u27e8hy, Finset.mem_univ y\u27e9)).trans (le_of_eq hcmin)
    have hcoe1 : ((G.dist c y : \u2115) : \u2115\u221e) = G.edist c y := by
      show (((G.edist c y).toNat : \u2115) : \u2115\u221e) = _
      exact ENat.coe_toNat
        (SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c y))
    have hfin : G.edist c y \u2260 \u22a4 :=
      SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c y)
    have hstep : G.edist c y + 1 \u2264 G.eccent c := by
      rw [heq]
      exact add_le_add hdy (le_refl 1)
    have hlt : G.edist c y < G.eccent c :=
      ENat.add_one_le_iff hfin |>.mpr hstep
    refine ENat.coe_lt_coe.mp ?_
    rw [hcoe1, hcoee]
    exact hlt

"""
s = s[:b1] + mid + s[b2:]
applied.append('f8-rewrite')

# 8. F5: named hS
rep('f5-hs', """  obtain \u27e8c, hc, hcmin\u27e9 := eccOn_eq_radOn_attained
    (G := G) (S := Finset.univ) Finset.univ_nonempty""",
    """  obtain \u27e8c, hc, hcmin\u27e9 := eccOn_eq_radOn_attained
    (G := G) (S := Finset.univ) (hS := Finset.univ_nonempty)""")

# 9. F5: rw order in hcz
rep('f5-rw', """    rw [\u2190 eccOn_univ_eq_eccent, hcen] at hcor""",
    """    rw [eccOn_univ_eq_eccent (c := z), hcen] at hcor""")

# 10. drop open-in
rep('open-in', """/-- The largest order of an induced tree. -/
open Classical in
noncomputable def treeNumber (G : SimpleGraph \u03b1) : \u2115 :=""",
    """/-- The largest order of an induced tree. -/
noncomputable def treeNumber (G : SimpleGraph \u03b1) : \u2115 :=""")

# 11. F14 obtain-destructure
rep('f14', """  refine Finset.sup_le ?_
  intro S hS
  exact Finset.le_sup (Finset.mem_filter.mpr \u27e8hS.1, hS.2.1\u27e9)""",
    """  refine Finset.sup_le ?_
  intro S hS
  obtain \u27e8-, htree, -\u27e9 := Finset.mem_filter.mp hS
  exact Finset.le_sup (Finset.mem_filter.mpr \u27e8Finset.mem_univ S, htree\u27e9)""")

io.open(p, 'w', encoding='utf-8').write(s)
print('applied:', applied)
