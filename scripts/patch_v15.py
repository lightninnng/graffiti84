# -*- coding: utf-8 -*-
"""v15: full rewrite of F7a and F8 bodies in BasicFacts.lean."""
import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()

# ---- replace F7a body ----
a1 = s.index('lemma deleteConnected_of_isUniqueEccentricPoint')
a2 = s.index('lemma radOn_erase_add_one_le_of_isUniqueEccentricPoint')

f7a = '''lemma deleteConnected_of_isUniqueEccentricPoint {G : SimpleGraph \u03b1}
    (hconn : G.Connected) {c v : \u03b1} (huep : IsUniqueEccentricPoint G c v) :
    DeleteConnected G v := by
  have hcv : G.edist c v = G.eccent c :=
    edist_eq_eccent_of_isUniqueEccentricPoint hconn huep
  have hlt : \u2200 {w : \u03b1}, w \u2260 v \u2192 G.edist c w < G.eccent c := by
    intro w hw
    exact edist_lt_eccent_of_dist_lt hconn (huep.2 w hw)
  have hne : G.eccent c \u2260 \u22a4 := by
    obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
    intro h
    rw [\u2190 ht] at h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t) h
  have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat hne
  -- every geodesic from c to w \u2260 v avoids v
  have havoid : \u2200 {w : \u03b1}, w \u2260 v \u2192 \u2203 q : G.Walk c w, v \u2208 q.support \u2192 False := by
    intro w hw
    have hcw : ((G.edist c w).toNat : \u2115\u221e) = G.edist c w :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected c w))
    have hvw : ((G.edist v w).toNat : \u2115\u221e) = G.edist v w :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected v w))
    obtain \u27e8q, hq\u27e9 := SimpleGraph.exists_walk_of_edist_eq_coe
      (k := (G.edist c w).toNat) hcw.symm
    refine \u27e8q, fun hpv => ?_\u27e9
    have hsum := edist_add_edist_le_of_mem_support (p := q) hpv
    rw [hq] at hsum
    have hnat1 : (1 : \u2115) \u2264 (G.edist v w).toNat := by
      refine ENat.coe_le_coe.mp ?_
      rw [hvw]
      exact Order.one_le_iff_pos.mpr
        (SimpleGraph.edist_pos_of_ne (Ne.symm hw))
    have hnat2 : ((G.edist c v).toNat + (G.edist v w).toNat : \u2115)
        \u2264 (G.edist c w).toNat := by
      refine ENat.coe_le_coe.mp ?_
      rw [hcv]
      rw [hcoee, hvw]
      exact hsum
    have hnat3 : (G.edist c w).toNat < (G.eccent c).toNat := by
      refine ENat.coe_lt_coe.mp ?_
      rw [hcw, hcoee]
      exact hlt hw
    have hnat4 : (G.edist c v).toNat = (G.eccent c).toNat := by rw [hcv]
    omega
  obtain \u27e8qx, hxq\u27e9 := havoid hx
  obtain \u27e8qy, hyq\u27e9 := havoid hy
  refine \u27e8qx.reverse.append qy, ?_\u27e9
  intro hv
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse] at hv
  simp only [List.mem_reverse] at hv
  rcases hv with h | h
  \u00b7 exact hxq h
  \u00b7 exact hyq h

'''

s = s[:a1] + f7a + s[a2:]

# ---- replace F8 body ----
b1 = s.index('lemma isUniqueEccentricPoint_of_radOn_erase')
b2 = s.index('/-! ### F5: deleting a leaf never raises the radius -/')

f8 = '''lemma isUniqueEccentricPoint_of_radOn_erase {G : SimpleGraph \u03b1}
    (hconn : G.Connected) {v : \u03b1} (h2 : 2 \u2264 Fintype.card \u03b1)
    (hmono : radOn G (Finset.univ.erase v) + 1 \u2264 radOn G Finset.univ) :
    \u2203 c, IsCentral G c \u2227 IsUniqueEccentricPoint G c v := by
  haveI : Nontrivial \u03b1 :=
    Fintype.one_lt_card_iff_nontrivial.mpr (by omega)
  obtain \u27e8x, hx\u27e9 := exists_ne v
  have hSe : (Finset.univ.erase v).Nonempty :=
    \u27e8x, Finset.mem_erase.mpr \u27e8hx, Finset.mem_univ x\u27e9\u27e9
  obtain \u27e8c, hc, hcmin\u27e9 := eccOn_eq_radOn_attained hSe
  have hcne : c \u2260 v := (Finset.univ.mem_erase.mp hc).1
  obtain \u27e8w, hwadj\u27e9 : \u2203 w, G.Adj v w := by
    have hne : G.edist v x \u2260 \u22a4 :=
      SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected v x)
    have hcoe : ((G.edist v x).toNat : \u2115\u221e) = G.edist v x := ENat.coe_toNat hne
    obtain \u27e8q, hq\u27e9 := SimpleGraph.exists_walk_of_edist_eq_coe
      (k := (G.edist v x).toNat) hcoe.symm
    cases q with
    | nil => exact absurd rfl hx
    | cons h _ => exact \u27e8_, h\u27e9
  have hwne : w \u2260 v := (G.ne_of_adj hw).symm
  have hwse : w \u2208 Finset.univ.erase v := Finset.mem_erase.mpr
    \u27e8hwne, Finset.mem_univ w\u27e9
  have hw' : G.edist c w \u2264 radOn G (Finset.univ.erase v) :=
    (edist_le_eccOn (G := G) (S := Finset.univ.erase v) (c := c) hwse).trans hcmin
  -- the eccentricity of c is at most \u03c1 + 1
  have hecc : G.eccent c \u2264 radOn G (Finset.univ.erase v) + 1 := by
    rw [\u2190 eccOn_univ_eq_eccent]
    refine eccOn_le (G := G) (S := Finset.univ) (c := c) (k := _) ?_
    intro x _
    by_cases hxv : x = v
    \u00b7 calc G.edist c x = G.edist c v := by rw [hxv]
      _ \u2264 G.edist c w + 1 := edist_le_add_edge (hconn.preconnected c v) hw.symm
      _ \u2264 radOn G (Finset.univ.erase v) + 1 := add_le_add hw' (le_refl 1)
    \u00b7 exact le_trans (edist_le_eccOn
        (G := G) (S := Finset.univ.erase v) (c := c)
        (Finset.mem_erase.mpr \u27e8hxv, Finset.mem_univ x\u27e9)) hcmin
  have heccne : G.eccent c \u2260 \u22a4 := by
    obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
    intro h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t)
      (by rw [\u2190 ht, h])
  have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat heccne
  -- c is central, and radius = restricted radius + 1
  have hradius : G.radius = radOn G (Finset.univ.erase v) + 1 :=
    le_antisymm (le_trans SimpleGraph.radius_le_eccent hecc)
      (hmono.trans (by rw [radOn_univ_eq_radius]))
  have hcen : IsCentral G c := by
    rw [\u2190 eccOn_univ_eq_eccent, hcmin, radOn_univ_eq_radius]
    exact hradius.symm
  have heq : G.eccent c = radOn G (Finset.univ.erase v) + 1 := by
    rw [\u2190 eccOn_univ_eq_eccent, hcmin, radOn_univ_eq_radius]
    exact hradius.symm
  have h\u03c1ne : radOn G (Finset.univ.erase v) \u2260 \u22a4 := by
    intro h
    rw [heq, h, ENat.top_add] at heccne
    exact heccne heq
  refine \u27e8c, hcen, ?_, fun y hy => ?_\u27e9
  \u00b7 -- dist c v = ecc.toNat
    have hc3 : ((G.edist c v).toNat : \u2115\u221e) = G.edist c v :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected c v))
    have hed : G.edist c v = G.eccent c := by
      refine le_antisymm ?_ ?_
      \u00b7 calc G.edist c v \u2264 G.edist c w + 1 :=
            edist_le_add_edge (hconn.preconnected c v) hw.symm
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
              (Finset.mem_erase.mpr \u27e8hxv, Finset.mem_univ x\u27e9)).trans hcmin
        have hsmall : G.eccent c \u2264 radOn G (Finset.univ.erase v) := by
          rw [\u2190 eccOn_univ_eq_eccent]
          exact eccOn_le (G := G) (S := Finset.univ) (c := c) (k := _) hallv
        rw [heq] at hsmall
        exact absurd (ENat.add_one_le_iff (hm := h\u03c1ne).mp hsmall) (lt_irrefl _)
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
        (Finset.mem_erase.mpr \u27e8hy, Finset.mem_univ y\u27e9)).trans hcmin
    have hcoe1 : ((G.dist c y : \u2115) : \u2115\u221e) = G.edist c y := by
      show (((G.edist c y).toNat : \u2115) : \u2115\u221e) = _
      exact ENat.coe_toNat
        (SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c y))
    refine ENat.coe_lt_coe.mp ?_
    rw [hcoe1, hcoee]
    refine ENat.add_one_le_iff (hm := ?_).mpr ?_
    \u00b7 show G.edist c y \u2260 \u22a4
      exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c y)
    \u00b7 rw [heq]
      exact add_le_add hdy (le_refl 1)

'''

s = s[:b1] + f8 + s[b2:]
io.open(p, 'w', encoding='utf-8').write(s)
print('F7a/F8 rewritten')
