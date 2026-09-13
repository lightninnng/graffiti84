# -*- coding: utf-8 -*-
"""Append batch 2 part 2 (F8 + F5) to BasicFacts.lean; fix lt_iff_add_one_le in part 1."""
import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()

# --- fix part 1's use of the non-existent Order.lt_iff_add_one_le ---
old = """    exact Order.lt_iff_add_one_le.mp hlt"""
new = """    exact (ENat.add_one_le_iff' (hn := hstep_ne_top)).mp hlt"""
assert old in s, 'fix 2a failed'
s = s.replace(old, new)

old2 = """  have hstep : eccOn G (Finset.univ.erase v) c + 1 \u2264 G.eccent c := by"""
new2 = """  have hstep_ne_top : G.eccent c \u2260 \u22a4 := by
    obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
    intro h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t)
      (by rw [\u2190 ht, h])
  have hstep : eccOn G (Finset.univ.erase v) c + 1 \u2264 G.eccent c := by"""
assert old2 in s, 'fix 2a anchor failed'
s = s.replace(old2, new2)

# --- append F8 and F5 ---
add = '''
/-! ### F8: the converse half of the criterion -/

/-- **F8 (converse).** If deleting `v` lowers the full radius by exactly one
(in the ambient-distance bookkeeping), the centre of the deleted graph is a
central vertex of `G` whose unique eccentric point is `v`. -/
lemma isUniqueEccentricPoint_of_radOn_erase {G : SimpleGraph \u03b1}
    (hconn : G.Connected) {v : \u03b1} (h2 : 2 \u2264 Fintype.card \u03b1)
    (hmono : radOn G (Finset.univ.erase v) + 1 \u2264 radOn G Finset.univ) :
    \u2203 c, IsCentral G c \u2227 IsUniqueEccentricPoint G c v := by
  have hSe : (Finset.univ.erase v).Nonempty := by
    by_contra hall
    have hv : \u2200 w : \u03b1, w = v := by
      intro w
      by_contra hw
      exact hall \u27e8w, hw\u27e9
    have hsub : (Finset.univ : Finset \u03b1) = {v} :=
      Finset.eq_singleton_iff_unique_mem.2 \u27e8rfl, fun x _ => hv x\u27e9
    rw [hsub] at h2
    simp at h2
  obtain \u27e8c, hc, hcmin\u27e9 := eccOn_eq_radOn_attained hSe
  have hcne : c \u2260 v := (Finset.univ.mem_erase.mp hc).1
  set \u03c1 := radOn G (Finset.univ.erase v) with h\u03c1
  have hall : \u2200 x : \u03b1, x \u2260 v \u2192 G.edist c x \u2264 \u03c1 := fun x hx =>
    edist_le_eccOn (Finset.mem_erase.mpr \u27e8hx, Finset.mem_univ x\u27e9)
  haveI : Nontrivial \u03b1 := by
    by_contra hnt
    have hall2 : \u2200 w : \u03b1, w = v := by
      intro w
      by_contra hw
      exact hnt \u27e8v, w, fun hh => hw hh.symm\u27e9
    have hsub : (Finset.univ : Finset \u03b1) = {v} :=
      Finset.eq_singleton_iff_unique_mem.2 \u27e8rfl, fun x _ => hall2 x\u27e9
    rw [hsub] at h2
    simp at h2
  obtain \u27e8x, hx\u27e9 := exists_ne v
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
  have hwse : w \u2208 Finset.univ.erase v := Finset.mem_erase.mpr \u27e8hwne, Finset.mem_univ w\u27e9
  have hecc : G.eccent c \u2264 \u03c1 + 1 := by
    refine eccOn_le (G := G) (S := Finset.univ) (c := c) (k := \u03c1 + 1) ?_
    intro x _
    by_cases hxv : x = v
    \u00b7 have hR : G.Reachable c w := hconn.preconnected c w
      have hw' : G.edist c w \u2264 \u03c1 := edist_le_eccOn hwse
      calc G.edist c x = G.edist c v := by rw [hxv]
      _ \u2264 1 + G.edist c w := edist_le_add_edge hR hw.symm
      _ \u2264 1 + \u03c1 := add_le_add_right hw' 1
    \u00b7 exact le_trans (hall x hxv) (le_self_add)
  have heccne : G.eccent c \u2260 \u22a4 := by
    obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
    intro h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t)
      (by rw [\u2190 ht, h])
  have hradius : G.radius = \u03c1 + 1 := by
    refine le_antisymm ?_ (by rw [radOn_univ_eq_radius]; exact hmono)
    calc G.radius \u2264 G.eccent c := SimpleGraph.radius_le_eccent
    _ \u2264 \u03c1 + 1 := hecc
    _ \u2264 radOn G Finset.univ := hmono
    _ = G.radius := radOn_univ_eq_radius
  have hcen : IsCentral G c := by
    rw [hc, hradius]
  have heq : G.eccent c = \u03c1 + 1 := by rw [hc, hradius]
  have h\u03c1ne : \u03c1 \u2260 \u22a4 := by
    intro h
    rw [h] at heq
    exact heccne heq
  refine \u27e8c, hcen, ?_, fun y hy => ?_\u27e9
  \u00b7 -- dist c v = ecc.toNat
    have hc3 : ((G.edist c v).toNat : \u2115\u221e) = G.edist c v :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
        (hconn.preconnected c v))
    have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat heccne
    have hed : G.edist c v = G.eccent c := by
      refine le_antisymm ?_ ?_
      \u00b7 calc G.edist c v \u2264 1 + G.edist c w :=
            edist_le_add_edge (hconn.preconnected c v) hw.symm
        _ \u2264 1 + \u03c1 := add_le_add_right (edist_le_eccOn hwse) 1
        _ = G.eccent c := by rw [heq, add_comm]
      \u00b7 intro hcon
        have hallv : \u2200 x : \u03b1, G.edist c x \u2264 \u03c1 := by
          intro x
          by_cases hxv : x = v
          \u00b7 rw [hxv]; exact hcon
          \u00b7 exact hall x hxv
        have hsmall : eccOn G Finset.univ c \u2264 \u03c1 :=
          eccOn_le (G := G) (S := Finset.univ) (c := c) (k := \u03c1) hallv
        rw [eccOn_univ_eq_eccent, heq] at hsmall
        exact absurd (ENat.add_one_le_iff (hm := h\u03c1ne).mp hsmall) (lt_irrefl \u03c1)
    rw [hc3, hcoee]
    exact ENat.coe_inj.mpr (by
      show (G.edist c v).toNat = (G.eccent c).toNat
      rw [hed])
  \u00b7 -- dist c y < ecc.toNat for y \u2260 v
    have hdy : G.edist c y \u2264 \u03c1 := hall y hy
    have hcoe1 : ((G.dist c y : \u2115) : \u2115\u221e) = G.edist c y := by
      show (((G.edist c y).toNat : \u2115) : \u2115\u221e) = _
      exact ENat.coe_toNat
        (SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c y))
    have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat heccne
    refine ENat.coe_lt_coe.mp ?_
    rw [hcoe1, hcoee]
    refine ENat.add_one_le_iff (hm := heccne).mp ?_
    calc G.edist c y + 1 \u2264 \u03c1 + 1 := add_le_add hdy (le_refl 1)
    _ = G.eccent c := heq.symm

/-! ### F5: deleting a leaf never raises the radius -/

/-- **F5.** If `z` is a leaf of a connected graph on at least three vertices,
then the radius restricted to the remaining vertices is at most the full
radius. -/
lemma radOn_erase_le_radOn_of_isLeaf {G : SimpleGraph \u03b1} (hconn : G.Connected)
    {z p : \u03b1} (hdeg : G.degree z = 1) (hzp : G.Adj z p)
    (hn3 : 3 \u2264 Fintype.card \u03b1) :
    radOn G (Finset.univ.erase z) \u2264 radOn G Finset.univ := by
  obtain \u27e8c, hc, hcmin\u27e9 := eccOn_eq_radOn_attained
    (G := G) (S := Finset.univ) (by simp)
  have hcen : G.eccent c = G.radius := by
    rw [\u2190 eccOn_univ_eq_eccent, hcmin, radOn_univ_eq_radius]
  have hcz : c \u2260 z := by
    intro h
    rw [h] at hcen
    have hcor := radius_lt_eccOn_of_isLeaf hconn hdeg hzp hn3
    rw [hcen] at hcor
    have hfin : G.radius \u2260 \u22a4 := by
      obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
      intro h
      exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t)
        (by rw [\u2190 ht, h])
    have hcoer : ((G.radius).toNat : \u2115\u221e) = G.radius := ENat.coe_toNat hfin
    have hnat : (1 : \u2115) + (G.radius).toNat \u2264 (G.radius).toNat := by
      refine ENat.coe_le_coe.mp ?_
      have hstep : (((1 : \u2115) + (G.radius).toNat : \u2115) : \u2115\u221e) = 1 + G.radius := by
        rw [Nat.cast_add, hcoer]
      rw [hstep]
      exact hcor
    omega
  have hmem : c \u2208 Finset.univ.erase z := Finset.mem_erase.mpr \u27e8hcz, Finset.mem_univ c\u27e9
  calc radOn G (Finset.univ.erase z) \u2264 eccOn G (Finset.univ.erase z) c :=
      radOn_le_eccOn hmem
  _ \u2264 eccOn G Finset.univ c := by
      refine eccOn_le (G := G) (S := Finset.univ.erase z) (c := c) (k := _) ?_
      intro x hx
      exact edist_le_eccOn (Finset.mem_univ x)
  _ = radOn G Finset.univ := by
      rw [eccOn_univ_eq_eccent, hcen, \u2190 radOn_univ_eq_radius]
'''

marker = 'end Graffiti84'
assert marker in s, 'marker missing'
s = s.replace(marker, add + '\n' + marker)
io.open(p, 'w', encoding='utf-8').write(s)
print('appended part 2')
