# -*- coding: utf-8 -*-
"""Append batch 2 part 1 (walk toolkit + F7) to BasicFacts.lean."""
import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()

add = '''
/-! ## Batch 2: walk toolkit and the UEP criterion (F7, F8, F5) -/

/-- Prepending an edge costs at most one: `d(u, w) <= 1 + d(v, w)` when
`u ~ v` and `v` reaches `w`. -/
lemma edist_le_add_edge_prepend {G : SimpleGraph \u03b1} {u v w : \u03b1}
    (huv : G.Adj u v) (hR : G.Reachable v w) :
    G.edist u w \u2264 1 + G.edist v w := by
  rw [SimpleGraph.edist_comm]
  have h1 : G.edist w u \u2264 G.edist w v + 1 :=
    edist_le_add_edge hR.symm huv.symm
  rw [SimpleGraph.edist_comm (G := G) v w] at h1
  linarith

/-- Any walk through `v` is at least as long as the two geodesic legs. -/
lemma edist_add_edist_le_of_mem_support {G : SimpleGraph \u03b1} {u v w : \u03b1}
    {p : G.Walk u w} (hpv : v \u2208 p.support) :
    G.edist u v + G.edist v w \u2264 (p.length : \u2115\u221e) := by
  induction p with
  | nil =>
      have hvu : v = u := by simpa using hpv
      subst hvu
      simp [SimpleGraph.edist_self]
  | @cons u x w h q ih =>
      rcases Finset.mem_cons.mp
        (by simpa [SimpleGraph.Walk.support_cons] using hpv) with rfl | hpv'
      \u00b7 simp
        exact SimpleGraph.edist_le (SimpleGraph.Walk.cons h q)
      \u00b7 have hsum := ih hpv'
        have hfin : ((q.length : \u2115) : \u2115\u221e) < \u22a4 := ENat.coe_lt_top _
        have hne : G.edist x v \u2260 \u22a4 := by
          intro hc
          rw [hc] at hsum
          simp at hsum
        have hr : G.Reachable x v := SimpleGraph.edist_ne_top_iff_reachable.mp hne
        have hpre : G.edist u v \u2264 1 + G.edist x v := edist_le_add_edge_prepend h hr
        have step1 : G.edist u v + G.edist v w \u2264 (1 + G.edist x v) + G.edist v w :=
          add_le_add_right hpre _
        have step2 : (1 + G.edist x v) + G.edist v w \u2264 1 + ((q.length : \u2115) : \u2115\u221e) := by
          rw [add_assoc]
          exact add_le_add_right hsum 1
        calc G.edist u v + G.edist v w \u2264
            ((1 + G.edist x v) + G.edist v w : \u2115\u221e) := step1
        _ \u2264 1 + ((q.length : \u2115) : \u2115\u221e) := le_trans step2 (le_refl _)
        _ \u2264 ((q.length + 1 : \u2115) : \u2115\u221e) := by push_cast; exact le_refl _
        _ = ((SimpleGraph.Walk.cons h q).length : \u2115\u221e) := by
            rw [SimpleGraph.Walk.length_cons]

/-- Bridging: in a connected graph, `dist < ecc.toNat` upgrades to an
`ENat`-strict bound. -/
lemma edist_lt_eccent_of_dist_lt {G : SimpleGraph \u03b1} (hconn : G.Connected)
    {c x : \u03b1} (hlt : G.dist c x < (G.eccent c).toNat) :
    G.edist c x < G.eccent c := by
  have hne : G.eccent c \u2260 \u22a4 := by
    obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
    intro h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t)
      (by rw [\u2190 ht, h])
  have hcoe : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat hne
  have hd : ((G.dist c x : \u2115) : \u2115\u221e) = G.edist c x := by
    show (((G.edist c x).toNat : \u2115) : \u2115\u221e) = _
    exact ENat.coe_toNat
      (SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c x))
  calc G.edist c x = ((G.dist c x : \u2115) : \u2115\u221e) := hd.symm
  _ < ((G.eccent c).toNat : \u2115\u221e) := by exact_mod_cast hlt
  _ = G.eccent c := hcoe

/-- The distance from a centre to its unique eccentric point is the full
eccentricity. -/
lemma edist_eq_eccent_of_isUniqueEccentricPoint {G : SimpleGraph \u03b1}
    (hconn : G.Connected) {c v : \u03b1} (huep : IsUniqueEccentricPoint G c v) :
    G.edist c v = G.eccent c := by
  have hne : G.eccent c \u2260 \u22a4 := by
    obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
    intro h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t)
      (by rw [\u2190 ht, h])
  have hcoe : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat hne
  have hd : ((G.dist c v : \u2115) : \u2115\u221e) = G.edist c v := by
    show (((G.edist c v).toNat : \u2115) : \u2115\u221e) = _
    exact ENat.coe_toNat
      (SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c v))
  rw [\u2190 hcoe, \u2190 hd, huep.1]

/-! ### F7: the drop half of the criterion -/

/-- **F7 (drop).** If a centre has the unique eccentric point `v`, then `G - v`
is connected. -/
lemma deleteConnected_of_isUniqueEccentricPoint {G : SimpleGraph \u03b1}
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
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t)
      (by rw [\u2190 ht, h])
  have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat hne
  intro x y hx hy
  obtain \u27e8q, hq\u27e9 := SimpleGraph.exists_walk_of_edist_eq_coe
    (k := (G.edist c x).toNat) (by
      have hc3 : ((G.edist c x).toNat : \u2115\u221e) = G.edist c x :=
        ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
          (hconn.preconnected c x))
      exact hc3.symm)
  have hqx : G.edist c x < G.eccent c := hlt hx
  by_cases hpv : v \u2208 q.support
  \u00b7 have hsum := edist_add_edist_le_of_mem_support (p := q) hpv
    rw [hq] at hsum
    have h1 : (1 : \u2115\u221e) \u2264 G.edist v x :=
      Order.one_le_iff_pos.mpr (SimpleGraph.edist_pos_of_ne (Ne.symm hx))
    have h2 : ((G.edist c v).toNat : \u2115) + ((G.edist v x).toNat : \u2115)
        \u2264 (G.edist c x).toNat := by
      have hco1 : ((G.edist c v).toNat : \u2115\u221e) = G.edist c v :=
        ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
          (hconn.preconnected c v))
      have hco2 : ((G.edist v x).toNat : \u2115\u221e) = G.edist v x :=
        ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
          (hconn.preconnected v x))
      have hco3 : ((G.edist c x).toNat : \u2115\u221e) = G.edist c x :=
        ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
          (hconn.preconnected c x))
      rw [hco1, hco2, hco3]
      exact hsum
    have h3 : (G.edist c x).toNat < (G.eccent c).toNat := by
      refine ENat.coe_lt_coe.mp ?_
      rw [hcoee]
      exact hqx
    have h4 : (G.edist c v).toNat = (G.eccent c).toNat := by rw [hcv]
    omega
  \u00b7 exact \u27e8q, hpv\u27e9

/-- **F7 (drop, radius form).** The restricted radius after deleting `v` is at
most the full radius minus one. -/
lemma radOn_erase_add_one_le_of_isUniqueEccentricPoint {G : SimpleGraph \u03b1}
    (hconn : G.Connected) {c v : \u03b1} (hc : IsCentral G c)
    (huep : IsUniqueEccentricPoint G c v) :
    radOn G (Finset.univ.erase v) + 1 \u2264 radOn G Finset.univ := by
  have hcv : G.edist c v = G.eccent c :=
    edist_eq_eccent_of_isUniqueEccentricPoint hconn huep
  have hcne : c \u2260 v := by
    intro h
    rw [h] at hcv
    simp [SimpleGraph.edist_self] at hcv
    exact SimpleGraph.eccent_ne_zero v hcv.symm
  have hmem : c \u2208 Finset.univ.erase v := Finset.mem_erase.mpr \u27e8hcne, Finset.mem_univ c\u27e9
  have hsup : \u2203 y \u2208 Finset.univ.erase v,
      eccOn G (Finset.univ.erase v) c = G.edist c y := by
    obtain \u27e8c0, hc0\u27e9 : (Finset.univ.erase v).Nonempty :=
      \u27e8c, Finset.mem_erase.mpr \u27e8hcne, Finset.mem_univ c\u27e9\u27e9
    haveI : Nonempty {x // x \u2208 Finset.univ.erase v} := \u27e8\u27e8c0, hc0\u27e9\u27e9
    obtain \u27e8m, hm\u27e9 := Finite.exists_max
      (f := fun x : {x // x \u2208 Finset.univ.erase v} => G.edist c x)
    exact \u27e8m, m.property, le_antisymm (iSup\u2082_le fun x hx => hm \u27e8x, hx\u27e9)
      (le_iSup\u2082 (f := fun i (_ : i \u2208 Finset.univ.erase v) => G.edist c i)
        m.val m.property)\u27e9
  obtain \u27e8y, hy, hyc\u27e9 := hsup
  have hyv : y \u2260 v := (Finset.univ.mem_erase.mp hy).1
  have hstep : eccOn G (Finset.univ.erase v) c + 1 \u2264 G.eccent c := by
    rw [hyc]
    have hlt : G.edist c y < G.eccent c :=
      edist_lt_eccent_of_dist_lt hconn (huep.2 y hyv)
    exact Order.lt_iff_add_one_le.mp hlt
  calc radOn G (Finset.univ.erase v) + 1
      \u2264 eccOn G (Finset.univ.erase v) c + 1 :=
        add_le_add_right (radOn_le_eccOn hmem) 1
  _ \u2264 G.eccent c := hstep
  _ = radOn G Finset.univ := by
      rw [radOn_univ_eq_radius, \u2190 hc]
'''

marker = 'end Graffiti84'
assert marker in s, 'marker missing'
s = s.replace(marker, add + '\n' + marker)
io.open(p, 'w', encoding='utf-8').write(s)
print('appended', len(add), 'chars')
