# -*- coding: utf-8 -*-
"""v16 surgical fixes."""
import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()


def rep(old, new):
    global s
    assert old in s, 'NOT FOUND: ' + old[:90]
    s = s.replace(old, new)


# 1. prepend lemma: drop goal-flipping rw; use eq lemmas
rep("""    G.edist u w \u2264 1 + G.edist v w := by
  rw [SimpleGraph.edist_comm]
  have h1 : G.edist w u \u2264 G.edist w v + 1 :=
    edist_le_add_edge hR.symm huv.symm
  rw [SimpleGraph.edist_comm (u := w) (v := v)] at h1
  calc G.edist u w \u2264 G.edist v w + 1 := h1
  _ = 1 + G.edist v w := (add_comm (G.edist v w) 1)""",
    """    G.edist u w \u2264 1 + G.edist v w := by
  have h1 : G.edist w u \u2264 G.edist w v + 1 :=
    edist_le_add_edge hR.symm huv.symm
  have h2 : G.edist w u = G.edist u w :=
    SimpleGraph.edist_comm (u := w) (v := u)
  have h3 : G.edist w v = G.edist v w :=
    SimpleGraph.edist_comm (u := w) (v := v)
  calc G.edist u w = G.edist w u := h2.symm
  _ \u2264 G.edist w v + 1 := h1
  _ = G.edist v w + 1 := by rw [h3]
  _ = 1 + G.edist v w := (add_comm (G.edist v w) 1)""")

# 2. support induction: nil case body, List.mem_cons
rep("""  | @nil a =>
      have hvu : v = a := by simpa using hpv
      subst hvu
      simp only [SimpleGraph.edist_self, zero_add]
      exact SimpleGraph.edist_le (SimpleGraph.Walk.cons h q)
  | @cons u x w h q ih =>
      have hmem : v \u2208 (SimpleGraph.Walk.cons h q).support := hpv
      rw [SimpleGraph.Walk.support_cons] at hmem
      rcases Finset.mem_cons.mp hmem with rfl | hpv'""",
    """  | @nil a =>
      have hvu : v = a := by simpa using hpv
      subst hvu
      simp [SimpleGraph.edist_self]
  | @cons u x w h q ih =>
      have hmem : v \u2208 (SimpleGraph.Walk.cons h q).support := hpv
      rw [SimpleGraph.Walk.support_cons] at hmem
      rcases List.mem_cons.mp hmem with rfl | hpv'""")

# 3. F7a: intro before obtaining geodesics
rep("""  have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat hne
  -- every geodesic from c to w \u2260 v avoids v""",
    """  have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat hne
  intro x y hx hy
  -- every geodesic from c to w \u2260 v avoids v""")

# 4. F7a hnat2: use hoisted hco1/hco2
rep("""      refine ENat.coe_le_coe.mp ?_
      rw [hcv]
      rw [hcoee, hvw]
      exact hsum""",
    """      refine ENat.coe_le_coe.mp ?_
      rw [hco1, hco2]
      exact hsum""")

# 5. F8 haveI: explicit alpha
rep("""  haveI : Nontrivial \u03b1 :=
    Fintype.one_lt_card_iff_nontrivial.mpr (by omega)""",
    """  haveI : Nontrivial \u03b1 :=
    Fintype.one_lt_card_iff_nontrivial (\u03b1 := \u03b1).mpr (by omega)""")

# 6. F8 heccne: fix the hne pattern
rep("""  have heccne : G.eccent c \u2260 \u22a4 := by
    obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
    intro h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t)
      (by rw [\u2190 ht, h])
  have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat heccne""",
    """  have heccne : G.eccent c \u2260 \u22a4 := by
    obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
    intro h
    rw [\u2190 ht] at h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t) h
  have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat heccne""")

io.open(p, 'w', encoding='utf-8').write(s)
print('v16 patches applied')
