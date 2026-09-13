# -*- coding: utf-8 -*-
"""v14 comprehensive fixes for BasicFacts batch 2."""
import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()


def rep(old, new, count=None):
    global s
    n = s.count(old)
    assert n > 0, 'NOT FOUND: ' + old[:80]
    if count is not None:
        assert n == count, 'COUNT %d != %d for: %s' % (n, count, old[:80])
    s = s.replace(old, new)


# A. IsCentral def sinks into BasicFacts (before the F7 section)
rep('/-! ### F7: the drop half of the criterion -/',
    '''/-- A vertex is central iff it realizes the graph radius. -/
def IsCentral (G : SimpleGraph \u03b1) (v : \u03b1) : Prop :=
  G.eccent v = G.radius

/-! ### F7: the drop half of the criterion -/''')

# B. global hne-pattern fix (rw [<- ht] at h)
old_hne = """    intro h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t)
      (by rw [\u2190 ht, h])"""
new_hne = """    intro h
    rw [\u2190 ht] at h
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t) h"""
rep(old_hne, new_hne, count=5)

# F5's hfin variant (same pattern, different lemma names)
old_hfin = """      intro h
      exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t)
        (by rw [\u2190 ht, h])"""
new_hfin = """      intro h
      rw [\u2190 ht] at h
      exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t) h"""
rep(old_hfin, new_hfin, count=1)

# C. edist_le_add_edge_prepend
rep("""  rw [SimpleGraph.edist_comm]
  have h1 : G.edist w u \u2264 G.edist w v + 1 :=
    edist_le_add_edge hR.symm huv.symm
  rw [SimpleGraph.edist_comm (G := G) v w] at h1
  linarith""",
    """  rw [SimpleGraph.edist_comm]
  have h1 : G.edist w u \u2264 G.edist w v + 1 :=
    edist_le_add_edge hR.symm huv.symm
  rw [SimpleGraph.edist_comm (u := w) (v := v)] at h1
  calc G.edist u w \u2264 G.edist v w + 1 := h1
  _ = 1 + G.edist v w := (add_comm (G.edist v w) 1)""")

# D. support-lemma induction fixes
rep("""  induction p with
  | nil =>
      have hvu : v = u := by simpa using hpv
      subst hvu
      simp [SimpleGraph.edist_self]
  | @cons u x w h q ih =>
      rcases Finset.mem_cons.mp
        (by simpa [SimpleGraph.Walk.support_cons] using hpv) with rfl | hpv'
      \u00b7 simp
        exact SimpleGraph.edist_le (SimpleGraph.Walk.cons h q)""",
    """  induction p with
  | @nil a =>
      have hvu : v = a := by simpa using hpv
      subst hvu
      simp only [SimpleGraph.edist_self, zero_add]
      exact SimpleGraph.edist_le (SimpleGraph.Walk.cons h q)
  | @cons u x w h q ih =>
      have hmem : v \u2208 (SimpleGraph.Walk.cons h q).support := hpv
      rw [SimpleGraph.Walk.support_cons] at hmem
      rcases Finset.mem_cons.mp hmem with rfl | hpv'
      \u00b7 simp only [SimpleGraph.edist_self, zero_add]
        exact SimpleGraph.edist_le (SimpleGraph.Walk.cons h q)""")

# E. F7a: hoist coe lemmas, fix h2/h3
rep("""  have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat hne
  intro x y hx hy""",
    """  have hcoee : ((G.eccent c).toNat : \u2115\u221e) = G.eccent c := ENat.coe_toNat hne
  have hco1 : ((G.edist c v).toNat : \u2115\u221e) = G.edist c v :=
    ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
      (hconn.preconnected c v))
  have hco2 : ((G.edist v x).toNat : \u2115\u221e) = G.edist v x :=
    ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
      (hconn.preconnected v x))
  have hco3 : ((G.edist c x).toNat : \u2115\u221e) = G.edist c x :=
    ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr
      (hconn.preconnected c x))
  intro x y hx hy""")

rep("""    have h2 : ((G.edist c v).toNat : \u2115) + ((G.edist v x).toNat : \u2115)
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
      exact hqx""",
    """    have h2 : ((G.edist c v).toNat + (G.edist v x).toNat : \u2115)
        \u2264 (G.edist c x).toNat := by
      refine ENat.coe_le_coe.mp ?_
      push_cast
      rw [hco1, hco2, hco3]
      exact hsum
    have h3 : (G.edist c x).toNat < (G.eccent c).toNat := by
      refine ENat.coe_lt_coe.mp ?_
      rw [hco3, hcoee]
      exact hqx""")

# F. F7b: le_iff direction + componentwise add
rep("""    exact (ENat.add_one_le_iff' (hn := hstep_ne_top)).mp hlt""",
    """    exact (ENat.add_one_le_iff' (hn := hstep_ne_top)
      (m := G.edist c y)).mpr hlt""")
rep("""        add_le_add_right (radOn_le_eccOn hmem) 1""",
    """        add_le_add (radOn_le_eccOn hmem) (le_refl 1)""")

# G. F8 hSe membership proofs
rep("""      by_contra hw
      exact hall \u27e8w, hw\u27e9""",
    """      by_contra hw
      exact hall \u27e8w, Finset.mem_erase.mpr \u27e8hw, Finset.mem_univ w\u27e9\u27e9""")
rep("""    have hsub : (Finset.univ : Finset \u03b1) = {v} :=
      Finset.eq_singleton_iff_unique_mem.2 \u27e8rfl, fun x _ => hv x\u27e9""",
    """    have hsub : (Finset.univ : Finset \u03b1) = {v} :=
      Finset.eq_singleton_iff_unique_mem.2
        \u27e8Finset.mem_univ v, fun x _ => hv x\u27e9""")

# H. F8 hall: explicit named args
rep("""  have hall : \u2200 x : \u03b1, x \u2260 v \u2192 G.edist c x \u2264 \u03c1 := fun x hx =>
    edist_le_eccOn (Finset.mem_erase.mpr \u27e8hx, Finset.mem_univ x\u27e9)""",
    """  have hall : \u2200 x : \u03b1, x \u2260 v \u2192 G.edist c x \u2264 \u03c1 := fun x hx =>
    edist_le_eccOn (G := G) (S := Finset.univ.erase v) (c := c)
      (Finset.mem_erase.mpr \u27e8hx, Finset.mem_univ x\u27e9)""")

# I. F5: univ nonempty + rw order in hcz
rep("""  obtain \u27e8c, hc, hcmin\u27e9 := eccOn_eq_radOn_attained
    (G := G) (S := Finset.univ) (by simp)""",
    """  obtain \u27e8c, hc, hcmin\u27e9 := eccOn_eq_radOn_attained
    (G := G) (S := Finset.univ) Finset.univ_nonempty""")
rep("""    rw [h] at hcen
    have hcor := radius_lt_eccOn_of_isLeaf hconn hdeg hzp hn3
    rw [hcen] at hcor""",
    """    rw [h] at hcen
    have hcor := radius_lt_eccOn_of_isLeaf hconn hdeg hzp hn3
    rw [\u2190 eccOn_univ_eq_eccent, hcen] at hcor""")

io.open(p, 'w', encoding='utf-8').write(s)
print('v14 patches applied')
