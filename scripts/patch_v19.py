rep('step1', """        have step1 : G.edist u v + G.edist v w \u2264 (1 + G.edist x v) + G.edist v w :=
          add_le_add_right hpre _""",
    """        have step1 : G.edist u v + G.edist v w \u2264 (1 + G.edist x v) + G.edist v w :=
          add_le_add_left hpre (G.edist v w)""")

# 2. hnat2: push_cast before the coe rewrites
rep('hnat2', """      refine ENat.coe_le_coe.mp ?_
      rw [hco1, hco2]
      exact hsum""",
    """      refine ENat.coe_le_coe.mp ?_
      push_cast
      rw [hco1, hco2]
      exact hsum""")

# 3. F8 haveI: explicit alpha
rep('haveI', """  haveI : Nontrivial α :=
    Fintype.one_lt_card_iff_nontrivial (α := α).mpr (by omega)""",
    """  haveI : Nontrivial α := by
    by_contra hnt
    have hall2 : ∀ w : α, w = v := by
      intro w
      by_contra hw
      exact hnt ⟨v, w, fun hh => hw hh.symm⟩
    have hsub : (Finset.univ : Finset α) = {v} :=
      Finset.eq_singleton_iff_unique_mem.2
        ⟨Finset.mem_univ v, fun x _ => hall2 x⟩
    have hcard2 : Fintype.card α = (Finset.univ : Finset α).card := rfl
    rw [hsub] at h2
    simp at h2
    omega""")

rep('hcen-heq', """  have hcen : IsCentral G c := le_antisymm hecc SimpleGraph.radius_le_eccent
  have heq : G.eccent c = radOn G (Finset.univ.erase v) + 1 := by
    rw [hc, hradius]""",
    """  have hcen : IsCentral G c := le_antisymm hecc SimpleGraph.radius_le_eccent
  have heq : G.eccent c = radOn G (Finset.univ.erase v) + 1 := by
    refine le_antisymm hecc ?_
    rw [\u2190 hradius]
    exact SimpleGraph.radius_le_eccent""")

# 5. UEP.1 calc: preconnected c w (not c v)
rep('f5-nonempty', """  have hcz : c \u2260 z := by
    intro h""",
    """  have hcz : c \u2260 z := by
    haveI : Nonempty \u03b1 := \u27e8z\u27e9
    intro h""")

# 8. F5 hfin: eq_top_iff route
rep('f5-hfin', """    have hfin : G.radius \u2260 \u22a4 := by
      obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
      intro h
      rw [\u2190 ht, h]
      exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t) h""",
    """    have hfin : G.radius \u2260 \u22a4 := by
      have h1 : G.radius \u2264 G.eccent c := SimpleGraph.radius_le_eccent
      obtain \u27e8t, ht\u27e9 := G.exists_edist_eq_eccent_of_finite c
      intro h
      rw [h, ht] at h1
      exact absurd (eq_top_iff.mpr h1)
        (SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected c t))""")

io.open(p, 'w', encoding='utf-8').write(s)
print('applied:', applied)
