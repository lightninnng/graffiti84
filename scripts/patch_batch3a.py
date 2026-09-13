# -*- coding: utf-8 -*-
"""Append treeNumber definition + F14 to BasicFacts.lean."""
import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()

add = '''
/-! ### The largest induced tree number t(G) -/

/-- `S` induces a connected subgraph: any two of its vertices are joined by a
walk staying inside `S`. -/
def ConnectsWithin (G : SimpleGraph \u03b1) (S : Finset \u03b1) (a b : \u03b1) : Prop :=
  \u2203 w : G.Walk a b, \u2200 z \u2208 w.support, z \u2208 S

/-- `S` induces a forest: no nontrivial cycle stays inside `S`. -/
def AcyclicWithin (G : SimpleGraph \u03b1) (S : Finset \u03b1) : Prop :=
  \u2200 a : \u03b1, \u2200 w : G.Walk a a,
    (\u2200 z \u2208 w.support, z \u2208 S) \u2192 w.length = 0 \u2228 \u00ac w.IsCycle

/-- `S` induces a tree: connected within `S`, and no cycle within `S`
(the empty and singleton sets count as trees here). -/
def IsInducedTree (G : SimpleGraph \u03b1) (S : Finset \u03b1) : Prop :=
  (\u2200 a \u2208 S, \u2200 b \u2208 S, ConnectsWithin G S a b) \u2227 AcyclicWithin G S

/-- The largest order of an induced tree. -/
open Classical in
noncomputable def treeNumber (G : SimpleGraph \u03b1) : \u2115 :=
  (Finset.univ.filter (fun S : Finset \u03b1 => IsInducedTree G S)).sup
    (fun S => S.card)

/-- **F14 (heredity).** Induced trees avoiding `v` are bounded by `t(G)`;
this is the ambient form of `t(G - v) \u2264 t(G)`. -/
lemma treeNumber_mono_erase {G : SimpleGraph \u03b1} {v : \u03b1} :
    (Finset.univ.filter (fun S : Finset \u03b1 =>
      IsInducedTree G S \u2227 S \u2286 Finset.univ.erase v)).sup (fun S => S.card)
      \u2264 treeNumber G := by
  refine Finset.sup_le ?_
  intro S hS
  exact Finset.le_sup (Finset.mem_filter.mpr \u27e8hS.1, hS.2.1\u27e9)
'''

marker = 'end Graffiti84'
assert marker in s
s = s.replace(marker, add + '\n' + marker)
io.open(p, 'w', encoding='utf-8').write(s)
print('appended treeNumber + F14')
