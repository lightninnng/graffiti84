# -*- coding: utf-8 -*-
"""Replace F1a/F1b with namespace-corrected, bookkeeping-fixed versions."""

NEW = '''/-! ### Batch 3b: geodesic structure (F1, F2, potential-function acyclicity) -/

/-- **F1a.** A walk realizing the distance has no repeated vertex: any repeat
could be cut out, shortening the walk below the distance. -/
theorem isPath_of_length_eq_dist {G : SimpleGraph α} (hconn : G.Connected)
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v) :
    p.IsPath := by
  rw [SimpleGraph.Walk.isPath_def, List.nodup_iff_count_le_one]
  intro z
  by_contra h1
  push_neg at h1
  have hm : z ∈ p.support := List.count_pos_iff.mp (by omega)
  have hsup : p.support = (p.takeUntil z hm).support ++
      (p.dropUntil z hm).support.tail := by
    conv_lhs => rw [← SimpleGraph.Walk.take_spec p hm]
    exact SimpleGraph.Walk.support_append _ _
  have hc1 : (p.takeUntil z hm).support.count z = 1 :=
    SimpleGraph.Walk.count_support_takeUntil_eq_one p hm
  have hcount : p.support.count z = 1 + (p.dropUntil z hm).support.tail.count z := by
    rw [hsup, List.count_append, hc1]
  have hrest : z ∈ (p.dropUntil z hm).support.tail :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨r, hrmem, hrlen⟩ :
      ∃ r : G.Walk z v, z ∈ r.support ∧ r.length < (p.dropUntil z hm).length := by
    cases hd : p.dropUntil z hm with
    | nil => rw [hd] at hrest; exact absurd hrest (by simp)
    | @cons z' x v'' h r =>
        rw [hd] at hrest
        rw [SimpleGraph.Walk.support_cons] at hrest
        refine ⟨r.dropUntil z hrest, SimpleGraph.Walk.start_mem_support _, ?_⟩
        have h1 : (SimpleGraph.Walk.cons h r).length = r.length + 1 :=
          SimpleGraph.Walk.length_cons h r
        have h2 : (r.dropUntil z hrest).length = r.length - r.support.idxOf z :=
          SimpleGraph.Walk.length_dropUntil r hrest
        have h3 : r.support.idxOf z < r.support.length :=
          List.idxOf_lt_length_of_mem hrest
        rw [SimpleGraph.Walk.length_support] at h3
        rw [hd, h1]
        omega
  have hq : (p.dropUntil z hm).length = p.length - p.support.idxOf z :=
    SimpleGraph.Walk.length_dropUntil p hm
  set w := (p.takeUntil z hm).append r with hwdef
  have hwlen : w.length = p.support.idxOf z + r.length := by
    rw [hwdef, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_takeUntil]
  have hrdist : G.dist u v ≤ w.length := SimpleGraph.dist_le w
  have hil := List.idxOf_lt_length_of_mem hm
  rw [SimpleGraph.Walk.length_support] at hil
  omega

/-- **F1b (chord exclusion).** If two vertices of a geodesic walk's support
are adjacent in `G`, their positions in the support differ by exactly one. -/
theorem geodesic_adj_support_succ {G : SimpleGraph α} (hconn : G.Connected)
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v)
    {a b : α} (ha : a ∈ p.support) (hb : b ∈ p.support) (hadj : G.Adj a b) :
    p.support.idxOf a + 1 = p.support.idxOf b ∨
      p.support.idxOf b + 1 = p.support.idxOf a := by
  by_cases hle : p.support.idxOf a ≤ p.support.idxOf b
  · left
    by_contra hne
    have hbmem : p.support.idxOf b ≤ p.length := by
      have := List.idxOf_lt_length_of_mem hb
      rw [SimpleGraph.Walk.length_support] at this
      omega
    set w := ((p.takeUntil a ha).append (SimpleGraph.Adj.toWalk hadj)).append
      (p.dropUntil b hb) with hwdef
    have hwlen : w.length =
        p.support.idxOf a + 1 + (p.length - p.support.idxOf b) := by
      rw [hwdef, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_takeUntil, SimpleGraph.Walk.length_dropUntil]
      simp [SimpleGraph.Adj.toWalk]
    have hrdist : G.dist u v ≤ w.length := SimpleGraph.dist_le w
    omega
  · right
    by_contra hne
    have hamem : p.support.idxOf a ≤ p.length := by
      have := List.idxOf_lt_length_of_mem ha
      rw [SimpleGraph.Walk.length_support] at this
      omega
    set w := ((p.takeUntil b hb).append (SimpleGraph.Adj.toWalk hadj.symm)).append
      (p.dropUntil a ha) with hwdef
    have hwlen : w.length =
        p.support.idxOf b + 1 + (p.length - p.support.idxOf a) := by
      rw [hwdef, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_takeUntil, SimpleGraph.Walk.length_dropUntil]
      simp [SimpleGraph.Adj.toWalk]
    have hrdist : G.dist u v ≤ w.length := SimpleGraph.dist_le w
    omega
'''

import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()
start_marker = '/-! ### Batch 3b: geodesic structure'
i = s.index(start_marker)
j = s.index('end Graffiti84')
assert i < j
s = s[:i] + NEW + '\n' + s[j:]
assert 'sorry' not in NEW
io.open(p, 'w', encoding='utf-8').write(s)
print('F1a/F1b replaced')
