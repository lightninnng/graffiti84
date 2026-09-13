# -*- coding: utf-8 -*-
"""Append batch 3b part 1 (F1a, F1b) to BasicFacts.lean. Direct UTF-8, no escapes."""

ADD = '''
/-! ### Batch 3b: geodesic structure (F1, F2, potential-function acyclicity) -/

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
  set q := p.dropUntil z hm with hqdef
  have hsup : p.support = (p.takeUntil z hm).support ++ q.support.tail := by
    conv_lhs => rw [← SimpleGraph.Walk.take_spec p hm]
    exact SimpleGraph.Walk.support_append _ _
  have hc1 : (p.takeUntil z hm).support.count z = 1 :=
    count_support_takeUntil_eq_one p hm
  have hrest : z ∈ q.support.tail := by
    have hcount : p.support.count z = 1 + q.support.tail.count z := by
      rw [hsup, List.count_append, hc1]
    have := List.count_pos_iff
    omega
  -- extract the cons structure of q and drop from the repeat occurrence
  have hmain : ∃ r : G.Walk z v, z ∈ r.support ∧ r.length < q.length := by
    cases q with
    | nil => exact absurd hrest (by simp)
    | @cons z x v h r =>
        have hcount : (z :: r.support).count z = 1 + r.support.count z := by
          simp [List.count_cons]
        have : z ∈ r.support := by
          by_contra hz'
          rw [List.count_eq_zero_iff] at hz'
          rw [hz'] at hcount
          simp at hcount
          have h2 : p.support.count z = 1 + 0 := by
            rw [hsup, List.count_append, hc1]
            simp [hqdef]
            omega
          omega
        refine ⟨r.dropUntil z this, ?_, ?_⟩
        · exact SimpleGraph.Walk.start_mem_support _
        · rw [length_dropUntil]
          have hil := List.idxOf_lt_length_of_mem this
          have hs : (SimpleGraph.Walk.cons h r).length = r.length + 1 := by
            rw [SimpleGraph.Walk.length_cons]
          rw [hs]
          omega
  obtain ⟨r, hrmem, hrlen⟩ := hmain
  have hlenq : q.length = p.length - p.support.idxOf z := length_dropUntil p hm
  have hlent : (p.takeUntil z hm).length = p.support.idxOf z := length_takeUntil p hm
  set w := (p.takeUntil z hm).append r with hwdef
  have hwlen : w.length = p.length - p.support.idxOf z + r.length := by
    rw [hwdef, SimpleGraph.Walk.length_append, hlent]
  have hrdist : G.dist u v ≤ w.length := SimpleGraph.dist_le w
  -- r.length < q.length = p.length - idxOf, so total < p.length
  have hridx : p.support.idxOf z ≤ p.length := by
    have := List.idxOf_lt_length_of_mem hm
    rw [SimpleGraph.Walk.length_support] at this
    omega
  omega

/-- **F1b (chord exclusion).** If two vertices of a geodesic walk's support
are adjacent in `G`, their positions in the support differ by exactly one. -/
theorem geodesic_adj_support_succ {G : SimpleGraph α} (hconn : G.Connected)
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v)
    {a b : α} (ha : a ∈ p.support) (hb : b ∈ p.support) (hadj : G.Adj a b) :
    p.support.idxOf a + 1 = p.support.idxOf b ∨
      p.support.idxOf b + 1 = p.support.idxOf a := by
  by_cases hle : p.support.idxOf a ≤ p.support.idxOf b
  · -- forward direction: idxOf a + 1 = idxOf b (else a chord shortens)
    left
    by_contra hne
    push_neg at hne
    have hbmem : p.support.idxOf b ≤ p.length := by
      have := List.idxOf_lt_length_of_mem hb
      rw [SimpleGraph.Walk.length_support] at this
      omega
    set w := ((p.takeUntil a ha).append (SimpleGraph.Adj.toWalk hadj)).append
      (p.dropUntil b hb) with hwdef
    have hwlen : w.length =
        p.support.idxOf a + 1 + (p.length - p.support.idxOf b) := by
      rw [hwdef, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
        length_takeUntil, length_dropUntil]
      simp [SimpleGraph.Adj.toWalk]
    have hrdist : G.dist u v ≤ w.length := SimpleGraph.dist_le w
    omega
  · right
    by_contra hne
    push_neg at hne
    have hamem : p.support.idxOf a ≤ p.length := by
      have := List.idxOf_lt_length_of_mem ha
      rw [SimpleGraph.Walk.length_support] at this
      omega
    set w := ((p.takeUntil b hb).append (SimpleGraph.Adj.toWalk hadj.symm)).append
      (p.dropUntil a ha) with hwdef
    have hwlen : w.length =
        p.support.idxOf b + 1 + (p.length - p.support.idxOf a) := by
      rw [hwdef, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
        length_takeUntil, length_dropUntil]
      simp [SimpleGraph.Adj.toWalk]
    have hrdist : G.dist u v ≤ w.length := SimpleGraph.dist_le w
    omega
'''

import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()
marker = 'end Graffiti84'
assert marker in s
assert s.count(marker) == 1
assert 'sorry' not in ADD and 'admit' not in ADD
s = s.replace(marker, ADD + '\n' + marker)
io.open(p, 'w', encoding='utf-8').write(s)
print('appended F1a + F1b')
