# -*- coding: utf-8 -*-
"""C2b: idxOf_reverse_mem helper only (keep CI green); main theorem next round."""

ADD = r'''
private lemma idxOf_reverse_mem {β : Type*} [BEq β] [LawfulBEq β] :
    ∀ (l : List β) (x : β), x ∈ l →
      List.idxOf x l.reverse + List.idxOf x l = l.length - 1 := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons h r ih =>
      intro x hx
      by_cases hxe : x = h
      · subst hxe
        simp [List.idxOf_cons_eq]
        omega
      · have hxr : x ∈ r := by
          by_contra hc
          rw [List.mem_cons] at hx
          rcases hx with h1 | h2
          · exact hxe h1
          · exact hc h2
        have hrec := ih x hxr
        rw [List.reverse_cons, List.idxOf_append_of_notMem (by
          intro hc
          simp only [List.mem_singleton] at hc
          exact hxe hc),
          List.idxOf_cons_eq hxe r h]
        simp only [List.length_reverse, List.length_cons]
        omega
'''

import io
import re

p = 'Graffiti84/RootedChung.lean'
s = io.open(p, encoding='utf-8').read()
marker = 'end Graffiti84'
assert marker in s
assert not re.search(r'\b(sorry|admit)\b', ADD)
s = s.replace(marker, ADD + '\n' + marker)
io.open(p, 'w', encoding='utf-8').write(s)
print('idxOf_reverse_mem appended')
