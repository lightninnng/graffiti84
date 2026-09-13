# -*- coding: utf-8 -*-
"""v17 pruned."""
import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()


def rep(old, new):
    global s
    assert old in s, 'NOT FOUND: ' + old[:90]
    s = s.replace(old, new)


