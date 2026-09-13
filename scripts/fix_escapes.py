# -*- coding: utf-8 -*-
"""Restore literal unicode-escape sequences in BasicFacts.lean."""
import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()
hexd = set('0123456789abcdef')
out = []
fixed = []
i = 0
n = len(s)
while i < n:
    if (s[i] == '\\' and i + 5 < n and s[i + 1] == 'u'
            and all(c in hexd for c in s[i + 2:i + 6])):
        code = int(s[i + 2:i + 6], 16)
        out.append(chr(code))
        fixed.append(s[i:i + 6])
        i += 6
    else:
        out.append(s[i])
        i += 1
io.open(p, 'w', encoding='utf-8').write(''.join(out))
print('fixed count:', len(fixed))
print('kinds:', sorted(set(fixed)))
