# -*- coding: utf-8 -*-
"""Count and restore literal unicode-escape sequences in BasicFacts.lean."""
import io

p = 'Graffiti84/BasicFacts.lean'
s = io.open(p, encoding='utf-8').read()
BS = chr(92)  # backslash
hexd = set('0123456789abcdef')
count = 0
kinds = {}
i = 0
out = []
n = len(s)
while i < n:
    if (s[i] == BS and i + 5 < n and s[i + 1] == 'u'
            and all(c in hexd for c in s[i + 2:i + 6])):
        esc = s[i:i + 6]
        kinds[esc] = kinds.get(esc, 0) + 1
        count += 1
        out.append(chr(int(s[i + 2:i + 6], 16)))
        i += 6
    else:
        out.append(s[i])
        i += 1
print('total escapes:', count)
print('kinds:', kinds)
io.open(p, 'w', encoding='utf-8').write(''.join(out))
print('restored')
