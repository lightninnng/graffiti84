import re
from collections import Counter

src = open('paper/graffiti84.tex', encoding='utf-8').read()
begins = re.findall(r'\\begin\{(\w+\*?)\}', src)
ends = re.findall(r'\\end\{(\w+\*?)\}', src)
b, e = Counter(begins), Counter(ends)
bad = {k: (b[k], e[k]) for k in set(b) | set(e) if b[k] != e[k]}
print("unbalanced envs:", bad or "none")
print("brace balance:", src.count('{') - src.count('}'))
labels = set(re.findall(r'\\label\{([^}]+)\}', src))
refs = set(re.findall(r'\\ref\{([^}]+)\}', src)) | set(re.findall(r'\\eqref\{([^}]+)\}', src))
print("dangling refs:", (refs - labels) or "none")
print("unused labels:", (labels - refs) or "none")
cites = set(re.findall(r'\\cite\{([^}]+)\}', src))
bibs = set(re.findall(r'\\bibitem\{([^}]+)\}', src))
flat = {c.strip() for grp in cites for c in grp.split(',')}
print("dangling cites:", (flat - bibs) or "none")
print("uncited bibitems:", (bibs - flat) or "none")
