"""Scan Lean sources for forbidden proof placeholders.

Strips Lean block comments (/- ... -/, which nest) and line comments (-- ...),
then flags any occurrence of `sorry`/`admit` and any `axiom` declaration.
Exit code 0 = clean, 1 = violation found.
"""
import re
import sys
from pathlib import Path


def strip_comments(text: str) -> str:
    out = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        else:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("--", i):
                while i < n and text[i] != "\n":
                    i += 1
            elif text.startswith('"""', i):
                j = text.find('"""', i + 3)
                j = n if j == -1 else j + 3
                out.append(text[i:j])
                i = j
            else:
                out.append(text[i])
                i += 1
    return "".join(out)


def main() -> int:
    root = Path("Graffiti84")
    violations = []
    for path in sorted(root.rglob("*.lean")):
        code = strip_comments(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(code.splitlines(), 1):
            if re.search(r"\b(sorry|admit)\b", line) or re.match(
                r"\s*(private\s+|protected\s+|scoped\s+)*axiom\s", line
            ):
                violations.append(f"{path}:{lineno}: {line.strip()}")
    if violations:
        print("Forbidden proof placeholder/axiom found:")
        for v in violations:
            print(" ", v)
        return 1
    print("Audit clean: no sorry/admit/axiom in Lean sources.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
