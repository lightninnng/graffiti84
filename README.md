# Graffiti.pc Conjecture 84 — local Lean workspace

Pinned environment:

- Lean `v4.32.2`
- Mathlib `v4.32.2`

## First local run

```bash
lake update
lake exe cache get
lake build
```

For faster diagnosis, compile layer by layer:

```bash
lake build Graffiti84.RadiusCriticalStructure
lake build Graffiti84.LeafLemma
lake build Graffiti84.GraphConjecture84
```

If the first command reports an API mismatch, send the complete terminal
output back to ChatGPT.  Fix the first failing layer before continuing.

## Integrity rule

This project intentionally contains no `sorry`, `admit`, or custom `axiom`.
Undeveloped major theorems are left as comments/TODO targets, not fake theorem
declarations.

## Target architecture

1. `RadiusCriticalStructure.lean`
   - radius deletion / unique-eccentric-point machinery
   - rooted Chung helper
   - theorem-specific vrd cut-vertex structure theorem

2. `LeafLemma.lean`
   - minimum-counterexample two-case proof
   - final theorem `leafLemma`

3. `GraphConjecture84.lean`
   - minimum-degree split
   - final theorem for Graffiti.pc #84

The current snapshot is a local-compilation starting point, not yet a claim
that the full theorem has been kernel-certified.

## Docs

- [docs/conjecture-logic.md](docs/conjecture-logic.md) — 猜想陈述、证明逻辑依赖图、
  复查发现的简化（ESS 可移除、下降判据拆两半）、隐式步骤清单与形式化路线图（中文）。
