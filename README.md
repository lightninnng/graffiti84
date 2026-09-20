# Graffiti.pc Conjecture 84 — local Lean workspace

Pinned environment:

- Lean `v4.32.2`
- Mathlib `v4.32.2`

## Verification in GitHub Actions

Lean runs in the GitHub-hosted Ubuntu runner in `.github/workflows/ci.yml`.
The local workspace is used for editing and reading Mathlib source only.
Pushes to `main` or `codex/**` run dependency resolution, Mathlib cache fetch
(with retries), `lake build`, source auditing, and declaration axiom reports.

## Formalization status

The full conjecture is **not yet formalized**. A successful build checks the
implemented declarations, not the existence of the final theorem.

Implemented components include:

- `BasicFacts`: geodesics, induced-tree size, ambient-distance bookkeeping.
- `RootedChung`: a rooted induced-tree witness on at least `2r - 1` vertices.
- `Deletion`: comparison with genuine induced-subgraph radii and both UEP
  radius-drop directions.
- `EndBlocks`: non-cut vertices, unique leaf neighbours, and Case B's
  non-cut closure without block decomposition.
- `CaseB`: self-centrality, the exceptional UEP witness, and the rooted tree.
- `LeafLemma`: induced-tree leaf extension and counting.
- `GraphConjecture84`: the minimum-degree-at-least-two branch.

Remaining: Case A's peeling/structure induction; induced-subgraph bookkeeping
for the minimal-counterexample induction; `leafLemma`; and the unconditional
`graphConjecture84` declaration. The mathematical manuscript is a proof draft,
not a substitute for those missing Lean declarations.

## Integrity rule

This project intentionally contains no `sorry`, `admit`, or custom `axiom`.
Undeveloped major theorems are left as comments/TODO targets, not fake theorem
declarations.

## Docs

- [docs/conjecture-logic.md](docs/conjecture-logic.md) — 猜想陈述、证明逻辑依赖图、
  复查发现的简化（ESS 可移除、下降判据拆两半）、隐式步骤清单与形式化路线图（中文）。
