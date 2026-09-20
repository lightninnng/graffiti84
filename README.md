# Graffiti.pc Conjecture 84 — local Lean workspace

Pinned environment:

- Lean `v4.32.2`
- Mathlib `v4.32.2`

## Verification in GitHub Actions

Lean runs in the GitHub-hosted Ubuntu runner in `.github/workflows/ci.yml`.
The local workspace is used for editing and reading Mathlib source only.
Pushes to `main` or `codex/**` run dependency resolution, Mathlib cache fetch
(with retries), `lake build`, source auditing, and declaration axiom reports.

## Final theorem

`Graffiti84.graphConjecture84` proves, for every finite connected nontrivial
simple graph `G`,

```lean
2 * G.radius.toNat ≤ treeNumber G * minDegree G
```

Here `treeNumber` is the maximum number of vertices in an induced tree,
and `minDegree` is the minimum vertex degree. There are no radius-critical
or structural hypotheses in the final theorem.

The proof uses the geodesic bound when the minimum degree is at least two.
The degree-one case is `Graffiti84.leafLemma`, proved by induction over the
vertex count. Case A uses direct leaf peeling; Case B uses a rooted induced
tree. A complete corona classification is not needed.

The CI audit builds both final declarations and prints their axiom
dependencies. Check the GitHub Actions result for the exact commit being used.

## Integrity rule

No `sorry`, `admit`, or custom `axiom` occurs in the Lean proofs.
The final theorem's dependencies are inspected with `#print axioms` in
`scripts/axioms.lean`, alongside the source audit.

## Proof guide

- [最终形式化证明导读（中文）](docs/formal-proof-guide.md)
- [Case A 的直接剥叶归纳](docs/case-a-induction.md)
- [最终定理源码](Graffiti84/GraphConjecture84.lean)
- [叶子引理源码](Graffiti84/LeafLemma.lean)

The older `docs/full-proof.md`, `docs/conjecture-logic.md`, and manuscript
retain the historical structural-classification route. They are not a
line-by-line description of the final Lean proof.
