# Graffiti.pc Conjecture 84 — A Complete Lean 4 Formalization

[![CI](https://github.com/lightninnng/graffiti84/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/lightninnng/graffiti84/actions/workflows/ci.yml)

This repository contains a complete, machine-checked proof of Graffiti.pc
Conjecture 84 (Fajtlowicz):

> For every finite, connected simple graph `G` with at least two vertices,
> **2·r(G) ≤ t(G)·δ(G)**, where `r(G)` is the radius, `t(G)` is the maximum
> number of vertices in an induced tree, and `δ(G)` is the minimum degree.

The final declaration is
[`Graffiti84.graphConjecture84`](Graffiti84/GraphConjecture84.lean). It is
compiled and audited by GitHub Actions on a clean Ubuntu sandbox on every push.

## Formal statement

```lean
theorem graphConjecture84 {α : Type u} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hG : G.Connected) :
    2 * G.radius.toNat ≤ treeNumber G * minDegree G
```

The typeclass arguments fix the setting: `Fintype α` + `DecidableEq α` restrict
`α` to finite vertex sets, `Nontrivial α` means at least two vertices, and
`hG : G.Connected` is connectedness. The three graph invariants are standard:

- `G.radius` — Mathlib's `SimpleGraph.radius` (valued in `ℕ∞`), coerced by
  `.toNat`;
- `treeNumber G` — the maximum order of an induced tree, defined in
  `Graffiti84/BasicFacts.lean` (`IsInducedTree G S` requires `S` to be
  connected and acyclic inside itself; `treeNumber` takes the supremum of
  `S.card`);
- `minDegree G` — defined in `Graffiti84/GraphConjecture84.lean`.

The theorem carries no radius-critical or structural side hypotheses — the
assumptions are exactly the hypotheses of the conjecture.

## Evidence

All of the following runs automatically in CI on every push
(`.github/workflows/ci.yml`); the latest run on `main` reports:

1. **Clean-room build passes.** On a fresh Ubuntu runner CI installs elan,
   resolves dependencies, fetches the Mathlib cache, and runs `lake build`,
   reporting `Build completed successfully (8669 jobs)`.
2. **Source audit is clean.** `scripts/audit_scan.py` scans all Lean sources
   (comments stripped first); the log shows
   `Audit clean: no sorry/admit/axiom in Lean sources.` — no `sorry`, no
   `admit`, and no custom `axiom` declarations.
3. **Axiom dependencies collapse to the three standard Lean axioms.**
   `scripts/axioms.lean` runs `#print axioms` on the final theorem and 13 key
   intermediate results (`leafLemma`, `vrd_cut_tree_bound`, the
   `rooted_chung` route, …). Every one prints

   ```text
   'Graffiti84.graphConjecture84' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   These are Lean's logical axioms (propositional extensionality, classical
   choice, quotients) that every Mathlib theorem also depends on; nothing
   graph-theoretic or arithmetic is assumed.

## Independent verification

- **Online**: trigger the `Lean CI` workflow manually on any commit (it
  supports `workflow_dispatch`), or download the full logs of any run from
  the Actions page.
- **Locally**:

  ```bash
  curl https://elan.lean-lang.org/elan_init.sh -sSf | sh -s -- -y
  lake exe cache get   # fetch the prebuilt Mathlib cache
  lake build           # build all 13 modules
  bash scripts/audit.sh
  ```

  The environment is pinned — Lean `v4.32.2`, Mathlib `v4.32.2`
  (`lake-manifest.json` pins commit `905b9581…`) — so CI and local runs
  check the same mathematics.

## Proof architecture

About 4,800 lines of Lean across 13 modules (`Graffiti84.lean` re-imports
them all):

| Module | Content |
| --- | --- |
| `BasicFacts` | Restricted radius `radOn` / eccentricity `eccOn`, `IsInducedTree`, `treeNumber`, unique eccentric points `IsUniqueEccentricPoint`, and basic distance/radius facts |
| `Deletion` | Radius comparisons under vertex deletion vs. induced subgraphs; the equivalence "radius drops ⟺ unique eccentric point" |
| `InducedTree` | Heredity of induced trees under taking induced subgraphs |
| `MaximalTree` | A maximum induced tree contains two non-cut vertices; `treeNumber` lower bounds when growing by leaves |
| `EndBlocks` | End-block structure: deletion connectivity of longest-path endpoints, uniqueness of a leaf's neighbor (`unique_leaf_neighbor`), … |
| `RootedChung` | A rooted Chung-type lemma (`rooted_chung`): chord-controlled walks from any root span an induced tree |
| `RadiusCriticalStructure` | Structure of radius-critical graphs: existence of a degree-one neighbor |
| `CaseA` | Main theorem `vrd_cut_tree_bound`: every non-cut deletion lowers the radius and the graph has a cut vertex |
| `CaseB` | The `drop_except` family: with a single exceptional deletion, all centers are unique eccentric points and span rooted induced trees |
| `LeafCore` | The non-leaf core has radius exactly one less |
| `LeafDeletion` | Lifting the center / unique-eccentric-point structure across leaf deletion |
| `LeafLemma` | `leafLemma`: `2r ≤ t·δ` for graphs with a leaf, by strong induction on the vertex count (Cases A and B supply the two recursions) |
| `GraphConjecture84` | Without leaves `δ ≥ 2` and geodesics give `2r ≤ t`; combines everything into the final theorem |

The proof line (see the [guide](docs/formal-proof-guide.md), in Chinese):

1. Dispatch on the existence of a degree-one vertex: with a leaf use
   `leafLemma`; without leaves `δ ≥ 2` and a geodesic directly gives
   `2r ≤ t`, then scale the inequality;
2. The leaf case goes by strong induction on the vertex count, the key
   invariant being that deleting the right vertex drops the radius by
   exactly one (characterized by unique eccentric points);
3. Case A recurses by peeling leaves off a maximum induced tree with two
   non-cut vertices;
4. Case B uses the rooted Chung lemma to grow a large enough induced tree
   from the single exceptional deletion;
5. No full corona classification is needed — a shorter route than the
   original manuscript.

## Documentation

- [Guide to the final formal proof (Chinese)](docs/formal-proof-guide.md) —
  a section-by-section walkthrough
- [The Case A leaf-peeling induction (Chinese)](docs/case-a-induction.md)
- [Final theorem source](Graffiti84/GraphConjecture84.lean) ·
  [Leaf lemma source](Graffiti84/LeafLemma.lean)
- `paper/graffiti84.tex` (with PDF) — the self-contained pen-and-paper proof

## Layout

```text
Graffiti84/   13 Lean modules plus the aggregate entry Graffiti84.lean
docs/         proof guides
paper/        pen-and-paper proof (LaTeX/PDF)
scripts/      CI audit scripts (sorry/admit/axiom scan and #print axioms)
```
