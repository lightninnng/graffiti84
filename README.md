# Graffiti.pc 猜想 84 的 Lean 4 形式化证明

[![CI](https://github.com/lightninnng/graffiti84/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/lightninnng/graffiti84/actions/workflows/ci.yml)

本仓库给出 Graffiti.pc 猜想 84（Fajtlowicz）的完整机器检查证明：

> 对每个有限、连通、至少两个顶点的简单图 `G`，有 **2·r(G) ≤ t(G)·δ(G)**，
> 其中 `r(G)` 是半径，`t(G)` 是最大诱导树的顶点数，`δ(G)` 是最小度。

最终声明是 [`Graffiti84.graphConjecture84`](Graffiti84/GraphConjecture84.lean)，
在 GitHub Actions 的干净 Ubuntu 沙盒里通过 `lake build` 编译与 axiom 审计。

## 形式化陈述

```lean
theorem graphConjecture84 {α : Type u} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hG : G.Connected) :
    2 * G.radius.toNat ≤ treeNumber G * minDegree G
```

类型参数的含义：`Fintype α` + `DecidableEq α` 把 `α` 上的简单图限定为有限图，
`Nontrivial α` 即至少两个顶点，`hG : G.Connected` 是连通性。三个图参数均为
Mathlib/本仓库的标准定义：

- `G.radius`：Mathlib 的 `SimpleGraph.radius`（`ℕ∞` 值），`.toNat` 转自然数；
- `treeNumber G`：最大诱导树顶点数，见 `Graffiti84/BasicFacts.lean`
  （`IsInducedTree G S` 定义为 `S` 内连通且无环，`treeNumber` 取其上确界）；
- `minDegree G`：最小度，见 `Graffiti84/GraphConjecture84.lean`。

定理没有任何半径临界性或其他结构性附加假设——假设恰好就是猜想的前提。

## 可靠性证据

以下均由 CI 在每次推送时自动执行（`.github/workflows/ci.yml`），最近一次
`main` 上的运行结果（提交 `ee9af97`）：

1. **干净环境编译通过**：CI 在全新 Ubuntu runner 上安装 elan、解析依赖、
   拉取 Mathlib 缓存后执行 `lake build`，日志显示
   `Build completed successfully (8669 jobs)`。
2. **源码审计干净**：`scripts/audit_scan.py` 扫描全部 Lean 源码（先剥离注释），
   日志显示 `Audit clean: no sorry/admit/axiom in Lean sources.`，
   即没有 `sorry`、`admit`，也没有自定义 `axiom` 声明。
3. **公理依赖收敛于 Lean 三条标准公理**：`scripts/axioms.lean` 用
   `#print axioms` 检查最终定理及 13 个关键中间声明（`leafLemma`、
   `vrd_cut_tree_bound`、`rooted_chung` 路线上的各定理等），全部输出

   ```text
   'Graffiti84.graphConjecture84' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   这三条是 Lean 内核的逻辑公理（命题外延性、经典选择、商类型），所有
   Mathlib 定理同样依赖它们；不依赖任何图论或算术方面的额外假设。

编译结果以所审提交的 GitHub Actions 为准；本仓库不要求信任本地环境。

## 独立验证

- **在线**：在 Actions 页面对任意提交手动触发 `Lean CI`
  （workflow 支持 `workflow_dispatch`），或在任一运行页面下载完整日志。
- **本地**：

  ```bash
  curl https://elan.lean-lang.org/elan_init.sh -sSf | sh -s -- -y
  lake exe cache get   # 拉取 Mathlib 预编译缓存
  lake build           # 编译全部 13 个模块
  bash scripts/audit.sh
  ```

  环境已钉死：Lean `v4.32.2`、Mathlib `v4.32.2`
  （`lake-manifest.json` 固定为 `905b9581…`），CI 与本地语义一致。

## 证明结构

约 4800 行 Lean，按依赖分 13 个模块（`Graffiti84.lean` 汇总导入）：

| 模块 | 内容 |
| --- | --- |
| `BasicFacts` | 受限半径 `radOn`/离心度 `eccOn`、`IsInducedTree`、`treeNumber`、唯一离心点 `IsUniqueEccentricPoint` 等基础定义与距离/半径基本事实 |
| `Deletion` | 删点半径与诱导子图半径的比较；"半径下降 ⟺ 唯一离心点"的等价转换 |
| `InducedTree` | 诱导树在取诱导子图时的遗传性 |
| `MaximalTree` | 最大诱导树上必有两个非割点；带叶扩张时 `treeNumber` 的下界 |
| `EndBlocks` | 最长路端点的删点连通性、叶顶点邻居的唯一性（`unique_leaf_neighbor`）等端块结构事实 |
| `RootedChung` | 有根 Chung 型引理（`rooted_chung`）：以任意顶点为根的弦控走路张成诱导树 |
| `RadiusCriticalStructure` | 半径临界图的结构：度一邻点存在性 |
| `CaseA` | 主定理 `vrd_cut_tree_bound`：所有非割点删点均降半径且图有割点的情形 |
| `CaseB` | `drop_except` 系列：唯一例外删点情形下全部中心都是唯一离心点、张出有根诱导树 |
| `LeafCore` | 非叶集诱导核心的半径恰好降一 |
| `LeafDeletion` | 删叶后中心/唯一离心点结构的提升 |
| `LeafLemma` | `leafLemma`：有叶图的 `2r ≤ t·δ`，按顶点数强归纳（Case A/B 分别引用上述两模块） |
| `GraphConjecture84` | 无叶时最小度 ≥ 2，走测地线界 `two_radius_le_treeNumber_mul_minDegree`；汇总得最终定理 |

证明主线（详见[导读](docs/formal-proof-guide.md)）：

1. 按是否存在度为一的顶点分派：有叶走 `leafLemma`，无叶则 `δ ≥ 2`，
   测地线直接给出 `2r ≤ t`，放大不等式收尾；
2. 有叶情形按顶点数强归纳，关键 invariant 是删点后半径恰降一
   （"唯一离心点"刻画）；
3. Case A 用最大诱导树的两个非割点直接剥叶递推；
4. Case B 用有根 Chung 引理从唯一例外删点张出足够大的诱导树；
5. 完整的冠（corona）结构分类不需要——这是比早期手稿更短的路线。

## 文档

- [最终形式化证明导读（中文）](docs/formal-proof-guide.md) — 证明主线逐段讲解
- [Case A 的直接剥叶归纳](docs/case-a-induction.md)
- [Lean/Mathlib API 踩坑笔记](docs/lean-api-notes.md) — 全部对应真实 CI 失败
- [最终定理源码](Graffiti84/GraphConjecture84.lean) · [叶子引理源码](Graffiti84/LeafLemma.lean)
- `paper/graffiti84.tex`（附 PDF）— 自含的手写数学证明

`docs/full-proof.md` 与 `docs/conjecture-logic.md` 保留早期结构分类路线，
仅供历史参考，与最终 Lean 证明不是逐行对应；以 Lean 源码与 CI 结果为准。

## 目录

```text
Graffiti84/   13 个 Lean 模块与汇总入口 Graffiti84.lean
docs/         证明导读与路线文档
paper/        手写证明（LaTeX/PDF）
scripts/      CI 审计脚本（sorry/admit/axiom 扫描与 #print axioms）
```
