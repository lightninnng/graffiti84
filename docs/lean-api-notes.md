# Lean/Mathlib v4.32.2 API 行为笔记

本文件记录 Graffiti84 形式化过程中踩过的坑与验证过的 API 形态。
每一条都对应真实的 CI 失败,写新证明前先过一遍。

## 1. 命名空间异象

- `Diam.lean` 的 `eccent` 系列引理(`eccent_pos_iff`、`eccent_ne_zero`、
  `exists_edist_eq_eccent_of_finite`、`edist_ne_top_iff_reachable` 等)
  **实际公开在根命名空间**。写 `G.引理名`(点标记)可以解析(有根级回退),
  写 `SimpleGraph.引理名` 反而 Unknown constant。
  验证手段:`#check @SimpleGraph.eccent_pos_iff` 输出 `@eccent_pos_iff`。
- `SimpleGraph.Adj.toWalk (h : G.Adj u v) : G.Walk u v`,方向与 h 一致,
  换方向要 `h.symm`。
- `edist_pos_of_ne (hne : u ≠ v) : 0 < G.edist u v` 是**有方向的**:
  需要哪个方向的距离就给哪个方向的不等。

## 2. ENat(ℕ∞)上的禁用武器

- `omega`、`linarith` **不适用**(无群结构)。线性步进用:
  `add_le_add`(`a≤c → b≤d → a+b≤c+d`,逐分量配对)、
  `le_self_add`、`add_le_add`/`le_refl` 组合。
- **⚠️ 本版 `add_le_add_left/right` 语义与命名直觉相反**:
  - `add_le_add_left h c : a + c ≤ b + c`(c 加在右)
  - `add_le_add_right h c : c + a ≤ c + b`(c 加在左)
  目标是 `k + _` 形状时用 RIGHT,`_ + k` 形状时用 LEFT。
  且两者在 h 含省缺参 meta 时会 elaboration 失败——先把 h 落成 `have`。
- `ENat.toNat_pos (hn0 : n ≠ 0) (hxt : n ≠ ⊤) : 0 < n.toNat`;
  `ENat.coe_toNat (h : n ≠ ⊤) : (n.toNat : ℕ∞) = n`;
  `ENat.toNat_eq_zero`;`bot_le` 收尾零下界。
- 强制转换余项:`push_cast` / `rw [← hcoe]` + `simp`;
  `rw [hcoe]` 匹配不到 `↑(toNat + 1)` 内部。
- `norm_num` 在 ℕ∞ 上基本可用(数值字面量)。

## 3. 已消失/更名的常量(v4.32.2)

| 旧名 | 替代 |
|---|---|
| `Finset.eq_singleton_of_unique_mem` | `Finset.eq_singleton_iff_unique_mem.2 ⟨mem, fun b hb => …⟩` |
| `Finset.exists_ne_map_eq_of_card_lt_of_mem` | card_eq_one + 手工(见 adj_eq_of_degree_eq_one) |
| `Finset.two_le_card` | `Finset.card_le_one` 反证(card ≤ 1 → 成员相等) |
| `Nonempty.of_finset` | `obtain ⟨c, hc⟩ := hS; haveI : Nonempty α := ⟨c⟩` |
| `SimpleGraph.IsShortest` | 不存在,自定义 geodesic 谓词 |

存在且可靠:`Finset.card_le_one`、`Finset.card_eq_one`、
`Finset.eq_singleton_iff_unique_mem`、`Finset.mem_erase.mp/mpr`、
`Finset.card_insert_of_notMem`、`Finite.exists_min/exists_max`
(**极小性不含归属**——要么在子类型上取,要么补 `m ∈ S`)、
`SimpleGraph.degree_pos_iff_exists_adj`、`SimpleGraph.edist_le`、
`SimpleGraph.radius_le_eccent`、`SimpleGraph.edist_le_eccent`。

## 4. 实例与作用域

- **`open Classical` 必须有**:`G.degree` 展开涉及
  `Fintype ↑(G.neighborSet z)` 的可判定成员实例;没有 Classical 时
  `simpa using hdeg` 这类推理全部报 `failed to synthesize Fintype ↑(…)`,
  而同样的代码在带 Classical 的文件里是绿的。
- Walk 成员/邻接互转:`Finset.mem_neighborFinset` 两个前缀都不存在,
  用 `by simpa using (h : G.Adj z a)`(Classical 开启后可靠)。
- `cases w with | cons h w'` 只绑定两个显式参数;要拿中间顶点必须写
  **全名 @ 模式**:`| @cons _ x _ h w'`(**5 个位置**:3 索引 + 邻接 + 尾部;
  只写 3 个名字会绑到索引上)。
- 对 cases 产生的不可达变量,`subst` 的消元方向不可控
  (可能消掉想保留的命名变量)——后续引用要跟着换名,或改用
  `rw [hxp] at h` 式的假设改写。
- `push_neg` 已弃用(警告不失败);本版里它对 ℕ∞ 的 `¬(0 < x)`
  不化简成 `x ≤ 0`——用 `not_lt.mp` + `le_antisymm … zero_le` 替代。

## 5. 省缺参数推断(metavariable)坑

- `iSup₂_le h` 可靠;`le_iSup₂_of_mem` 不可靠时用
  `le_iSup₂ (f := fun i (_ : i ∈ S) => …) x hx` 显式给 f。
- `iInf₂_le a ha : ⨅ i ∈ s, f i ≤ f a` 可靠(成员形式);
  `le_iInf₂ fun i hi => …` 可靠。
- `le_iSup`/`iInf₂_le` 在目标是 def(如 `eccent`/`radOn`)包着的 iSup/iInf
  时 f 推不出——先 `rw [SimpleGraph.eccent]` 展开,或显式
  `(f := …)`。
- 复合引理(如 `add_le_add_right (foo x) 1`)整体 elaboration 先于
  expected-type 统一 → meta 残留。**纪律:先 `have hX : <具体类型> := foo x`,
  再使用 hX。**

## 6. 策略层面

- `subst h : a = b` 消元方向:Lean 优先消掉**右侧**自由变量;
  消完之后所有引用要跟着改。分支里要引用的变量被消掉时,
  改 `rw [h] at <hyps>`。
- calc 步骤里对 `have hw := cons …` 这种**绑定变量**做
  `rw [Walk.length_cons]` 失败(非语法 cons)——把构造内联到每个步骤,
  或先 `simp only [hw]`。
- `Finite.exists_max/min (f := …)` 的 Nonempty 是**实例参数**
  (haveI 提供),不是显式参数。
- 极小/极大都需要归属时,在子类型 `{x // x ∈ S}` 上取
  (property 即归属)。

## 7. 工作流

本地只写代码 + `grep .lake/packages/mathlib/Mathlib` 查真实 API
(源码 115MB 保留,olean 缓存 6.3GB 不落本地);
推送触发 CI(`lake update → cache get → build → audit`),
`scripts/ci_log.py <run_id>` 拉取每个 step 的结论与错误行。
审计脚本 `scripts/audit.sh` 会剥注释后扫描 sorry/admit/axiom。
