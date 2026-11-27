# 六顶点图染色引理

[![Verify](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/workflows/verify.yml)

[English](README.md) · [完整初等证明](docs/proof.zh-CN.md) · [Lean 定理](SixVertex/Coloring.lean)

**对任意至多六个顶点的无三角形简单图，无论怎样把边染成红、蓝两色，都能给顶点染红、蓝两色，使红边不连接两个红点、蓝边不连接两个蓝点。**

这个项目提供一份简短的结构证明、一份独立编写的完整穷举程序，以及一个独立的 Lean 形式化项目。

## 证明的关键

这样的图最多删掉一条边就能成为二分图。如果它原本不是二分图，必然包含一个没有弦的五边形；圈外至多一个顶点，无三角形条件又限制了它的连边方式，因此可以直接分析全部结构。

给删边后的图按二分部正常染色。如果补回的那条边违反要求，就把所有顶点的红蓝颜色整体互换。那条边得到修复，其他边仍然连接异色顶点。详见[完整证明](docs/proof.zh-CN.md)。

## 验证结果与复现

独立 Python 程序枚举全部六顶点标号简单图：

| 类别 | 数量 |
|---|---:|
| 全部图 | 32,768 |
| 无三角形图 | 5,789 |
| 已经是二分图 | 5,177 |
| 恰需删一条边成为二分图 | 612 |
| 已核验的“图／边染色”组合 | 294,987 |
| 反例 | 0 |

Lean 使用内核归约验证有限图性质，再严格连接到 `SimpleGraph` 上的命题，并覆盖全部 `k ≤ 6` 的情况。Python 检查结果不作为 Lean 定理的公理或受信任输入。

GitHub Actions 会编译项目、用 `leanchecker` 回放项目模块，并检查最终定理的公理依赖，只允许 `propext`、`Classical.choice`、`Quot.sound`。上方徽章显示本仓库当前的实际验证状态。

安装 [elan](https://github.com/leanprover/elan) 后运行：

```bash
python3 scripts/check_exhaustive.py
lake update
lake exe cache get
lake build
lake env leanchecker SixVertex
lake env lean Check.lean
```

版本固定为 Lean **4.33.1** 和 Mathlib 提交 **0df444a360eaa60ab8c11dca51a86af692955474**。

## 来源与署名

命题对应 Left to Solve 中 Erdős #151 某个变体的 **R1.H2 子步骤**，拆分由 **dk8827** 提出，见 [PR #4050](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4050)。

准备发布时，我们核实 **Salofe 的 [PR #5331](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5331)** 已于 **2026 年 11 月 27 日北京时间 19:22:31** 被接受并合并。此前网页的“开放”状态存在滞后。该形式化同样使用有限图检查与整体换色；已有形式化的优先权属于该贡献者，本仓库不声称首次解决。

本项目为 **sunnyspot114514** 准备，由 **ChatGPT** 协助完成。

## 范围

这是一条明确、有限的图论引理及其可复现证明。**它不等于解决 Erdős #151，也不等于解决其 `cliqueFree_four` 变体或该拆分的其他假设。** 人类可读证明使用五边形结构；Lean 实现通过计算验证对应的有限图性质。
