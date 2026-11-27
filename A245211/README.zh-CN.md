# OEIS A245211：R2.H2 的 Lean 证明

## 精确结论

令

$$
a(n)=\sum_{d\mid n,\ d<n} d\,\tau(d),
$$

其中 $\tau(d)$ 是正因子的个数。本项目证明：若 $n$ 平方自由，其不同素因子的数量 $r$ 满足 $3\le r<65$、$r$ 为奇数且不是素数的正整数次幂，则 $a(n)\ne n$。

这正是 [Left to Solve 的 OeisA245211.conjecture.R2.H2](https://lefttosolve.com/p/OeisA245211.conjecture.R2.H2)。可能的 $r$ 只有

$$
15,21,33,35,39,45,51,55,57,63.
$$

整数 $n$ 的大小没有上界。有限检查覆盖的是数学归约后的一组因子位置；这份证明不包含原猜想的其余分支。

## 证明结构

上游 R2 的公开引理给出固定点的乘积恒等式，以及每个素因子的下界。对素因子之间的整除关系建立映射，证明任何非空闭合子集都必须是全集，便得到一个包含全部素因子的循环。适当编号后，存在整数乘子 $d_i$，使得

$$
2p_{i+1}+1=d_i p_i,\qquad
\prod_{i=0}^{r-1}d_i=2^r+1,
$$

下标按 $r$ 循环，每个 $p_i$ 都是大于 $2^{r-1}$ 的素数。

把 $2^r+1$ 的素因子按重数列出，每个因子分配到某个 $d_i$，再旋转循环，让指定的一个因子位于位置 0。重复的素因子分别编号，并证明交换它们不改变检验结果。由此可以只计算等价位置排列中的一个代表。

定义整数递推

$$
c_0=0,\qquad c_{j+1}=d_jc_j+2^j.
$$

循环方程给出

$$
2^k p_k+c_k=\left(\prod_{j<k}d_j\right)p_0.
$$

取 $k=r$，由闭合条件和乘积恒等式得到 $c_r=p_0$。因此，对任意选定的奇数模数，因子的位置已经确定了起点和全部后续素数的剩余类。真实素数必须与这些小模数互素；每种可能的位置安排都在某一步违反该条件。

## 有限证书

| 素因子数量 | 使用的模数 |
|---|---|
| 15 | 33 |
| 21 | 3 |
| 33 | 33 |
| 35 | 5、3、7、11、13 |
| 39 | 3 |
| 45 | 3、5、7、13、19 |
| 51 | 3、7、5、11、13 |
| 55 | 5、11、3、13、17 |
| 57 | 3 |
| 63 | 3 |

在较大的四种情形中，先用一个模数证明位置分类，再对留下的位置组合使用后续模数。模 3 的零乘子锚点和模 5 的闭合路径枚举可以提前排除不可能的安排；两种提前检查都有独立的正确性证明。交换相同素因子之后，r=45、51、55 的 13、3、19 类分别只需检查 4、2、10 个代表，其余情况由列表置换引理直接推出。与当前模数同余于 1 的因子可以删除，这一步有单独的等式证明。

有限分类和排除均使用 `decide +kernel`。Python 搜索仅用于发现和组织证书，不是 Lean 证明的假设。

386 个闭合计算证书使用值为命题证明的 `def` 声明，类型和 `decide +kernel` 证明体均保持完整。这让 Lean 同步处理这些较大的计算，减少待处理定理的上下文累积；最终结论仍为 `theorem OMA.solution`。Lean 的 `defProp` 样式警告予以保留，未使用警告屏蔽属性或放宽提交规则。

模 3 的锚点从因子位置的短列表计算最小值；Lean 证明了它与逐个扫描全部循环位置得到的锚点完全相同。因此这项计算优化同时保留检验结果、置换不变性和中性因子删除引理。

最终连接先证明投影后的因子列表与证书使用的显式列表相等，再在模检验结论中改写这个列表。列表过滤由 `norm_num` 检查；这一写法使通用简化器不会展开带有未知位置的整个循环检验。原有的十个命题及有限证书均保持不变。

## 文件

- [`submission/OeisA245211.conjecture.R2.H2.lean`](submission/OeisA245211.conjecture.R2.H2.lean)：供上游直接检查的完整单文件证明。
- `Core.lean`：计算定义。
- `Cycle.lean`：单循环结构。
- `TokenAllocation.lean`：因子分配与循环旋转。
- `Checker.lean`：模检验的正确性证明。
- `Projection.lean`：因子列表、乘子与模检验的衔接。
- `Finite.lean`：全部有限分类与排除证书。
- `Main.lean`：十种情形和精确的 `OMA.solution`。
- `assemble.py`：生成上游要求的单文件提交。
- `position_certificates.py` 和 `position_certificates.json`：独立整数计算和生成证书所用的位置表。
- `generate_finite_lean.py`、`generate_main_lean.py`：重建有限证书与最终定理模块；`search_moduli.py` 提供素因子表和探索程序。

## 版本与验证

固定使用 Formal Conjectures 提交 `9097e2f90e66d2f6244209cb1c07f7120d17ec53`、Lean 4.33.1，以及 open-math-agents 提交 `d4827fcc0af9b8327e56e1eb335394e1cf6514c6` 中已接受的 R2 归约。

完整单文件证明已通过 [GitHub Actions 运行 46064959548](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/runs/46064959548)。原版上游检查器于 2026-11-28 04:52（北京时间）返回 `accepted`；`OMA.solution` 的公理审计结果为 `[propext, Classical.choice, Quot.sound]`。

检查对应源提交 `b8dd8c8e5f726ab70812fadb20c39289b2e79444`，单文件 SHA-256 为 `8bc73d1427b8c9c4457f0f92dab919a392f46a0ebd9354261cca2656dbf1e015`。可查看 [验证清单](verification/verification.json) 和 [检查器原始判定](verification/github-h2-verdict.json)。这里的 `accepted` 是检查器判定；本独立实现未向已关闭的 H2 任务重复发起上游 PR。

在此基础上，另有 [恰好 65 个不同素因子的证明](count65/README.zh-CN.md)。它越过了本目录 H2 的 `r < 65` 范围；新归约和对应 H1 证明也已分别通过原版检查器。

完整复现步骤写在仓库的 [A245211 验证工作流](../.github/workflows/a245211.yml) 中：准备固定版本的 Formal Conjectures 和已接受归约，从各模块源文件组装完整单文件，运行原版上游 `tools/check.sh` 的提交检查与公理审计。工作流保留原有的 30 分钟编译期限、全部证明检查，以及 `OMA.solution` 的公理白名单。该工作流可从 GitHub Actions 手动运行。

在仓库根目录重建提交文件：

```bash
python3 A245211/assemble.py --output A245211/submission/OeisA245211.conjecture.R2.H2.lean
```

Python 数据不是 Lean 编译的输入。重建发现过程时，可依次运行 `position_certificates.py`、`generate_finite_lean.py`、`generate_main_lean.py`；重建后仍需重新运行 Lean 检查。

## 已有工作

循环论证的数学思路也见于上游 [R2.H1 的 PR #7273](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7273)。本实现及分阶段的位置证书独立编写。

本实现组装后，任务台返回了 MakisChristou 更早的完成记录，指向 [提交 71b87a97](https://github.com/MakisChristou/open-math-agents/commit/71b87a97ceaf05143fdf1e376e878143e0bd3c65)。该工作已通过上游 [PR #9600](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9600) 合并。本项目保留独立实现及其复现材料，不主张首次解决该分支，也不重复提交已关闭任务。
