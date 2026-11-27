# OEIS A245211：R2.H2 的 Lean 证明

## 精确结论

令

\[
a(n)=\sum_{d\mid n,\ d<n} d\,\tau(d),
\]

其中 \(\tau(d)\) 是正因子的个数。本项目证明：若 \(n\) 平方自由，其不同素因子的数量 \(r\) 满足 \(3\le r<65\)、\(r\) 为奇数且不是素数的正整数次幂，则 \(a(n)\ne n\)。

这正是 [Left to Solve 的 OeisA245211.conjecture.R2.H2](https://lefttosolve.com/p/OeisA245211.conjecture.R2.H2)。可能的 \(r\) 只有

\[
15,21,33,35,39,45,51,55,57,63.
\]

整数 \(n\) 的大小没有上界。有限检查覆盖的是数学归约后的一组因子位置；这份证明不包含原猜想的其余分支。

## 证明结构

上游 R2 的公开引理给出固定点的乘积恒等式，以及每个素因子的下界。对素因子之间的整除关系建立映射，证明任何非空闭合子集都必须是全集，便得到一个包含全部素因子的循环。适当编号后，存在整数乘子 \(d_i\)，使得

\[
2p_{i+1}+1=d_i p_i,\qquad
\prod_{i=0}^{r-1}d_i=2^r+1,
\]

下标按 \(r\) 循环，每个 \(p_i\) 都是大于 \(2^{r-1}\) 的素数。

把 \(2^r+1\) 的素因子按重数列出，每个因子分配到某个 \(d_i\)，再旋转循环，让指定的一个因子位于位置 0。重复的素因子分别编号，并证明交换它们不改变检验结果。由此可以只计算等价位置排列中的一个代表。

定义整数递推

\[
c_0=0,\qquad c_{j+1}=d_jc_j+2^j.
\]

循环方程给出

\[
2^k p_k+c_k=\left(\prod_{j<k}d_j\right)p_0.
\]

取 \(k=r\)，由闭合条件和乘积恒等式得到 \(c_r=p_0\)。因此，对任意选定的奇数模数，因子的位置已经确定了起点和全部后续素数的剩余类。真实素数必须与这些小模数互素；每种可能的位置安排都在某一步违反该条件。

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

最终内核检查结果待补入。

完整复现步骤写在仓库的 [A245211 验证工作流](../.github/workflows/a245211.yml) 中：准备固定版本的 Formal Conjectures 和已接受归约，编译全部模块，再从源文件重新生成单文件，运行上游原版 `tools/check.sh`，检查 `OMA.solution` 的公理依赖。该工作流可从 GitHub Actions 手动运行。

在仓库根目录重建提交文件：

```bash
python3 A245211/assemble.py --output A245211/submission/OeisA245211.conjecture.R2.H2.lean
```

Python 数据不是 Lean 编译的输入。重建发现过程时，可依次运行 `position_certificates.py`、`generate_finite_lean.py`、`generate_main_lean.py`；重建后仍需重新运行 Lean 检查。

## 已有工作

循环论证的数学思路也见于上游 [R2.H1 的 PR #7273](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7273)。本实现及分阶段的位置证书独立编写。

本实现组装后，任务台返回了 MakisChristou 更早的完成记录，指向 [提交 71b87a97](https://github.com/MakisChristou/open-math-agents/commit/71b87a97ceaf05143fdf1e376e878143e0bd3c65)，当时尚待创建上游 PR。本项目不主张先于该工作完成。
