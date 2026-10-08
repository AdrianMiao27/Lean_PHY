# 从模型权重到源导数、关联与受控响应

后续公共连接见[有限量子响应](quantum-response.md)：实际时间导数、有限时间扰动和非对易 Gibbs 导数已接入。本文客户端中较广的动力学／关联义务继续保留，一般驱动、频率表示和时间有序 Wick 目标尚未全部完成。

本批对应全局路线 T1/T2/T3/T5，以及能力 C04、C05、C08、C12、C13、C15、C19。公共操作连接了现有的有限 Gibbs 态、有限路径和、连通关联、上一批多项式作用量，以及 `ErrorCertificate`。这是有限系统的静态平衡／Euclidean 源响应；时间依赖的量子 Kubo、retarded/Matsubara 转换及热力学极限仍在建设路线中。

## 约定和研究操作

实源系综采用

\[
w_i(J)=\exp\!\left[-S_i+\sum_a J_a A_a(i)\right],\quad
Z(J)=\sum_i w_i(J),\quad p_i(J)=w_i(J)/Z(J).
\]

`S` 是无量纲实作用量，场构型与源标签都是可变的有限类型。非空构型空间保证所有实源下 `Z > 0`；源可以任意取值，不局限于零源或两能级模型。期望和协方差直接使用现有 `FiniteProbability`。

| 研究操作 | 公开定理 | 实际推出的结论 |
| --- | --- | --- |
| 任意源方向 `J + t v` 的 log Z 导数 | `SourceEnsemble.hasDerivAt_logPartition` | `d log Z / dt = ⟨Σ_a v_a A_a⟩`。 |
| 归一化期望的源响应 | `SourceEnsemble.hasDerivAt_expectation` | `d⟨O⟩/dt = Cov(O, Σ_a v_a A_a)`。 |
| 参数依赖观测量 | `SourceEnsemble.hasDerivAt_moving_expectation` | 保留 `⟨∂_t O⟩` 接触项。 |
| log Z 的二阶导数 | `SourceEnsemble.hasDerivAt_deriv_logPartition` | 实际一阶导函数的导数为方向插入的方差。 |
| 多源易感率 | `susceptibility_is_response`、`susceptibility_symm`、`susceptibility_nonneg` | 各矩阵元对应真实源导数，矩阵对称且二次型非负。 |
| 共轭观测量的单调性 | `conjugate_expectation_monotone` | 任意实源方向上，共轭期望单调不减。 |
| 有限源变化 | `expectation_source_error` | 一致幅度界产生两个有限源值之间的期望误差证书。 |

这些是 Lean/mathlib 的 `HasDerivAt` 定理，导数由实际有限权重推出。公共的 `FiniteWeighted.hasDerivAt_expectation_score` 也允许某些权重为零，只要求整个配分函数在求导点非零：

\[
 w_i'=w_i s_i\quad\Longrightarrow\quad
 \partial_t\langle O\rangle=\langle O'\rangle+
 \langle O s\rangle-\langle O\rangle\langle s\rangle.
\]

最后一项来自归一化。此接口不进行逐权重除法，也不把最终响应关系交由调用者直接提供。

## 能量源、温度和可变参数

对于 `exp(-β E)`，能量扰动 `E-hA` 对应无量纲源 `J=βh`。因此响应包含显式的 **β 因子**：

```lean
import LeanPhy.Entry.StatMech

open LeanPhy.StatMech

example {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (E A O : ι → ℝ) (h : ℝ) :
    HasDerivAt
      (fun s => (finiteGibbsProbability β (fun i => E i - s * A i)).expectation O)
      (β * (finiteGibbsProbability β (fun i => E i - h * A i)).covariance O A) h :=
  hasDerivAt_finiteGibbs_energySource β E A O h
```

`hasDerivAt_finiteGibbs_parameter` 允许能量和观测量同时随参数变化，推出
`∂⟨O⟩ = ⟨O'⟩ − β Cov(O,E')`。`hasDerivAt_finiteGibbs_beta` 推出
`∂_β⟨O⟩ = −Cov(O,E)`，因而平均能量对逆温度的导数非正。

`hasDerivAt_finiteGibbs_temperature` 在 `T ≠ 0`、`β=1/T`、`k_B=1` 的约定下，对固定能量函数给出热容 `Var(E)/T²`；该接口没有自动进行带量纲单位转换。磁易感率非负的结论显式要求 `β ≥ 0`。这些公式针对可交换的实构型能量，不能直接用于对非对易量子 Hamiltonian 的指数求导。

## 与量子热态、基底和时间演化的连接

[FiniteThermalState](../LeanPhy/Quantum/FiniteThermalState.lean) 接受任意非空有限标签空间。`diagonalDensity` 将已有非负归一化概率转换为有正性与迹一证明的 `FiniteDensity`；`diagonalDensity_trace_mul` 允许任意复矩阵探针，并证明期望只读取其对角元。对实对角探针，矩阵迹期望与连通关联分别等于原概率期望与协方差。

`thermalStateInBasis U β E` 在给定酉基底中构造热态，`thermalStateInBasis_eq_exp` 证明它等于 `Z⁻¹ • exp(-β U diag(E) U†)`。`thermalStateInBasis_partition` 证明这个 Z 正是矩阵指数的迹。态与探针同时换基时，迹期望保持；仅改变态通常会改变读数，回归中显式得到 0 与 1 的差别。

对于任意有限 Hermitian Hamiltonian，`finiteThermalState H hH β` 使用 mathlib 的实际谱定理构造状态，证明：

- `finiteThermalState_eq_exp`：状态矩阵等于 `Tr(exp(-βH))⁻¹ • exp(-βH)`。
- `finiteThermalState_partition_pos`：配分函数的实部严格为正，因而可以合法归一化。
- `finiteThermalState_conjugate`：热态构造在酉换基下协变；给定的对角化与谱构造一致。
- `finiteThermalState_stationary`：在已有 `exp(+itH)` 共轭演化下状态保持不变。
- `hasDerivAt_finiteThermalState_energy_beta` 与 `hasDerivAt_finiteThermalState_energy_temperature`：实际矩阵平均能量的逆温度导数和热容由能量方差给出。

这些结果不要求非简并谱或谱隙。谱基底由库定理选择，不是数值对角化算法；这里没有声称参数变化时选出的本征矢光滑。

```lean
import LeanPhy.Entry.Quantum

open LeanPhy.Quantum

example {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β t : ℝ) :
    (finiteHamiltonianFlow H hH t).conjugate (finiteThermalState H hH β).rho =
      (finiteThermalState H hH β).rho :=
  finiteThermalState_stationary H hH β t
```

`hasDerivAt_thermalStateInBasis_parameter` 将源响应接到矩阵迹读数，保留观测量导数；它的能量、扰动和探针位于**固定的共同基底**。任意 Hermitian 热态的构造已经实现，但非对易 Hamiltonian 扰动的导数仍未实现，不能将前者当作后者已证。固定 H 的温度变化没有这个移动本征基底问题。

## 复源与有限场论路径和

`FinitePathIntegral.sourceWeight` 使用 `w_i exp(z A_i)`。`withSource` 要求给出当前源点的 `sourcePartition ≠ 0`；`hasDerivAt_sourceExpectation` 则给出该点倾斜系综的连通关联。零源处重用原路径和的非零配分函数证明。

这是实际指数权重的复导数，不是旧的有限阶 `sourceGeneratingPolynomial`。两者继续分别使用，未将一个有限阶多项式宣称为完整生成泛函。复源接口不引入复对数分支，也没有隐含的 `i` 因子、时间排序或因果性。

回归中的基准权重 `(2,-1)` 具有非零配分函数，但经插入 `(0,1)` 在源 `Complex.log 2` 处配分函数为零；其零源连通自关联为 `-2`。因此：

- 基准模型可归一化，不意味着每个复源点可归一化。
- 非零配分函数不意味着权重非负，也不能直接使用概率方差／易感率非负定理。
- 原始 `sourceExpectation` 使用 Lean 的全定义除法；零点处的函数值不能解释为物理归一化期望。定理及 `withSource` 保留非零条件。

实源系综通过 `SourceEnsemble.fromRealAction_expectation` 和 `fromRealAction_connected` 与既有 `FinitePathIntegral.fromRealAction` 明确对应。归一化概率权重与未归一化指数权重不被误认成相同权重对象；一致的是期望与连通关联。

## 与作用量层及误差层的组合

`FirstOrderLagrangian.finiteAction` 在显式有限场值／梯度表上求值，并按给定单元系数组合成实作用量。`hasDerivAt_finiteAction_expectation` 证明对密度扰动 `L+hV`，

\[
\partial_h\langle O\rangle=-\operatorname{Cov}(O,S_V).
\]

`S_V` 是同一有限表上求值的扰动作用量，负号来自 `exp(-S)`。这一接口直接复用 [上一批作用量工具](variational.md)；没有自动证明输入梯度槽来自有限差分、单元系数逼近积分，或有限构型集合逼近连续场积分。

若对所有构型证明 `|O_i| ≤ M`、`|Σ_a v_a A_a(i)| ≤ N`，且 `M,N ≥ 0`，`expectation_source_error` 给出

\[
\operatorname{ErrorCertificate}\bigl(
\langle O\rangle_{J+s v},\langle O\rangle_{J+t v},
2MN|s-t|\bigr).
\]

这个界不追求最优常数；它通过实际响应的统一界与中值估计证明有限源变化的控制，不等于“线性项是精确有限变化”，也不提供未证明的 Taylor 余项。输入界必须覆盖整个构型集合，数值采样不能替代证明。

## 验收与使用

[SourceResponseResearch](../LeanPhy/Examples/SourceResponseResearch.lean) 检查任意有限边集与耦合的 Ising 响应、接触项、β 因子、作用量接口、复源零点及有限源预算，以及量子热态、热平衡不变性、矩阵期望的 β 因子与基底变换。研究报告登记十项实际定理，并保留热力学极限与动力学响应两项开放义务：

```bash
lake exe leanphy_source_client --project-json
# 按预期失败：极限和动力学义务仍然开放
lake exe leanphy_source_client --strict
lake exe leanphy_index --query 'Gibbs energySource' --kind theorem
lake exe leanphy_index --query 'source error' --kind theorem
lake exe leanphy_index --query 'finiteThermalState' --kind theorem
```

本批没有完成非对易 Gibbs/Duhamel 导数、实时间 retarded 响应、Green 函数频率表示、一般 Wick 与真实态的连接、连续路径测度或热力学临界极限。这些边界记录在 [能力盘点](capabilities.md) 与 [全局路线](roadmap.md)，不会因有限源导数已证而自动关闭。
