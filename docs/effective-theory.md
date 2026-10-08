# 逐阶运算、消元与有效读数

本指南对应[全局能力清单](capabilities.md)的 C06、C14、C18、C19，以及[路线](roadmap.md)的 T2、T4、T5。它是全局建设的一部分：源／热态、动力学关联、多体构造、证据核验和探索工作流仍各有独立的建设任务。

公共操作按形式展开、消元、重场作用量和误差传播分层。`Examples/EffectiveResearch` 和独立 `Clients/EffectiveClientMain.lean` 消费公共操作；数值小回归只用于检查次序、源符号与归一化，公共输入不固定为这些数值或维度。

| 输入与研究操作 | 公共模块／关键结果 | 输出及条件 |
| --- | --- | --- |
| 非交换系数的单参数形式级数 | [FormalExpansion](../LeanPhy/Mathematics/FormalExpansion.lean)：`Below.mul`、`Below.inverse`、`truncate_inverse`、`conjugate_mul` | 乘法、逆及相似变换保持所保留系数；逆的常数项必须是已证明的单位 |
| 算符级数与矩阵级数互接 | [FormalMatrix](../LeanPhy/Mathematics/FormalMatrix.lean)：`matrixHom`、`matrixUnit` | 从矩阵常数项的单位及形式逆，构造条目为级数的可逆矩阵 |
| 分块线性方程、源和线性探针 | [BlockElimination](../LeanPhy/Mathematics/BlockElimination.lean)：`System.satisfies_iff`、`readout_of_solution` | 全方程与有效方程等价，重分量可重构；源与探针一同转换 |
| 截断输入后的消元 | [FormalBlockElimination](../LeanPhy/Mathematics/FormalBlockElimination.lean)：`effective_below`、`effectiveSource_below`、`effectiveReadout_below` | 任意保留阶数的有效算符、源和读数系数一致；不推断级数求值或收敛 |
| 有限量子块的本征方程及二次探针 | [EffectiveHamiltonian](../LeanPhy/Quantum/EffectiveHamiltonian.lean)：`Model.eigen_equation_iff`、`quadratic_readout`、`norm_readout` | 能量依赖有效 Hamiltonian、重构映射、有效探针及归一化度规 |
| 一个代数辅助重场和任意轻场多项式 | [HeavyFieldElimination](../LeanPhy/FieldTheory/HeavyFieldElimination.lean)：`action_eliminated`、`eval_eliminate`、`eulerLagrange_effective` | 实际求解重场方程，替换作用量与插入，接到现有局部变分操作 |
| 混合质量矩阵与导数耦合 | [PropagatingHeavy](../LeanPhy/FieldTheory/PropagatingHeavy.lean)：`inverseApprox`、`equation_reconstruct_order`、`kinetic` | 构造任意有限截断，逐项保留不交换次序和可计算方程残差 |
| 二次传播重场匹配 | [HeavyFieldMatching](../LeanPhy/FieldTheory/HeavyFieldMatching.lean)：`jetModel`、`density_perturb`、`density_matching` | 从密度导出重场方程；保留截断残差、散度、源接触项与重场读数 |
| 实际重场区间作用量 | [HeavyFieldInterval](../LeanPhy/FieldTheory/HeavyFieldInterval.lean)：`evaluate_residual`、`action_matching`、`action_error` | 实际光滑剖面、第一变分及积分匹配；端点通量和一致残差预算显式 |
| 实际近似逆及其残差 | [EliminationError](../LeanPhy/Mathematics/EliminationError.lean)：`inverse_error`、`effective_error` | 在次乘性范数下产生 `ErrorCertificate`；仍需提供真实逆或其一致界 |

新增的[复矩阵证书链](matrix-certificates.md) 为下述精确分块和逆误差接口提供实际输入：由有理复矩阵残差构造精确逆及其界，并同时认证有效源、重构、线性探针与有限能量圆盘。原接口仍可接受其它来源的逆证明；有理指数／Gibbs 包络另已接入；不确定实输入、能量无关酉约化与传播重场的 Green 函数／一致误差仍待补齐。二次传播重场的有限阶操作见下文。

## 1. 形式阶数的含义

`Below N f g` 表示所有 `k < N` 的系数相等。`N` 是**不包含的上界**；例如 `Below 2` 保留常数与一次项。零阶截断不保留任何系数，因此 `truncate_inverse` 要求 `0 < N` 以保留可逆常数项。

系数只要求 `Ring`，不要求交换。若 `D₀ = u` 是一个单位，逆级数前两项为

```text
(D⁻¹)₁ = −u⁻¹ D₁ u⁻¹
(D⁻¹)₂ = u⁻¹ D₁ u⁻¹ D₁ u⁻¹ − u⁻¹ D₂ u⁻¹
```

每个因子的顺序都属于结论。`conjugate` 是可逆相似变换；它不自动证明酉性。一个保留阶数的结论也不自动成为有限参数处的范数余项界。

## 2. 分块方程同时变换源和观测量

对于 `A x + B y = jL`、`C x + D y = jH`，输入的 `D` 必须携带真实双边逆。公共操作给出

```text
Aeff = A − B D⁻¹ C
jeff = jL − B D⁻¹ jH
y    = D⁻¹ (jH − C x)
```

轻／重空间可具有不同维度。线性探针 `OL x + OH y` 变为

```text
(OL − OH D⁻¹ C) x + OH D⁻¹ jH
```

最后的源偏移不能省略。下面直接使用任意有限空间，而不是某个内置 Hamiltonian：

```lean
import LeanPhy.Mathematics.BlockElimination

open LeanPhy.Mathematics.BlockElimination

example {L H : Type*} [Fintype L] [Fintype H] [DecidableEq H]
    (S : System ℂ L H) (x : L → ℂ) (y : H → ℂ)
    (jL : L → ℂ) (jH : H → ℂ) :
    S.fullMatrix.mulVec (Sum.elim x y) = Sum.elim jL jH ↔
      S.effective.mulVec x = S.effectiveSource jL jH ∧
        y = S.reconstruct x jH := by
  rw [S.fullMatrix_equation_iff, S.satisfies_iff]
```

量子接口将重块设为实际 `D − z I`。所得 `Heff(z)` 一般依赖能量，不是已经构造好的能量无关 Schrieffer–Wolff Hamiltonian。重构矩阵 `F` 给出 `Oeff = F† O F` 和 `G = F† F`；归一化期望的分母必须使用重构范数。已证明的 `normMetric_eq` 保留重分量贡献，不能直接把 `G` 换为恒等矩阵。

`eigen_equation_iff` 包括零向量的方程等价；`lifted_ne_zero_iff` 另行处理非零态。一般复能量的代数消元不保证 Hermitian；`effectiveHamiltonian_isHermitian` 明确要求轻块、交叉伴随及重 resolvent 的 Hermitian 条件。

## 3. 辅助重场作用量及插入

作用量为 `V(φ) + m χ²/2 + χ J(φ)`，其中 `V`、`J` 是任意轻场多项式，`m` 是二次项系数。若 `m ≠ 0`，重场方程给出 `χ = −J/m`，诱导作用量为 `V − J²/(2m)`。同一个代数同态作用于任意插入，不只作用于作用量。

```lean
import LeanPhy.FieldTheory.HeavyFieldElimination

open LeanPhy.FieldTheory.HeavyFieldElimination

example {Field : Type*} (m : ℝ) (hm : m ≠ 0)
    (V J : MvPolynomial Field ℝ) :
    eliminate m J (action m V J) = effective m V J :=
  action_eliminated m hm V J
```

`effective_source_shift` 保留 `J → J + h Q` 所产生的一次与二次源项。`effective_derivative` 和 `eulerLagrange_effective` 把诱导相互作用的轻场导数交给已有变分层。

该接口处理代数辅助场。下节扩展二次传播重场的动能与有限阶展开；一般场重定义／EOM 冗余、Gaussian 测度／行列式和圈贡献仍需独立建设。

## 4. 混合传播重场的有限阶匹配

`PropagatingHeavy.jetModel` 接受任意重场标签 `H`、轻场标签 `Field`、方向 `Direction`、对称可逆实矩阵 `M` 和对称导数张量 `Zᵢⱼᵐᵘⁿᵘ = Zⱼᵢⁿᵘᵐᵘ`。`M` 是作用量二次项的系数矩阵；物理模型采用质量平方时，调用者应输入质量平方矩阵。`Z` 和源 `J` 可以是任意轻场／背景的多项式 jet。重场变化时它们保持固定。

采用显式约定

\[
\mathcal L=V+\tfrac12\chi^T M\chi+
 \tfrac\epsilon2\sum_{ij\mu\nu}Z_{ij}^{\mu\nu}(\partial_\mu\chi_i)(\partial_\nu\chi_j)
 +\chi^T J,\qquad
 (L\chi)_i=\sum_{j\mu\nu}\partial_\mu(Z_{ij}^{\mu\nu}\partial_\nu\chi_j).
\]

由重场第一变分得到 `Dχ + J`，其中 `D = M − εL`。`ε` 是显式展开参数，可以取 `1`；没有隐含的时空 signature 或正定性假设。`Z` 随背景变化时，`kinetic` 会实际求导 `Z`，不能把它移到导数之外。

保留 `N` 项的操作为

\[
K_N=\sum_{k=0}^{N-1}\epsilon^k(M^{-1}L)^kM^{-1},\qquad
\chi_N=-K_NJ,\qquad
R_N=D\chi_N+J=\epsilon^N M(M^{-1}L)^N M^{-1}J.
\]

`N` 是不包含的上界：`N=0` 给出零重建场，`N=1` 是代数首项，`N=2` 再保留一次动能插入。质量混合与导数耦合无需交换；右端的质量逆和整体符号属于结论。这里的阶数计数动能插入，不能在含高阶背景 jet 时直接解释成统一的时空导数阶数。

```lean
import LeanPhy.Entry.HighEnergy

open LeanPhy.FieldTheory LeanPhy.FieldTheory.PropagatingHeavy

noncomputable def heavySector {Field H Direction : Type}
    [Fintype H] [DecidableEq H]
    (M : (Matrix H H ℝ)ˣ)
    (hM : ∀ i j, (M : Matrix H H ℝ) i j = (M : Matrix H H ℝ) j i)
    (Z : H → H → Direction → Direction → JetPolynomial ℝ Field Direction)
    (hZ : ∀ i j μ ν, Z i j μ ν = Z j i ν μ) := jetModel M hM Z hZ

example {R H Direction : Type} [CommRing R] [Algebra ℝ R]
    [Fintype H] [DecidableEq H] [Fintype Direction]
    (M : Model R H Direction) (ε : ℝ) (N : ℕ) (J : H → R) :
    M.residual ε J (M.field ε N J) =
      ε ^ N • (((M.massOperator : Module.End ℝ (H → R)) *
        ((↑(M.massOperator⁻¹) : Module.End ℝ (H → R)) * M.kineticOperator) ^ N *
          ↑(M.massOperator⁻¹)) J) := M.residual_field ε N J
```

匹配密度定义为 `V + χ_NᵀJ/2 = V − JᵀK_NJ/2`。公共操作证明的是带显式余项的精确关系：

\[
\mathcal L[\chi_N]=\mathcal L_{\mathrm{eff},N}
 +\tfrac12\chi_N^T R_N
 +\tfrac\epsilon2\sum_\mu\partial_\mu B^\mu,
\qquad B^\mu=\sum_{ij\nu}\chi_{N,i}Z_{ij}^{\mu\nu}\partial_\nu\chi_{N,j}.
\]

`density_perturb` 另外证明重场变化的线性项是 `ηᵀ(Dχ+J) + ε div B(η,χ)`，从而把方程与作用量绑定。`effective_source_shift` 对 `J+sQ` 保留两项混合源和二次源接触项；导数核的两项混合乘积在局部密度上不应擅自合并。`readout` 将 `O+Qᵀχ` 接到同一个重建场，`readout_source_shift` 跟踪源变化。

```lean
import LeanPhy.FieldTheory.HeavyFieldMatching

open LeanPhy.FieldTheory.PropagatingHeavy

example {R H D : Type} [CommRing R] [Algebra ℝ R]
    [Fintype H] [DecidableEq H] [Fintype D]
    (M : Model R H D) (ε s : ℝ) (N : ℕ) (V : R) (J Q : H → R) :
    M.effective ε N V (J + s • Q) = M.effective ε N V J +
      (s / 2) • (pair (M.field ε N J) Q + pair (M.field ε N Q) J) +
      (s ^ 2 / 2) • pair (M.field ε N Q) Q :=
  M.effective_source_shift ε s N V J Q
```

## 5. 实际作用量、端点和可认证的差异

一维剖面接口使用 `CurveJet.evaluate`，把所有 jet 解释为**同一组实际光滑函数的迭代导数**。`evaluate_density` 和 `evaluate_residual` 分别把形式密度和方程连接到实际动能与 `d(Z dχ)/dt`。`action_matching` 积分上式，保留 `ε[B(b)−B(a)]/2`；`hasDerivAt_action` 是实际作用量的参数导数，`stationary_of_equation` 还要求实际方程及匹配的端点通量。

```lean
import LeanPhy.FieldTheory.HeavyFieldInterval

open LeanPhy.FieldTheory LeanPhy.FieldTheory.PropagatingHeavy
open scoped ContDiff

example {Field H : Type} [Fintype H] [DecidableEq H]
    (φ : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (M : Model (JetPolynomial ℝ Field Unit) H Unit)
    (hδ : M.derivative () = JetPolynomial.totalDerivative ())
    (ε a b : ℝ) (V : JetPolynomial ℝ Field Unit)
    (J χ η : H → JetPolynomial ℝ Field Unit) :
    HasDerivAt (fun s : ℝ => Interval.action φ hφ M ε a b V J (χ + s • η))
      (Interval.integral φ hφ a b (pair η (M.residual ε J χ)) +
        ε * (CurveJet.evaluate φ b (M.flux η χ ()) -
          CurveJet.evaluate φ a (M.flux η χ ()))) 0 :=
  Interval.hasDerivAt_action φ hφ M hδ ε a b V J χ η
```

由 `jetModel` 构造的模型自动以 `rfl` 满足 `hδ`。`action_error` 接受整个区间上的 `|χ_NᵀR_N| ≤ ρ` 证书和端点差 `|B(b)−B(a)| ≤ β`，给出实际已替换作用量与匹配作用量之间的预算

```text
(ρ · |b−a| + |ε| · β) / 2
```

单个采样点不满足一致残差前提。即使方程残差为零，端点也不能自动丢弃：回归取 `M=Z=ε=1`、`J(t)=t`、`N=1`、区间 `[0,1]`，得到 `χ=-t`、残差 `0`，原作用量 `1/3`、匹配作用量 `−1/6`，差 `1/2` 恰为端点项。这个差异已由实际积分核验。

本批支持任意有限重场混合、轻场多项式 jet 和形式方向；实际区域解释目前是一维区间。尚未构造指定边界条件下的 Green 函数、证明到精确重场解的距离或随 `N` 收敛，也未提供非二次重场求解、统一 EFT 算符基／EOM 商、多维边界积分或圈行列式。`action_error` 的目标是**已替换作用量**，不能改称尚未构造的精确低能理论误差。

## 6. 解析逆误差是独立证明

在范数环中，对真实单位 `D` 和候选近似逆 `K`，证明使用实际残差：

```text
‖D⁻¹ − K‖ ≤ ‖D⁻¹‖ ‖1 − D K‖
‖(A − B D⁻¹ C) − (A − B K C)‖ ≤ ‖B‖ ‖D⁻¹‖ ‖1 − D K‖ ‖C‖
```

这一误差接口的 `A,B,C,D,K` 属于同一个范数环；它没有自动给出任意矩形分块之间的全部算符范数适配。矩阵使用时须选择满足次乘性的范数，例如算子范数。

有限几何逆 `K_N = Σ(k < N) X^k` 的残差严格等于 `X^N`。`geometric_inverse_error` 在 `D = 1 − X`、真实逆及 `NormOneClass` 条件下给出 `‖D⁻¹‖ ‖X‖^N`。有限阶估计本身不要求 `‖X‖ < 1`；要由此证明随阶数衰减，还必须提供该小量条件和适当的一致逆界。

## 7. 验证入口与下一步

```bash
lake build leanphy_effective_client
lake exe leanphy_effective_client --project-json
```

客户端报告 14 条带证明结论和 3 条开放义务：低能适用域、Green 函数与量子匹配、能量无关酉动态约化。`--strict` 应因开放义务而失败。客户端通过 `CLI.Core` 导入，不依赖默认领域包或精选目录。

发布检查包含该客户端、编译声明索引、公共入口、全库公理审计及负向回归。新增回归拒绝奇异重块、遗漏源或探针偏移、丢弃重构度规、交换算符次序、把保留阶数当成精确等式、错误常数项、零质量解算及凭空给出零误差。当前验证状态以 [VERIFIED](../VERIFIED.md) 和[能力清单](capabilities.md)为准。

下一步的选择遵循全局待办：与谱域和数值证据接通、扩展传播重场操作，与多体模型／动力学读数的建设共同排序。增加某个固定消元例子不提升上述开放能力的状态。

传播重场专项测试 `python3 scripts/test_heavy_field_matching.py` 用独立精确微分覆盖七组可变维数／阶数模型，并检查实际积分、非零端点、指南片段。新增拒绝检查覆盖质量对称性、变量系数求导、算符次序、截断阶数、残差、源／探针项、光滑性和区间一致性。完整发布状态见 VERIFIED，专项通过不替代全量发布运行。
