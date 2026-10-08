# 有限量子动力学与非对易热响应

这组公共操作连接实际矩阵指数、密度态、Hamiltonian 扰动和探针读数，服务有限体积凝聚态模型及有限模式场论。它接受任意有限指标、耦合矩阵、初态和探针；不要求扰动与原 Hamiltonian 对易，也不求参数可微的本征基。

对应全局清单 C04/C05/C08/C13/C20 和待办 R06。四个公共模块已接入，独立客户端目前有 11 条结论和 3 组开放义务；模块和客户端检查已通过，当前新增范围的完整发布检查尚未完成，见 [VERIFIED](../VERIFIED.md)。这不是一般连续 QFT、任意时变驱动或完整频域输运工具。

## 操作与物理约定

| 模块 | 输入与输出 | 证明中的关键边界 |
| --- | --- | --- |
| [Duhamel](../LeanPhy/Mathematics/Duhamel.lean) | 完备实赋范代数中的生成元、扰动、时间 → 实际指数差分与参数导数、共轭变化的积分对易子 | 从指数时间导数和积分基本定理推导；没有将最终积分恒等式作为输入。 |
| [DynamicalResponse](../LeanPhy/Quantum/DynamicalResponse.lean) | 有限 H、V、态和探针 → Heisenberg／态导数、图像读数一致性、有限时间响应及接触项 | 使用 ℏ = 1、`H + ε V`、`exp(+itH)`；物理态构造消费 Hermitian 和密度证明。 |
| [ThermalPerturbation](../LeanPhy/Quantum/ThermalPerturbation.lean) | 有限 H、V、O、O′、β → 实际归一化 Gibbs 期望的导数 | 实参数 Hermitian 扰动族；非空有限空间保证 Z > 0；不要求谱非简并。 |
| [FiniteFrequencyResponse](../LeanPhy/Quantum/FiniteFrequencyResponse.lean) | 给定有限 Fourier 系统和采样时间 → sampled step response 的频率系数、逆变换重构和 Parseval 关系 | 只对提供的有限网格精确；采样时间、归一化和 Fourier 系统由调用方提供，不推出平稳性或连续谱。 |

Heisenberg 算符为

\[
O_H(t)=e^{itH}Oe^{-itH},\qquad
\partial_t O_H(t)=i[H,O_H(t)].
\]

`Dynamics.state` 用相反时间构造物理态，得到 `∂t ρ(t) = -i[H,ρ(t)]`。
`state_expectation` 证明演化态与演化探针的迹读数相同；因此两种图像没有各自独立的符号约定。

## 从真实演化得到响应

`expectation_perturbation_integral` 证明

\[
\left.\frac{d}{d\varepsilon}
\operatorname{Tr}(\rho\,O_{H+\varepsilon V}(t))\right|_{0}
=\int_0^t i\operatorname{Tr}(\rho[V_H(s),O_H(t)])\,ds.
\]

这里初态固定，不要求它是平衡态。核保留两个时间参数；尚未把它替换为只依赖时间差的表达式。`H - ε V` 的源约定需要取相反号。

`stepExpectation` 表示在零时刻打开常值扰动：`t ≤ 0` 使用原 H，`t > 0` 使用 `H + ε V`。`step_response_derivative` 证明该实际读数对振幅的导数，`step_response_causal` 给出过去及零时刻的零响应。这是一个常值开关源的结论；一般时间轮廓与时间有序传播子仍开放。未加开关的积分对负时间是有向积分，不能直接称作过去的零响应。

若探针同时变为 `O + ε O′`，`expectation_perturbation` 保留 `Tr(ρ O′_H(t))` 接触项。初态本身随参数变化的导数不是此定理的输入，应另行相加和证明。

以下代码消费现有有限态，而无需展开具体维数：

```lean
import LeanPhy.Quantum.DynamicalResponse

open LeanPhy.Quantum LeanPhy.Quantum.Dynamics
open scoped Matrix Matrix.Norms.Operator

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : FiniteDensity ι) (H V O : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun ε : ℝ => expectation ρ.rho (H + ε • V) O t)
      (∫ s in (0 : ℝ)..t, kernel ρ.rho H V O t s) 0 :=
  expectation_perturbation_integral ρ.rho H V O t
```

此解析恒等式对任意矩阵也成立；若需要解释为封闭系统的物理演化，H 和 V 应为 Hermitian。`state` 的构造直接要求 H 的 Hermitian 证明；`ThermalPerturbation.perturbed_hermitian` 将 H、V 的证明传给整族 `H + ε V`。

## 有限采样到频率系数

`FiniteFrequencyResponse` 把上述实际 step response 在调用方给出的有限时间表 `times : α → ℝ` 上采样，再消费 `FiniteFourierSystem` 的正变换。`finiteFrequencyResponse_inverse` 和 `finiteFrequencyResponse_reconstruct_at` 精确恢复每个采样读数，`finiteFrequencyResponse_parseval` 保留该 Fourier 系统的归一化。因而它可用于有限体积数值模型的离散频率读数和回归检查：

```lean
import LeanPhy.Quantum.FiniteFrequencyResponse

open LeanPhy.Quantum LeanPhy.Quantum.Dynamics
open LeanPhy.Mathematics

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ H V O : Matrix ι ι ℂ) (times : Fin 4 → ℝ) :
    FiniteFourierSystem.inverse FiniteFourierSystem.fourier4
        (finiteFrequencyResponse FiniteFourierSystem.fourier4 ρ H V O times) =
      sampledStepResponse ρ H V O times :=
  finiteFrequencyResponse_inverse FiniteFourierSystem.fourier4 ρ H V O times
```

这个桥不把采样序列视为平稳关联函数，也不自动进行时间差化简、连续 Fourier 积分、无限时间／体积极限、输运谱或谱收敛估计。一般时间轮廓、平稳性证明、连续频率表示和有限振幅余项仍是 R06 的开放任务。

## 非对易 Gibbs 导数

记 `W = exp(-β H)`、`Z = Tr W`。库使用有向插入积分

\[
D_\beta=\int_0^{-\beta} e^{(-\beta-s)H}V e^{sH}\,ds
\]

证明它是 W 在 `H + ε V` 方向的导数。归一化读数的导数为

\[
\frac{\operatorname{Tr}(D_\beta O+WO')}{Z}
-\frac{\operatorname{Tr}(WO)\operatorname{Tr}(D_\beta)}{Z^2}.
\]

`thermal_expectation_perturbation` 将这个公式连接到实际 `finiteThermalState`。其谱构造可以有简并，证明不对本征矢求导。只有在 `Commute H V` 条件下，`response_of_commute` 才将插入化简为普通协方差形式，并保留负 β 因子和探针接触项。

```lean
import LeanPhy.Quantum.ThermalPerturbation

open LeanPhy.Quantum LeanPhy.Quantum.ThermalPerturbation
open scoped Matrix Matrix.Norms.Operator

example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H V O O' : Matrix ι ι ℂ) (hH : H.IsHermitian) (hV : V.IsHermitian) (β : ℝ) :
    HasDerivAt (fun ε : ℝ => Matrix.trace
      ((finiteThermalState (H + ε • V) (perturbed_hermitian H V hH hV ε) β).rho *
        (O + ε • O'))) (response H V O O' β) 0 :=
  thermal_expectation_perturbation H V O O' hH hV β
```

原始 `mean`／`response` 函数采用 Lean 的全除法。`mean_perturbation` 明确要求 Z ≠ 0；物理热态定理从非空有限空间和 Hermitian H 证明这一条件。有限系统允许任意实 β，温度／单位的物理解释仍需使用者选择。

## 集成与验收

[DynamicsResearch](../LeanPhy/Examples/DynamicsResearch.lean) 使用任意模式数的已构造 CAR Hamiltonian 和热初态消费响应公式，并在 `fourier4` 有限网格上检查实际响应的重构；小矩阵回归用于检查可证伪的边界，不承担通用推导的实现。

```bash
lake build leanphy_dynamics_client
lake exe leanphy_dynamics_client --project-json
lake exe leanphy_dynamics_client --strict
```

客户端有 18 条结论与 3 组开放任务，严格模式应拒绝未决项目。正向证明及负向夹具检查：Heisenberg 与源的符号、非对易输入、可交换规则的前提、热态归一化、接触项、β 因子、开关源的过去响应、Hermitian 扰动条件及有限 Fourier 网格重构。恒等探针的归一化热响应为零，而对应未归一化插入可以非零。

一般 ODE 存在性、任意实验室系驱动、平稳性与时间差化简、连续频率／谱表示、选定参数域的有限振幅余项、无界算符、无限体积及无限时间仍未完成。现有源客户端的广义动力学义务和费米客户端的动力学关联义务继续保留；本批没有证明时间有序 Wick 收缩或这些广义任务的全部目标。

物理背景参考：David Tong 的线性响应讲义第 4.3 节推导源扰动与对易子关联，第 4.3.1 节进一步讨论频率及收敛条件。本实现的旧接口取有限空间、有限时间和常值扰动；新增 R06 接口已覆盖实际非自治解族和连续旋转框架脉冲，但讲义中的任意实验室系驱动、频域极限和输运结论仍不随之自动得到。[作者讲义](https://davidtong.org/pdfs/teaching/kinetic-theory/kinetic4.pdf)。

## 一般时变驱动（R06 增量）

`Quantum.TimeDependentEvolution` 将实际演化表示为 `U(a)=1` 与
\[
 U'(t)=-iH(t)U(t)
\]
的证明对象。由此直接推出 `U(t)†U(t)=1`、态／观测量读数一致性、区间传输的复合律，以及两组演化的精确比较式。一般驱动不能把逆传播写成 `U(-t)`；接口使用伴随和有序传输。

`Quantum.DrivenResponse` 接受一族真实解 `U_ε`，要求共同初值、联合的 `(ε,t)` 连续性和连续源轮廓。它从比较恒等式取 `ε=0` 的实际导数，得到
\[
\partial_\epsilon\operatorname{Tr}(\rho O_\epsilon(t))\big|_0
=\int_a^t i\operatorname{Tr}\rho[ V_H(s),O_H(t)]\,ds .
\]
时间次序、初态和探针接触项都保留；`expectation_contacts` 还显式加入初态导数与探针导数。阶跃接口在 `t≤a` 给出零响应；`response_congr` 说明区间外改变源不影响该一阶读数。

`Quantum.DrivenPulse` 给出一类可实际构造的解：在任意背景演化上，连续包络 `f` 与 Hermitian `B` 产生旋转框架驱动
`f(t) U(t) B U(t)†`，解为背景演化乘以脉冲面积的指数。`pulseFamily_response` 将该构造消费到有限 CAR Hamiltonian 和 Gibbs 初态；它不是把响应积分作为假设输入。

这批结果覆盖有限维、有限区间、连续 Hamiltonian 和联合参数连续性。一般 ODE 存在性、任意实验室系驱动的解构造、有限振幅余项、时间平移不变性、连续频率／输运极限以及无界或热力学极限仍是开放义务。`DrivenFamily` 中的矩阵曲线也不自动证明每个任意给定的 `ρ_ε` 都是正密度；需要实际态构造另行提供。

当前动力学客户端由 11 条结论增至 18 条，仍保留 3 个开放义务。可用检查：

```bash
lake build leanphy_dynamics_client
lake exe leanphy_dynamics_client --project-json
python3 scripts/test_driven_response.py
```
