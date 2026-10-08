# 实际场、作用量变分与边界条件

本批对应全局路线 R07，连接 C10/C11 的形式作用量操作与 C19/C20 的实际导数、积分和误差。输入可以更换场分量、方向、动能混合、相互作用势和扰动；公共操作接受任意一阶多项式密度。

## 已连接的研究步骤

| 操作 | 输入与保证 |
| --- | --- |
| 实际场求值 | 场 `φ a : E → ℝ`，显式方向向量 `e μ : E`；梯度槽取实际 `fderiv ℝ (φ a) x (e μ)`。 |
| 局部第一变分 | 对 C² 场与可微扰动，证明实际 `Euler × 扰动 + 边界流散度` 恒等式；扰动密度的参数导数也有 `HasDerivAt` 证明。 |
| 符号 jet 解释 | 一维光滑剖面的每阶 jet 取同一个场的迭代导数；总导数与实际求导相容，原符号 Euler 方程等于实际 Euler 残差。 |
| 区间作用量求导 | `action` 是实际区间积分。多项式扰动的连续性与紧致性给出积分号下求导所需的控制，调用者无需额外假设可交换求导和积分。 |
| 边界与驻值 | 第一变分保留两端通量。通量相等或扰动在两端为零时才能消去；实际 Euler 方程进一步推出驻值。 |
| Noether 流 | 实际光滑场上的流满足含方程残差的积分平衡；壳上两端值相等，离壳残差和显式破缺则产生累计误差界。 |

公共源码：[FieldEvaluation](../LeanPhy/FieldTheory/FieldEvaluation.lean)、[CurveJet](../LeanPhy/FieldTheory/CurveJet.lean)、[IntervalAction](../LeanPhy/FieldTheory/IntervalAction.lean)。共用的多项式链式法则与积分证明分别位于 [PolynomialEvaluation](../LeanPhy/Mathematics/PolynomialEvaluation.lean)、[PolynomialIntegral](../LeanPhy/Mathematics/PolynomialIntegral.lean)。

## 实际局部场

`E` 可以是任意实赋范空间；方向向量显式给出，不隐式选择度规、时空符号或坐标基。局部密度使用实际场值和方向导数。残差约定与原形式层相同：

```text
π_a^μ(x) = (∂L/∂(∂_μ φ_a)) evaluated on φ and its actual derivatives
E_a(x)   = (∂L/∂φ_a)(x) − Σ_μ ∂_μ π_a^μ(x)
δL(x)    = Σ_a E_a(x) η_a(x) + Σ_μ ∂_μ(Σ_a π_a^μ(x) η_a(x))
```

这里 `δL` 是 `L[φ+sη]` 在 `s=0` 的实际导数；`FieldEvaluation.hasDerivAt_value_perturb` 证明这项解释。动量的可微性由密度的多项式结构与场的 C² 正则性推导。

```lean
import LeanPhy.Entry.FieldTheory

open LeanPhy.FieldTheory
open scoped BigOperators ContDiff

example {Field Direction E : Type*} [Fintype Field] [Fintype Direction]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : FirstOrderLagrangian ℝ Field Direction)
    (e : Direction → E) (φ η : Field → E → ℝ) (x : E)
    (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    (hη : ∀ i, DifferentiableAt ℝ (η i) x) :
    FieldEvaluation.variation L e φ η x =
      (∑ i, FieldEvaluation.euler L e φ i x * η i x) +
      FieldEvaluation.divergence e (FieldEvaluation.boundary L e φ η) x :=
  FieldEvaluation.first_variation L e φ η x hφ hη
```

对于给定背景剖面，可把它作为额外场输入并令对应扰动为零。此时使用完整第一变分或匹配端点公式保留实际变分范围；`stationary_of_euler` 是所有分量满足方程时的充分条件，不要求使用者把未变分背景也当成动力学未知量。

## 从实际作用量得到驻值条件

`IntervalAction` 的方向类型为 `Unit`，自变量为实数。它可表示有限模式的时间作用量，或一维静态场剖面的泛函；两种解释的符号由密度本身给出。积分允许反向和重合端点。

`hasDerivAt_action_boundary` 证明

```text
d/ds S[φ+sη]|₀ = ∫_a^b Σ_i E_i(t) η_i(t) dt + [Σ_i π_i(t) η_i(t)]_a^b
```

对于任何一阶多项式密度，C¹ 场／扰动足以给出积分导数；将其写成 Euler 残差与端点项使用 C² 场、C¹ 扰动。`hasDerivAt_action_matched_endpoints` 消费实际端点通量相等的证明，`hasDerivAt_action_fixed_endpoints` 消费扰动在两端为零的证明。

```lean
import LeanPhy.FieldTheory.IntervalAction

open LeanPhy.FieldTheory
open scoped ContDiff

example {Field : Type*} [Fintype Field]
    (L : FirstOrderLagrangian ℝ Field Unit) (φ η : Field → ℝ → ℝ)
    (hφ : ∀ i, ContDiff ℝ 2 (φ i)) (hη : ∀ i, ContDiff ℝ 1 (η i))
    (a b : ℝ) (ha : ∀ i, η i a = 0) (hb : ∀ i, η i b = 0)
    (hE : ∀ t ∈ Set.uIcc a b, ∀ i,
      FieldEvaluation.euler L IntervalAction.direction φ i t = 0) :
    HasDerivAt (fun s => IntervalAction.action L (FieldEvaluation.perturb φ η s) a b) 0 0 :=
  IntervalAction.stationary_of_euler L φ η hφ hη a b ha hb hE
```

驻值不是最小值，也没有自动得到 Euler 方程解的存在性或稳定性。当前正则性假设定义在整个实轴／环境空间；尚未提供一般开区域上的局部正则性适配器。

## 符号结果与近似候选

`CurveJet.evaluate` 将 `jet a α` 映射到 `iteratedDeriv (α ()) (φ a)`。对 C∞ 剖面，`hasDerivAt_evaluate` 对任意阶多项式 jet 证明总导数相容；`evaluate_eulerLagrange` 因此把既有符号推导接到实际方程。这个通用高阶桥使用 C∞，而上述直接作用量积分接口只需明确的 C¹/C² 条件。

对于实际剖面，`IntervalAction.noether_balance` 保留离壳项：

```text
J(b) − J(a) = −∫_a^b Σ_i E_i(t) η_i(t) dt
```

若还有显式对称破缺 `δL − ∂B`，`noether_drift_certificate` 复用原残差模块。假设**整个区间**内已证明 `|E_i| ≤ ε_i`、`|η_i| ≤ M_i`、破缺绝对值至多 `δ`，得到：

```text
ErrorCertificate J(b) J(a) ((δ + Σ_i ε_i M_i) · |b−a|)
```

该结论控制真实流的端点变化。预算可继续与既有误差证书组合；采样点、未核验的数值求解输出或任意 jet 赋值不能代替区间假设。

## 客户端与拒绝检查

[ActionEvaluationResearch](../LeanPhy/Examples/ActionEvaluationResearch.lean) 消费公共层，检查混合动能的实际交叉加速度、任意势和动能混合的剖面方程，以及相互作用平移对称性的实际流。它还保留两个关键检验：

- 自由密度 `L=(φ′)²/2`，剖面 `φ(t)=t` 满足体方程，但扰动 `η(t)=t` 改变端点场值，固定积分区间 `[0,1]` 上的作用量导数为 `1`。这个反例进入已有探索账本，原正向猜想不会被反例关闭。
- 剖面 `φ(t)=t²` 的方程残差为 `−2`，公共积分误差定理给出非零流变化预算 `2`。

```bash
lake build leanphy_action_evaluation_client
lake exe leanphy_action_evaluation_client --project-json
lake exe leanphy_action_evaluation_client --strict
```

报告有 9 条结论和 4 项开放任务：被反驳的无边界条件猜想，以及解存在／稳定性、多维时空边界／电荷、协变／分级场三类后续研究义务。严格模式应失败。负向回归检查端点、正则性、实际剖面、交叉项、误差预算和探索目标绑定。

## 全局范围

R07 获得实际场求值和有限区间积分链；R09 的对称解释与 C19 的残差传播也获得实际消费。仍需场重定义、IBP/EOM 算符关系、协变与 Grassmann 场、多维区域边界通量及积分电荷。R04/R05 的算符与真实态关联、R08 的传播重场／酉约化、R10 的自洽条件和 R11 的可靠数值包络保持独立优先级。

多维局部第一变分不等于多维积分定理；一维 Noether 端点结论不自动等于场论的空间积分电荷守恒。验证状态见 [VERIFIED](../VERIFIED.md)。
