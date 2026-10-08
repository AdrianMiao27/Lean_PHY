# 场替换、外源与一阶边界条件

本功能对应 R07，连接 C10 的局部变分、实际场与区间作用量，并为 R08 的算符基操作提供可组合输入。当前范围是**实系数、可交换场的多项式点变换**：旧场 `φ_a = F_a(ψ)` 不依赖新场导数，也没有显式坐标依赖。

## 已实现的公共操作

| 模块 | 输入与输出 | 适用范围 |
| --- | --- | --- |
| [PointTransformation](../LeanPhy/FieldTheory/PointTransformation.lean) | 任意有限新场、多项式场映射、旧密度 → 变换后的密度；势、梯度、外源一起传输 | 精确多项式操作；组合与恒等变换有证明；逆向恢复需给出实际多项式复合恒等式。 |
| [TransformationEvaluation](../LeanPhy/FieldTheory/TransformationEvaluation.lean) | 场映射和实际可微剖面 → 实际密度及区间作用量相等；有限单元表 → 相应实际权重相等 | 实际梯度需要可微性；有限表保留相同构型标签，不是连续测度变量替换。 |
| [EulerTransport](../LeanPhy/FieldTheory/EulerTransport.lean) | 实际密度 → Jacobian 转置 Euler 残差、动量／变分流、实际作用量导数；右逆或非零行列式 → 域内方程对应 | 任意有限场数与恒定坐标方向；实际场要求 C²；逆向结论显式保留正则域，不推断全局逆场坐标。 |
| [RedefinitionVariation](../LeanPhy/FieldTheory/RedefinitionVariation.lean) | `φ → φ + s P(φ)` → 实际区间作用量在 `s=0` 的导数 | 显式保留 Euler 体积分和端点通量；满足方程与匹配边界后才推出一阶驻值。 |

梯度按全 Jacobian 变换：

\[
\partial_\mu\phi_a=\sum_b\frac{\partial F_a}{\partial\psi_b}\partial_\mu\psi_b.
\]

`pullback` 对整个密度作用。因此 `J φ` 一般不再是 `J ψ`；比如 `φ = ψ + g ψ³` 时，它成为 `J(ψ + g ψ³)`，动能同时获得 `(1 + 3gψ²)²` 因子。密度、源、探针与场表述必须一致。

## 精确变换与组合

下面的证明接受任意密度和两次场变换，不依赖某个内置作用量。

```lean
import LeanPhy.FieldTheory.PointTransformation

open LeanPhy.FieldTheory PointTransformation

example {A B C D : Type*} [Fintype B] [Fintype C]
    (F : A → MvPolynomial B ℝ) (G : B → MvPolynomial C ℝ)
    (L : FirstOrderLagrangian ℝ A D) :
    pullback G (pullback F L) = pullback (compose F G) L :=
  pullback_compose F G L
```

`pullback_inverse` 需要证明 `aeval G (F a) = X a`；这只是所述方向的恢复条件，不能从任意 `F` 自动推断逆映射。客户端用双场非线性剪切验证该接口。现在 `EulerTransport` 已推导实际 Euler 方程及正则域内的逆向传输；全局逆映射、不同分支的覆盖和逆坐标范围仍需另外构造。

`value_pullback` 将形式密度接到实际场，`action_pullback` 给出区间作用量对应。有限单元表则使用 `finiteAction_pullback` 和 `finiteProbability_pullback`：每个原构型的梯度槽也按同一映射变换，权重因而相同。这里没有删改构型、假设测度不变或推导量子 Jacobian。

## 运动方程、变分流与正则域

令 `J_ab = ∂F_a/∂ψ_b`，库从完整密度与实际 C² 场证明

\[
E_b(F^*L)[\psi]=\sum_a J_{ab}(\psi) E_a(L)[F(\psi)],\qquad
\pi_b^\mu(F^*L)=\sum_a J_{ab}\pi_a^\mu(L).
\]

力项会产生 Hessian 项；这些项与动量中 Jacobian 的导数相消。源和动能混合都参与推导，调用方不需要提供最终方程等价的证明。

```lean
import LeanPhy.FieldTheory.EulerTransport

open LeanPhy.FieldTheory PointTransformation
open scoped ContDiff BigOperators

example {Old New Dir : Type*} [Fintype Old] [Fintype New] [Fintype Dir]
    (F : Old → MvPolynomial New ℝ) (L : FirstOrderLagrangian ℝ Old Dir)
    (e : Dir → ℝ) (ψ : New → ℝ → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b))
    (x : ℝ) (b : New) :
    FieldEvaluation.euler (pullback F L) e ψ b x =
      ∑ a, FieldEvaluation.euler L e (transformed F ψ) a x * jacobian F ψ a b x :=
  euler_pullback F L e ψ hψ x b
```

正向传输允许矩形或奇异映射：原方程在 `F(ψ)` 成立，则新方程成立。反向恢复使用 `euler_recover`：给出矩形 Jacobian 的右逆 `J K = I_old`，库导出 `E_old = Kᵀ E_new`。左逆 `K J = I_new` 不能替代这个条件。

方阵情形只需证明行列式非零，库由实际矩阵构造逆。可以在研究者指定的区域内使用这一结论：

```lean
import LeanPhy.FieldTheory.EulerTransport

open LeanPhy.FieldTheory PointTransformation
open scoped ContDiff

example {Field Dir : Type*} [Fintype Field] [DecidableEq Field] [Fintype Dir]
    (F : Field → MvPolynomial Field ℝ) (L : FirstOrderLagrangian ℝ Field Dir)
    (e : Dir → ℝ) (ψ : Field → ℝ → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b))
    (S : Set ℝ) (hregular : ∀ x ∈ S, (jacobianMatrix F ψ x).det ≠ 0) :
    (∀ x ∈ S, ∀ b, FieldEvaluation.euler (pullback F L) e ψ b x = 0) ↔
      (∀ x ∈ S, ∀ a, FieldEvaluation.euler L e (transformed F ψ) a x = 0) :=
  euler_zero_iff_on_of_det_ne_zero F L e ψ hψ S hregular
```

此处证明的是指定剖面与其像的方程对应。库不会由点态正则性推断全局一一映射，也不会自动求解正则域。客户端证明非线性双场剪切的行列式恒为 1；另一条实际反例取 `φ=ψ²` 和线性源 `L=φ`：在 `ψ=0` 时，新 Euler 残差为 0，原残差仍为 1，奇异点不能用作反向传输的证据。

`pushVariation F ψ η` 构造 `δφ=Jη`；`boundary_pullback` 保持完整变分流，`variation_pullback` 保持实际第一变分。`action_derivative_pullback` 进一步将新变量下的实际区间作用量导数写为原场的 Euler 体积分与两个端点项。边界流对应不意味着流为零，区域积分仍限已实现的一维区间。

## 按运动方程化简时保留边界与阶数

对于点变换方向 `P`，实际作用量导数为

\[
\left.\frac{d}{ds}S[\phi+sP(\phi)]\right|_{s=0}
=\int_a^b\sum_i E_i(L)P_i(\phi)\,dt
+\left[\sum_i\pi_iP_i(\phi)\right]_a^b.
\]

库从已证明的区间变分定理导出它；没有要求调用方先提供该等式。下例明确保留方程、正则性与边界前提。

```lean
import LeanPhy.FieldTheory.RedefinitionVariation

open LeanPhy.FieldTheory PointTransformation
open scoped ContDiff

example {Field : Type*} [Fintype Field]
    (P : Field → MvPolynomial Field ℝ) (L : FirstOrderLagrangian ℝ Field Unit)
    (φ : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ 2 (φ i)) (a b : ℝ)
    (hboundary : IntervalAction.endpoint L φ (transformed P φ) b =
      IntervalAction.endpoint L φ (transformed P φ) a)
    (hE : ∀ t ∈ Set.uIcc a b, ∀ i,
      FieldEvaluation.euler L IntervalAction.direction φ i t = 0) :
    HasDerivAt (fun s => IntervalAction.action (pullback (infinitesimal P s) L) φ a b) 0 0 :=
  action_infinitesimal_on_shell P L φ hφ a b hboundary hE
```

这是在零点的一阶导数结论。不能把它当成有限参数下精确相等、任意 EFT 阶数的 EOM 冗余或散射振幅不变。客户端检验 `L = (∂φ)²`、`φ(t)=t` 的缩放：体方程成立，但实际作用量为 `(1+s)²`，导数为 `2`，省略边界或二阶项都会给出错误结果。

## 验证和剩余工作

[物理客户端](../LeanPhy/Examples/FieldRedefinitionResearch.lean) 保留 13 条结论、4 项开放义务，包含任意场数的传输、剪切的域内方程对应和奇异映射反例。独立有理表回归改变场数、方向数、非线性系数、混合梯度／源项，核对实际替换值；拒绝检查覆盖 Jacobian、源项、逆向条件、边界、正则性和有限阶区别。专项与入口／客户端检查已通过，当前工作树完整发布检查尚未完成。发布证据以 [VERIFIED](../VERIFIED.md) 为准。

本批已补多项式点场替换的实际 Euler／变分流传输及显式正则域条件。下一步继续全局逆坐标与分支、IBP/EOM 的保留阶数及导数依赖操作。导数依赖变换、多维边界、协变／分级场、量子测度与散射条件仍开放。真实态关联 R05、受控匹配 R08 和数值包络 R11 保持独立优先级；本功能没有替代这些任务。
