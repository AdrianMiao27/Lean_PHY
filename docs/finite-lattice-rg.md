# 有限格点、Ward 插入与 RG 误差诊断

`FiniteSchwingerDyson` 与 `FiniteRGDiagnostics` 现在有一个独立的研究出口：
[FiniteLatticeResearch](../LeanPhy/Examples/FiniteLatticeResearch.lean) 和
`leanphy_finite_lattice_client`。它面向有限格点、有限体积截断和有限状态的探索性计算，
把对称插入、算符缩放以及 blocking 误差放在同一条可审计链上。

## 可复用的公共操作

`InvolutiveVariation.ofWeightSymmetry` 接受有限配置空间上的 `Equiv.Perm`、显式的
`e (e i) = i` 证明和权重不变性，构造单位 Jacobian 的 `InvolutiveVariation`。
`weight_symmetry_ward` 随后给出

\[
  \langle O(e i)-O(i)\rangle=0 .
\]

这只是有限和的 Schwinger--Dyson/Ward 形式。调用方仍需把 `e` 和权重对称性解释成
目标格点或截断场论的实际变换；库不会从 `WeightSymmetry` 推出连续函数测度、边界项消失
或规范固定。

`FiniteRGStep.ScalingCertificate` 记录调用方提供的有限算符关系
`fineObs x = lambda * coarseObs (R.coarse x)`，`expectation_scales` 将其传输到归一化
读数。`lambda` 是模型输入；它不会自动被解释为临界指数或 beta 函数。

对于数值或截断 blocking，`FixedPointDefect` 为每个粗配置保存 `coarseWeight` 与
`fineWeight` 的误差半径。`partition_error` 将半径求和为配分函数误差，
`toExpectationComparison` 在调用方给出两个分母下界和插入上界后，生成
`NormalizedExpectationCertificate`。`FixedPointDefect.compose` 和
`compose_partition_error` 只有在中间权重等式显式成立时才会相加两阶段预算。

## 最小客户端形状

```lean
import LeanPhy.Mathematics.FiniteSchwingerDyson
import LeanPhy.Mathematics.FiniteRGDiagnostics

open LeanPhy.Mathematics

theorem ward_step {ι : Type*} [Fintype ι]
    (P : FinitePathIntegral ι) (e : Equiv.Perm ι)
    (hinv : ∀ i, e (e i) = i)
    (hsym : FinitePathIntegral.WeightSymmetry P e) (O : ι → ℂ) :
    P.expectation (fun i => O (e i) - O i) = 0 :=
  P.weight_symmetry_ward e hinv hsym O
```

运行完整客户端报告：

```text
lake exe leanphy_finite_lattice_client --project-json
```

当前客户端登记 6 条参数化的 kernel-checked claims 和 3 项开放义务。`--strict` 会按设计
因连续 Schwinger--Dyson、物理 RG 流以及热力学／临界极限仍未证明而失败。

## 研究边界

这条链可以支撑有限体积回归、blocking 候选比较、Ward 残差预算和观测量误差传播。它不
宣称连续泛函积分、反射正性、普适性、实际 beta 流、临界指数、体积极限或输运极限。
这些结论需要模型特定的尺度约定、投影／闭合误差、均匀估计和分析极限，并作为独立开放
义务推进。
