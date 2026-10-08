# 实际有限系综的自洽与误差

本功能对应全局路线 R10，连接 C08 的有限源响应、C19 的固定点／残差及 C23 的证据接口。三个公共模块接受可更换的构型、可观测量、内部能量、外场和耦合表；[物理客户端](../LeanPhy/Examples/SelfConsistencyResearch.lean) 消费它们。领域入口为 `Entry.StatMech`、`Entry.Condensed` 和 `Entry.FieldTheory`。

## 模型与结果

对非空有限构型 `ι`、有限序参量标签 `σ`，定义

\[
p_m(i)=Z(m)^{-1}\exp\left[-S(i)+\sum_a (J_a+\sum_b K_{ab}m_b)A_a(i)\right],
\qquad F_a(m)=\langle A_a\rangle_{p_m}.
\]

这里的 `p_m` 是实际归一化有限 Gibbs 概率。`SourceFeedback.feedback` 构造 `F`；它不是记录调用方给出的抽象自洽定律。

- [SourceFeedback](../LeanPhy/StatMech/SourceFeedback.lean)：源、耦合插入、实际反馈、全局 Lipschitz 界、压缩证书、残差／读数误差和外场敏感性。
- [FeedbackCertificate](../LeanPhy/StatMech/FeedbackCertificate.lean)：可复用输入界 `Envelope`、有限最大值构造、唯一解与迭代收敛、近似更新和近似读数的误差组合。
- [MeanFieldFunctional](../LeanPhy/StatMech/MeanFieldFunctional.lean)：实际反馈的协方差导数、驻值泛函的方向导数和能量单位转换。

这验证的是**所定义的有限闭合模型**。它与原始相互作用模型之间的近似误差、热力学极限，以及非对易量子自洽仍需独立证明。

## 从输入数据导出适用域

在序参量的上确界范数中，有限输入条件是

\[
|A_a(i)|\le M,\qquad
\sum_b\left|\sum_a K_{ab}A_a(i)\right|\le B.
\]

库从实际源响应证明 `dist (F m) (F n) ≤ q * dist m n`，其中 `q = 2 M B`。`q < 1` 才提供全局唯一解及任意初值的迭代收敛。这个保守充分条件不是临界温度公式；域外不推出无解，也不推出多解。

`Envelope.automatic` 用有限最大值直接构造 `M` 与 `B`，包括空的序参量标签类型。也可提交已证明的较简洁上界以避免枚举巨大构型空间。构造器不要求使用者先证明 `F` 压缩。

```lean
import LeanPhy.StatMech.FeedbackCertificate

open LeanPhy.StatMech SourceFeedback

example {ι σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]
    (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) (K : σ → σ → ℝ)
    (hsmall : (Envelope.automatic A K).rate < 1) :
    ∃ m : σ → ℝ, feedback S A J K m = m := by
  exact ⟨(Envelope.automatic A K).solution S J hsmall,
    (Envelope.automatic A K).solution_isFixedPt S J hsmall⟩
```

`solution` 是由证明确定的数学对象；该 API 没有把实指数或有限最大值变成浮点求解器。数值程序可以产生候选；现在 [Gibbs 数值证书](numerical-gibbs.md) 能对精确有理输入的实际指数和归一化读数生成这一误差证据。

## 残差与可观测量预算

若候选 `m` 的实际残差不超过 `ε`，则

\[
\|m-m_*\|_\infty\le \frac{\varepsilon}{1-q},\qquad
|\langle O\rangle_{p_m}-\langle O\rangle_{p_{m_*}}|
\le 2 N B\frac{\varepsilon}{1-q},\quad |O(i)|\le N.
\]

若外部程序给出更新 `y`，而不是精确 `F(m)`，需要先证明 `dist y (F m) ≤ δ`。实际残差预算是 `dist m y + δ`；可观测量的数值计算误差 `η` 还需另行相加。

```lean
import LeanPhy.StatMech.FeedbackCertificate

open LeanPhy.StatMech LeanPhy.Mathematics SourceFeedback
open scoped NNReal

example {ι σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]
    (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) (K : σ → σ → ℝ)
    (e : Envelope A K) (hsmall : e.rate < 1)
    (m y : σ → ℝ) (δ : ℝ) (hy : ErrorCertificate y (feedback S A J K m) δ)
    (O : ι → ℝ) (N : ℝ≥0) (hO : ∀ i, |O i| ≤ N)
    (value η : ℝ)
    (hv : ErrorCertificate value
      ((SourceEnsemble.probability S A (source J K m)).expectation O) η) :
    ErrorCertificate value
      ((SourceEnsemble.probability S A (source J K (e.solution S J hsmall))).expectation O)
      (η + (2 * N * e.coupling) * ((dist m y + δ) / (1 - e.rate))) := by
  have hr : ErrorCertificate m (feedback S A J K m) (dist m y + δ) :=
    (show ErrorCertificate m y (dist m y) from ⟨dist_nonneg, le_rfl⟩).trans hy
  exact e.evaluated_observable_error S J hsmall m _ hr O N hO value η hv
```

这些证据都绑定实际模型。换外场或耦合后，旧残差不能直接用于新解。相同耦合下的外场扫描可用 `fixedPoint_bias_error`：外场插入界为 `D` 时，解的位移不超过 `2 M D / (1-q)`。

## 温度与驻值的物理解释

能量约定是 `E(i) - Σ_a (h_a + Σ_b G_ab m_b) A_a(i)`。`probability_energy` 证明它对应 `S = β E`、`J = β h`、`K = β G`，两处 β 都保留。有限簇客户端允许任意内部能量和耦合表；对称两态回归的实际线性化是 `β G`。

对称 `K` 下，库实际微分

\[
\Phi(m)=\tfrac12 m^T K m-\log Z(m),\qquad
D_v\Phi(m)=\sum_a(Kv)_a[m_a-F_a(m)].
\]

因此自洽解是方向驻值点。当前没有证明它是变分自由能的极小值，亦没有在奇异 `K` 下宣称逆命题；客户端给出 `K=0` 时驻值但不自洽的实际反例。平均场泛函与变分原则需区分，这一点也见 [Agra、van Wijland、Trizac (2006)](https://arxiv.org/abs/cond-mat/0601125)。本库的接口划分是实现选择，证明来自上述 Lean 模块。

## 验收与开放工作

物理客户端现在记录 11 条结论、4 项开放义务，严格模式拒绝未完成项目。两态非零外场／耦合检查保留 `4/5` 的解误差和 `1/5` 的读数误差；这些只是回归预算，不是最优估计。独立回归从有理有限表核对输入包络及实际反馈 Jacobian，保留协方差减均值和矩阵方向；拒绝检查覆盖温度因子、严格参数域、缺失误差、模型绑定、对称条件与空系综。

原自洽批次已通过完整发布验证；新增数值证书的当前检查范围见 [VERIFIED](../VERIFIED.md)。`GibbsCertificate` 与生成器现已补上精确有理有限表到实际指数权重、残差和解／读数误差的公共链；客户端用非零十进制近似点检查 `1/75000` 的解误差与 `3/200000` 的读数误差。尚未交付：临界附近的局部稳定性／多分支追踪、不确定实输入包络、规模化求解器、闭合模型误差、非对易量子自洽及热力学极限。全局 R05 的真实态关联、R07/R08 的场操作与匹配继续独立推进。
