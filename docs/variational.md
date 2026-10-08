# 从作用量到方程、局部流与误差预算

对应全局路线 T1/T2/T5 和能力 C04、C10、C11、C19。此层服务耦合标量场、各向异性有效作用量、有限模式及格点力学模型中的形式推导；凝聚态和高能入口复用相同声明。

新增的[实际场与作用量桥](action-evaluation.md) 已将本页的形式结果连接到实际剖面导数、区间作用量、边界驻值与 Noether 流误差。以下首先说明形式层自身的输入和保证。

## 已实现的推导链

```text
一阶多分量多项式密度 L(φ, ∂φ)
  → 各分量动量 π_a^μ 与 Euler–Lagrange 残差 E_a
  → 第一变分 = Σ_a E_a δφ_a + 完整边界项散度
  → 对称变分／平移变分 → Noether 流／正则能动张量
  → 精确壳上局部守恒，或非零残差下的局部误差证书
```

`FirstOrderLagrangian R Field Direction` 用不同变量槽表达 `φ_a` 与 `∂_μ φ_a`。它只容纳一阶导数，不能把二阶作用量直接传给一阶公式。`JetPolynomial R Field Direction` 则以多重指标表示任意阶形式导数：总导数推进每个场分量，不在加速度之后截断。两种类型之间有显式 `lift`。

残差约定为

\[
E_a(L)=\frac{\partial L}{\partial\phi_a}
       -\sum_\mu D_\mu\frac{\partial L}{\partial(\partial_\mu\phi_a)}.
\]

`first_variation` 证明

\[
\delta L=\sum_a E_a\eta_a+
D_\mu\left(\sum_a\pi_a^\mu\eta_a\right).
\]

当已有证明给出 `δL = D_μ B^μ` 时，`noether_off_shell` 推出 `D_μ J^μ = -Σ_a E_a η_a`，其中 `J^μ = Σ_a π_a^μ η_a − B^μ`。边界项不会被隐式置零。平移变分 `η_a = ∂_ν φ_a` 的对称性由 `firstVariation_translation` 从任意一阶密度证明，进而得到 `canonicalStressTensor_off_shell`；不要求调用者直接提交最终守恒结论。

## 任意分量的耦合作用量

`quadraticAction K V` 接受任意有限场集合、有限方向集合、常系数动能张量 `K_(aμ,bν)` 和任意场值多项式势 `V`。`K` 明确承载时空符号、各向异性和动能混合；它不默认正定、对角或可逆。

```lean
import LeanPhy.Entry.FieldTheory

open LeanPhy.FieldTheory
open LeanPhy.FieldTheory.JetPolynomial
open LeanPhy.FieldTheory.FirstOrderLagrangian
open scoped BigOperators

example {Field Direction : Type*} [Fintype Field] [Fintype Direction]
    (K : (Field × Direction) → (Field × Direction) → ℝ)
    (hK : ∀ i j, K i j = K j i)
    (V : MvPolynomial Field ℝ) (a : Field) :
    eulerLagrange (quadraticAction K V) a =
      -lift (potential (MvPolynomial.pderiv a V)) -
        ∑ μ, ∑ j, MvPolynomial.C (K (a, μ) j) *
          jet j.1 (Finsupp.single j.2 1 + Finsupp.single μ 1) :=
  eulerLagrange_quadraticAction K hK V a
```

若不满足 `hK`，`momentum_quadraticKinetic` 保留 `K` 与其转置两部分；不能使用只含一个指标顺序的动量公式。一般 `FirstOrderLagrangian` 也允许场依赖的导数耦合，回归已验证 `φ₀ ∂ₜφ₀ ∂ₜφ₁` 的链式项。常系数二次动能定理只是这一公共变分操作的可复用特例。

## 模型表示和约定转换

- `eulerLagrange_renameFields`：对场标签的单射重命名保持推导结果。有限模式的重排可用等价映射；合并两个场不是单纯重命名。
- `eulerLagrange_toMechanical`：一阶时间作用量转成原有 `(q,v,a)` 多分量接口后，方程残差一致，包括交叉加速度项。
- `toFieldJets`：任意阶 jet 到三槽 jet 的形式投影。三阶及以上被置零；它不是物理解的截断误差定理。上述一致性定理限定一阶时间作用量，其方程只用到零、一、二阶导数。
- `canonicalStressTensor L μ ν`：第一个槽是流／散度方向，第二个槽是平移方向；未隐式用度规升降指标。这里得到正则张量，未声称对称、规范不变或完成改进项。

## 近似候选解与显式破缺

`noether_residual_certificate` 不要求候选满足精确 Euler 方程。给定求值映射 `ev` 及证明

\[
|ev(E_a)|\le\epsilon_a,\qquad |ev(\eta_a)|\le M_a,\qquad
|ev(\delta L-D_\mu B^\mu)|\le\delta,
\]

可构造现有公共类型 `ErrorCertificate`，结论是

\[
|ev(D_\mu J^\mu)|\le\delta+\sum_a\epsilon_a M_a.
\]

`noether_residual_of_symmetry` 和 `canonicalStressTensor_residual` 提供精确对称性及平移的专用入口。输出可继续使用既有证书的合成工具；非零预算不会自动变成精确守恒。

[VariationalResearch](../LeanPhy/Examples/VariationalResearch.lean) 检查交叉动能、导数耦合、共同平移对称性、含任意质量平方与四次耦合的 1+1 维标量方程，以及一个流散度确实等于 `2` 的离壳候选：其误差半径为 `2`，而非零。研究报告保留光滑解与积分电荷两项开放义务：

```bash
lake exe leanphy_variational_client --project-json
# 此命令按预期失败：形式推导尚未完成解析义务
lake exe leanphy_variational_client --strict
lake exe leanphy_index --query 'eulerLagrange quadraticAction' --kind theorem
lake exe leanphy_index --query 'noether residual' --kind theorem
```

## 范围与后续工作

已有定理是平直坐标中**可交换场的一阶局部多项式恒等式**。标量系数在总导数下为常数，没有显式坐标依赖；背景剖面需要作为带 jet 的额外场处理，并单独确定哪些场被变分。未实现 Grassmann 场、规范协变 jet、约束／退化体系的完整处理、广义坐标变换或高阶作用量变分。

求值映射不自动保证各 jet 值来自同一个光滑场。在时空区域上应用误差界，需要在整个区域证明输入界；单点数值或采样不能替代。[IntervalAction](../LeanPhy/FieldTheory/IntervalAction.lean) 现已提供一维实际剖面的作用量积分、端点条件、Noether 平衡和累计残差误差；[CurveJet](../LeanPhy/FieldTheory/CurveJet.lean) 证明其光滑 jet 解释。多维时空区域、空间积分电荷、局部区域正则性及解存在性仍需继续桥接。本批没有实现 Green 函数、顶角／振幅、低能消元或圈重整化；这些仍按 [全局路线](roadmap.md) 推进。
