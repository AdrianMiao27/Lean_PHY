# 指数包络、有限 Gibbs 读数与数值自洽证书

本功能对应 R11，补上已有自洽后验界中的数值输入。公共操作接受任意有限的有理作用量、源、耦合与可观测量表，检查外部程序给出的有理数或十进制近似值，导出**实际实指数系综**的误差证书。凝聚态的有限簇闭合和统计场论的有限 Euclidean 权重共用这一层；生成器不绑定某个 Hamiltonian。

| 入口 | 职责 |
| --- | --- |
| [RationalExp](../LeanPhy/Mathematics/RationalExp.lean) | 有理 Taylor 余项、范围缩减与重复平方、候选输出的误差检查 |
| [GibbsCertificate](../LeanPhy/StatMech/GibbsCertificate.lean) | 归一化读数、源系综、反馈残差及实际解／读数误差 |
| [gibbs_certificate.py](../scripts/gibbs_certificate.py) | 生成待 Lean 检查的数据、接受命题与物理桥；Python 预检不是证明 |
| [SelfConsistencyResearch](../LeanPhy/Examples/SelfConsistencyResearch.lean) | 消费数值证书，保留闭合、临界、多分支及量子义务 |

领域入口为 `Entry.StatMech`、`Entry.Condensed`、`Entry.FieldTheory` 和 `Entry.HighEnergy`；标量包络也从 `Entry.Analysis` 导出。

## 从有理输入到实际指数

`enclose q depth order` 返回有理中心 `c` 与半径 `r`。它先把输入除以 `2^depth`，在绝对值不超过一的范围内用 `order + 1` 项 Taylor 多项式及已证余项界求包络，再逐次平方。每一步都证明包住实际实指数；`Accepted` 检查范围条件以及 `|c-value| + r ≤ error`。

```lean
import LeanPhy.Mathematics.RationalExp
open LeanPhy.Mathematics
set_option maxRecDepth 16384

example : ErrorCertificate (1648721 / 1000000 : ℝ)
    (Real.exp (1 / 2)) (1 / 100000) := by
  have h := RationalExp.sound (1 / 2) 0 10 (1648721 / 1000000) (1 / 100000)
    (by decide +kernel)
  norm_num at h ⊢
  exact h
```

所有数值操作在 `ℚ` 中精确进行。外部求解器可以使用浮点运算，但只提交明确的输出值；证书重新计算完整误差，不需要信任该求解器的舍入模式或停止阈值。这不等于已经验证该求解器的每一步实现。

## 归一化分母与带符号读数

给定指数 `qᵢ` 和观测量 `Oᵢ`，目标是

\[
\langle O\rangle=\frac{\sum_i e^{q_i}O_i}{\sum_i e^{q_i}}.
\]

候选可以选择公共平移 `s`，由库证明 `qᵢ-s` 给出相同的归一化读数。若 `exp(qᵢ-s)` 的包络是 `(cᵢ,rᵢ)`，检查器重新计算

\[
Z_{\rm low}=\sum_i(c_i-r_i),\qquad
R=\left|\sum_i c_i(O_i-v)\right|+\sum_i r_i|O_i-v|.
\]

只有 `Zlow > 0`、`ε ≥ 0`、`R ≤ ε Zlow` 及每个指数的范围条件都通过，才产生 `|v-⟨O⟩| ≤ ε` 的实际定理。这里允许负的 `O`，保留中心值的抵消。非正的分母下界会被拒绝，即使实际系综仍有正配分函数；此时应增加阶数或调整范围缩减。

```lean
import LeanPhy.StatMech.GibbsCertificate
open LeanPhy.Mathematics LeanPhy.StatMech.GibbsCertificate
set_option maxRecDepth 16384

def q : Fin 2 → ℚ := ![1/2, -1/2]
def probe : Fin 2 → ℚ := ![1, -1]
def candidate : Candidate := ⟨0, 0, 12, 462117/1000000, 1/100000⟩

example : ErrorCertificate (candidate.value : ℝ)
    (expectation q probe) (candidate.error : ℝ) :=
  sound candidate q probe (by decide +kernel)
```

`checker q O target` 同时绑定指数表、探针表和目标候选。元数据摘要只用于追溯；替换 payload、模型、读数或预算后必须重新证明接受命题。

## 从外部近似解到物理误差

`feedbackSource` 和 `exponent` 在 Lean 内从 `S,A,J,K,m` 计算指数。生成器的 `feedback` 模式不会把 Python 计算的指数表当作模型桥。每个候选的 `value` 必须等于相应的 `mₐ`，分量预算必须落在共同预算 `ε` 内，然后得到

\[
\|m-F(m)\|_\infty\le\varepsilon.
\]

结合已证输入包络及严格压缩域 `ρ < 1`，`solution_error` 给出 `ε/(1-ρ)` 的真实解误差。`solution_readout_error` 另外检查近似点上的读数预算 `η`，保留总误差 `η + 2NB ε/(1-ρ)`。压缩条件、原模型的闭合误差及数值求值误差各有不同含义。

```lean
import LeanPhy.Examples.Generated.BiasedFeedbackCertificate
open LeanPhy.Mathematics LeanPhy.StatMech
open LeanPhy.Generated.GibbsCertificates.BiasedFeedback

example
    (e : SourceFeedback.Envelope
      (fun a i => (observables a i : ℝ)) (fun a b => (coupling a b : ℝ)))
    (hsmall : e.rate < 1) :
    ErrorCertificate (fun a => (point a : ℝ))
      (e.solution (fun i => (action i : ℝ)) (fun a => (bias a : ℝ)) hsmall)
      ((error : ℝ) / (1 - e.rate)) := solution_bound e hsmall
```

客户端使用外场 `1/3`、耦合 `1/8` 与外部近似点 `0.361413`。Lean 检查实际残差不超过 `10⁻⁵`，再证明解误差不超过 `1/75000`；另一带符号读数保留 `3/200000` 的总误差。这些数值来自非零有理外场，检查器实际计算指数余项。

## 生成与复验

```bash
python3 scripts/gibbs_certificate.py \
  examples/gibbs-certificates/biased-feedback.json \
  --output /tmp/BiasedFeedback.lean --report /tmp/BiasedFeedback.json
lake env lean /tmp/BiasedFeedback.lean
python3 scripts/test_gibbs_certificate.py --report /tmp/gibbs-tests.json
```

JSON 的 `kind` 为 `expectation` 时，提供 `exponents`、`observable` 和 `candidate`；`feedback` 时提供 `action`、`observables`、`bias`、`coupling`、`point`、`candidates` 和共同 `error`。两种模式都需要 `name`。候选有 `shift/depth/order/value/error` 五项；数字为整数或有理／十进制字符串，禁止含糊的 JSON 浮点数字。完整反馈格式见仓库示例。

生成器报告 `candidate_requires_lean_check`，并记录有理数最大位数、生成耗时和源码大小。测试报告另外记录 Lean 检查耗时和进程峰值内存。CLI 对范围缩减／阶数设有有理数规模限制；公共 Lean 定理不依赖这个限制。

## 适用范围与未完成工作

当前输入模型是**精确有理有限表**，输出绑定实际实数系综。它没有自动把不确定实参数、测量误差或其它函数的近似值转成模型输入包络。一般区间／多项式算术、矩阵函数与本征值包络、局部自洽求解器和大规模稀疏性能仍属 R11 后续任务。

这条链不证明闭合模型对原相互作用系统的精度，不证明临界域或多分支稳定性，也不包含非对易量子闭合及热力学极限。精确有理数在重复平方时会增长；本批性能证据应按实际测试规模解读。验证范围和数字统一记录在 [VERIFIED](../VERIFIED.md)，全局取舍见 [roadmap](roadmap.md)。
