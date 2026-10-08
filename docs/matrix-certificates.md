# 复矩阵残差证书与有效理论误差

这一层把外部给出的近似逆接到 Lean 中的实际有限矩阵、谱域和分块消元。研究者提供名义矩阵、近似逆和误差预算；Lean 重新计算有理残差，检查接受条件，然后构造精确逆并证明误差界。输入中的“逆范数上界”是近似矩阵 `K` 的界，不是要求用户预先知道精确逆的界。

## 输入、接受条件与结论

名义矩阵为 `A`，近似逆为 `K`，实际模型为 `D`。数据使用两个有理矩阵表示复数的实部与虚部；乘法实现复数乘法，包含交叉项。采用的矩阵范数是 **L∞ 算子范数**，向量范数是最大分量范数；不是逐元素最大值，也不是 Hilbert 空间的 L² 算子范数。需要 L² 读数时，应另行证明范数转换及其维数因子，不能只切换记号沿用相同数值界。

`RationalMatrix.Bounded` 检查每行的有理和 `∑ (|re| + |im|)`。它给出复矩阵 L∞ 算子范数的保守上界，适用于矩形和空矩阵。

候选证书包含非负有理预算 `κ`、`r`、`ε`，并实际检查：

```text
||K|| ≤ κ
||1 − A K|| ≤ r
ε ≥ 0
q = r + ε κ < 1
```

前两项由有理行界推出，残差 `1 − A K` 在 Lean 内部计算。对任何满足 `||D − A|| ≤ ε` 的实际矩阵，证明链给出：

```text
||1 − D K|| ≤ q
D 可逆
||D⁻¹|| ≤ κ / (1 − q)
||D⁻¹ − K|| ≤ κ q / (1 − q)
```

`ResidualInverse.unit` 利用收敛几何级数和有限矩阵的一侧逆性质构造两侧逆。后两个界由实际残差恒等式推出，不以精确逆或其范数为输入。模型偏差先进入 `q`，因此不能在计算误差时丢掉舍入、参数变化或数据不确定性。

`q ≥ 1` 表示这个证书不足以确认结论，不表示矩阵一定奇异。边界 `q = 1` 不被接受。

| 公共模块 | 提供的功能 |
| --- | --- |
| [RationalMatrix](../LeanPhy/Mathematics/RationalMatrix.lean) | 精确复矩阵数据运算、实现正确性、可判定行界、逐元素包络到范数界 |
| [ResidualInverse](../LeanPhy/Mathematics/ResidualInverse.lean) | 从右残差构造精确逆、逆范数与误差、模型扰动预算 |
| [MatrixCertificate](../LeanPhy/Mathematics/MatrixCertificate.lean) | 有理接受判据、实际矩阵上的 soundness、绑定名义数据和候选的外部证书接口 |
| [CertifiedElimination](../LeanPhy/Mathematics/CertifiedElimination.lean) | 不同维数的轻／重空间，有效算符、源、重构、线性探针与偏移的误差 |
| [CertifiedResolvent](../LeanPhy/Quantum/CertifiedResolvent.lean) | 实际有限谱排除域、圆盘内一致逆界、既有能量依赖有效 Hamiltonian 的构造 |

## 外部候选到内核证明

输入格式见 [complex-heavy.json](../examples/matrix-certificates/complex-heavy.json)。例如，名义重块为
`[[4,i],[-i,4]]`，候选为 `K = I/4`；取 `κ = r = 1/4`、`ε = 1`，得到 `q = 1/2`、逆范数界 `1/2` 和逆误差界 `1/4`。

```bash
python scripts/matrix_certificate.py examples/matrix-certificates/complex-heavy.json \
  --output /tmp/ComplexHeavy.lean --report /tmp/ComplexHeavy.json
lake env lean /tmp/ComplexHeavy.lean
```

生成器接受整数或精确有理／十进制字符串，例如 `"1/4"`、`"0.125"`。它拒绝 JSON 浮点数，避免把二进制浮点误差悄悄当作精确输入。十进制字符串按其精确十进制值解释；如果它来自测量或舍入，仍需把与实际模型的差异计入包络。

Python 预检查失败时不产生文件。通过时，报告仍标为 `candidate_requires_lean_check`；输入摘要只用于追溯，不是数学证据。生成的 `accepted` 定理使用 `decide +kernel`，由 Lean 内核计算有限有理判据。随后 `MatrixCertificate.sound` 生成实际矩阵结论。即使绕过 Python 预检查，篡改候选后也必须重新通过 Lean。

输出文件默认不能覆盖；显式 `--force` 可替换已有输出，但不会覆盖输入文件。源码名、形状、实虚部和三个预算都进行格式检查。

生成的 [ComplexHeavyCertificate](../LeanPhy/Examples/Generated/ComplexHeavyCertificate.lean) 也演示了 `CertificateEnvelope` / `VerifiedCertificate` 的使用。检查器要求包内候选等于结论索引的候选，并重新消费接受证明；修改包中的矩阵或半径不能靠保留名称或摘要复用旧证据。

## 直接在 Lean 中使用

这一段使用一个标量块，但调用的是任意维数公共检查器。误差界 `1/6` 来自输入的近似逆 `1/3`，不要求用户提供精确逆 `1/2`。

```lean
import LeanPhy.Mathematics.MatrixCertificate

open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open scoped Matrix.Norms.Operator

namespace MyCertificate

def nominal : RationalMatrix 1 1 := ⟨!![2], !![0]⟩

def candidate : Candidate 1 where
  inverse := ⟨!![(1 / 3 : ℚ)], !![0]⟩
  inverseBound := 1 / 3
  residualBound := 1 / 3
  modelRadius := 0

theorem accepted : candidate.Accepted nominal := by decide +kernel

theorem bounded_inverse : Valid nominal candidate := sound nominal candidate accepted

noncomputable def exactUnit : (Matrix (Fin 1) (Fin 1) ℂ)ˣ :=
  candidate.unit nominal accepted nominal.realize (by simp [candidate])

example : ErrorCertificate (↑(exactUnit⁻¹) : Matrix (Fin 1) (Fin 1) ℂ)
    candidate.inverse.realize (1 / 6) := by
  have h := candidate.inverse_error nominal accepted nominal.realize (by simp [candidate])
  have he : (candidate.errorBound : ℝ) = 1 / 6 := by
    norm_num [Candidate.errorBound, Candidate.normBound, Candidate.totalResidual, candidate]
  rw [he] at h
  exact h

end MyCertificate
```

对实际矩阵 `D` 的逐元素包络，可用 `RationalMatrix.enclosure_norm_le`：提供有理误差矩阵 `E`、各行和的界，以及实际证明 `||Dᵢⱼ − Aᵢⱼ|| ≤ Eᵢⱼ`。它将这些条件转换为证书所需的模型范数球。声明一个半径本身不会证明实际模型位于其中。

## 从证书进入物理推导

[MatrixCertificateResearch](../LeanPhy/Examples/MatrixCertificateResearch.lean) 使用上述复 Hermitian 重块、一个轻自由度以及复耦合 `B = [1,i]`、`C = B†`。证书构造能量圆盘 `|z| ≤ 1` 内的实际 `(H − zI)⁻¹`，然后送入既有 `EnergyElimination.Model`：

- 原完整块本征方程与约化方程／重构仍有精确等价证明。
- 近似有效算符是 `−1/2`，对圆盘内每个能量，L∞ 算子误差至多 `1/2`。
- 重源、有效源、重构、线性探针和源诱导偏移使用同一个逆证书；轻、重、读数空间的维数可以不同。
- 谱域命题进入探索工作流，原目标以实际证明关闭，模型和参数条件保留在 Lean 命题中。

```lean
import LeanPhy.Examples.MatrixCertificateResearch

open LeanPhy.Mathematics LeanPhy.Examples.MatrixCertificateResearch
open scoped Matrix.Norms.Operator

example (z : ℂ) (hz : ‖z‖ ≤ 1) : z ∉ spectrum ℂ heavy := disk_excluded z hz

example (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ErrorCertificate (model z hz).effectiveHamiltonian !![-(1 / 2 : ℂ)] (1 / 2) :=
  effective_disk_error z hz

example : package.resolvedObligations.length = 1 := rfl
example : package.obligationCount = 3 := rfl
```

运行研究客户端：

```bash
lake build leanphy_matrix_certificate_client
lake exe leanphy_matrix_certificate_client --project-json
lake exe leanphy_matrix_certificate_client --strict
```

客户端有 9 条结论和 3 类开放任务：新物理模型的包络、能量无关酉低能动态、规模与连续有效性。严格命令应失败。谱圆盘认证只针对声明的有限重块，不推断全耦合 Hamiltonian 的同一谱域。

## 当前范围与验证

本批 R11/R08 提供可核验的精确有理复矩阵数据到物理消元误差的路径。它不提供通用区间算术、不从浮点文件自动导出可靠舍入包络、不认证单个本征值，也不保证自动找到足够好的近似逆。Python 可以替换为任意外部候选生产者；每个候选仍需通过相同的 Lean 检查器。

矩阵采用稠密有限表示，尚无大系统性能承诺。无界算子、无限体积、传播重场匹配、能量无关酉约化和动力学误差仍分别开放。Hermitian 性不是接受判据的一部分；非正规复矩阵也可使用残差证书，物理上需要 Hermitian 的结论必须另行证明。

专项回归与完整发布验证分别记录在 [VERIFIED](../VERIFIED.md)。生成器回归包含独立内核拒绝测试；输入摘要和 Python 预检查不能替代完整声明审计。
