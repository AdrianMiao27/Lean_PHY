# LeanPhy v1

LeanPhy 是建立在 Lean 4 和 mathlib 之上的理论物理形式化验证库。它沿用 Lean 的语法、
编辑器、定理库、证明自动化和构建工具，让物理推导能够写成可检查的 Lean 命题。

LeanPhy 验证的是**条件性正确性**：在明确列出的假设下，结论是否确实由这些假设推出。
它检查的是推导的逻辑有效性，不判断模型是否描述真实世界，也不会自动证明连续极限、
热力学极限、路径积分的良定义性或物理解释的正确性。只有写成 Lean 命题并提供通过
检查的证明项，或通过可信接口导入经验证的外部证书，相关内容才会进入已验证结论；
尚未完成的分析论证和物理前提会保留在开放义务账本中。模型说明中的文字本身不会获得
定理地位。

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

English documentation: [README.md](README.md)

## 项目定位

LeanPhy 使用 Lean 的原生语法、类型系统、代码精化器（elaborator）、证明自动化（tactic）、
Lake 构建和 CI 工作流。物理专用模块提供可复用的对象、定理、记法、自动化工具和研究
账本，但不另造一套与 Lean 并行的证明逻辑。已有 Lean 项目可以按领域逐步引入这些模块，
也可以继续直接使用普通 Lean 和 mathlib 定理。

v1 重点覆盖有限维、有限截断和有界对象。连续分析接口可以表达积分、算子、谱和收敛
条件，但结论只有在相应假设或证明项存在时才会被接受。当前回归基线包括 204 个 Lean
源文件、448 个 smoke 检查项、131 条负向 elaboration（代码精化）测试，以及覆盖 13 个
领域包的研究账本（28 条经 Lean kernel 检查的结论、14 条开放义务）。这些数字表示库和
回归测试的规模，不表示已经形式化了同等数量的完整物理论文。

## 能力范围与边界

| 领域 | v1 已提供 | 仍需显式假设或外部工作 |
| --- | --- | --- |
| 量子力学与量子信息 | Pauli/Dirac 记法、密度矩阵、POVM、CPTP/Kraus、Bell/CHSH、有限 Lindblad、振子与 CCR 代数 | 以有限矩阵和显式代数假设为主；无界算子定义域与测量解释仍需前提 |
| 场论与高能物理 | 有限 Fock/CAR/CCR/Wick 恒等式、Clifford/gamma 矩阵、自旋量、迹、Ward 风格代数步骤；有限 EFT 展开、截断误差和系数匹配预算 | 不自动推出场的存在性、无穷维极限、UV 完备性、重整化或非微扰结论 |
| 凝聚态与统计物理 | 格点、Hubbard、BdG、Berry、Jordan–Wigner、有限 Gibbs/Markov 核和转移矩阵 | 热力学极限、相变和实验参数标定是独立义务 |
| 规范、经典、相对论、光学与流体 | 离散 Maxwell/Yang–Mills、外微分与 plaquette 恒等式、辛和 Lorentz 代数、ABCD/Jones 光学、有限体积守恒和离散涡量 | 连续场方程的正则性、全局存在性、边界物理和湍流闭合不会由有限模型自动产生 |
| 数学与数值桥接 | Bochner 积分、支配收敛、Lax–Milgram、Banach 不动点、有界 Hilbert 算子、谱演算、谱隙、算子收敛、残差/能量预算、有限路径积分和逐 regulator 证书 | 数值/CAS 输出必须经过 Lean 侧的 CertificateChecker；数据和 JSON 本身不是证明 |

以下主题在 v1 中仍属于开放或条件性接口：一般无界 Hamiltonian 的自伴性、
Stone 定理、一般谱测度、无穷维路径测度、Osterwalder–Schrader 重构、完整重整化
极限、Navier–Stokes 正则性和非微扰 QFT 存在性。详见
[VERIFIED.md](VERIFIED.md) 和 [docs/verified-scope.md](docs/verified-scope.md)。

## 快速开始

安装与仓库工具链一致的 Lean 4.34.0 后，在仓库根目录运行：

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

完整发布门禁还会运行公共入口、下游客户端、研究账本、声明审计、脚手架和负向
elaboration 测试：

```bash
./scripts/verify.sh
```

首次构建建议使用本地 ext4 或 overlay 文件系统。mathlib 导入和缓存访问在 FUSE 或
网络挂载上可能明显变慢。

## 一个最小的已验证推导

下面使用普通 Lean 语法，把 CCR 假设交给已经通过 kernel 检查的对易子定理。变量
`adag` 表示产生算符 `a†`：

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
```

对于有限 EFT，截断接口把层级和误差写进定理参数：

```lean
import LeanPhy.Entry.HighEnergy
open LeanPhy.HighEnergy
open LeanPhy.Mathematics

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : ExpansionParameter) (T : FiniteEFT ι) (S : Finset ι) (cutoff : ℕ)
    (horder : ∀ i ∈ Finset.univ \ S, cutoff ≤ T.order i) :
    ErrorCertificate (T.amplitude E) (T.retainedAmplitude E S)
      (((Finset.univ \ S).card : ℝ) * T.coefficientBound * E.value ^ cutoff) := by
  exact T.truncation_error_certificate E S cutoff horder
```

这里的结论只针对给定的有限系数表、展开参数、截断集合和阶数假设；它不声称存在
连续 EFT、UV 完备理论或与 regulator 无关的匹配极限。

公共入口包括 LeanPhy.Minimal、按领域选择的 LeanPhy.Entry.* profile，以及组合
多个领域时使用的 LeanPhy.Entry.Physics。工作流模块 LeanPhy/Workflow.lean 记录命名
假设、模型、带证明的结论、依赖、证书和开放义务。

## 研究工作流

1. 选择最小的 `LeanPhy.Entry.*` 入口，减少无关依赖和编译时间。
2. 把数学前提、物理约定、边界条件、截断范围和近似参数写成类型、结构字段或定理参数。
3. 使用可复用定理和 tactic 完成代数步骤。若使用 CAS 或数值程序，必须通过带有
   `CertificateChecker.sound` 定理的接口导入结果。
4. 将结果登记为 `TheoryPackage` 或 `ResearchProject` 中的 checked claim（带证明的结论），
   并把尚未完成的分析、物理解释和连续极限写入 open obligation（开放义务）。
5. 运行 `leanphy_check` 和 `scripts/verify.sh`，同时检查人类可读报告与 JSON 报告。

信任边界可以概括为：

```text
显式假设 + Lean 证明项  ── Lean kernel ──>  条件性已验证结论
```

运行时布尔值、未检查的 JSON、未经证书化的数值输出和隐含的连续极限都不会直接
获得定理地位。报告中的 `VERIFIED-CONDITIONAL` 表示账本中的证明项已经编译并通过
kernel 检查，同时仍有明确列出的开放义务。

## 仓库结构

```text
LeanPhy/                 按物理领域组织的库源码
  Mathematics/            分析、算子、谱、极限和证书
  Quantum/ QuantumInfo/   量子力学与量子信息
  FieldTheory/            CCR/CAR/Fock/Wick 代数
  HighEnergy/             Clifford、gamma、自旋量和有限 EFT
  GaugeTheory/            规范场与离散几何代数
  Condensed/ StatMech/     凝聚态和统计模型
  Classical/ Relativity/  经典力学与相对论结构
  Surface/                Dirac、Einstein、指标和量纲记法
  Entry/                  按领域选择的公共入口
  Examples/               工作流和研究项目示例
Main.lean                内核回归入口
Prototype.lean           端到端闭环原型
Check.lean               研究账本 CLI
scripts/                 发布验证和负向测试
docs/                    架构、路线图和详细范围
.github/                 CI、Issue 模板和 PR 模板
```

## 报告、开发和引用

`leanphy_check` 支持人类可读和机器可读的账本：

```bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
```

默认报告保留开放义务并标记为 `VERIFIED-CONDITIONAL`；`--strict` 用于在仍有开放义务
时让 CI 失败。新增模块应提供可复用定理、明确假设、正向 smoke、必要的负向测试和
文档，具体要求见 [CONTRIBUTING.md](CONTRIBUTING.md)、[docs/architecture.md](docs/architecture.md)
和 [docs/roadmap.md](docs/roadmap.md)。

版本为 1.0.0，Lean 和 mathlib 版本固定在 lean-toolchain 和 lakefile.toml。研究引用
时请同时记录提交号、工具链、mathlib 修订、入口 profile 和生成的账本 JSON；引用格式
见 CITATION.cff。项目采用 Apache License 2.0。
