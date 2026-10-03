# LeanPhy v1

LeanPhy 是一个基于 Lean 4 和 mathlib 的理论物理形式化验证库。它把物理推导
表达为带有明确假设的 Lean 命题，并由 Lean kernel 检查最终证明项。

LeanPhy 关心的问题是：**在给定假设下，结论是否确实可以从这些假设推出？**
这是一种对推导有效性的条件性验证。模型是否足以描述自然界、连续或热力学极限
是否存在、路径积分是否有严格定义，以及物理解释是否正确，属于另外的研究问题；
它们必须作为显式假设、证明义务或开放义务记录，不能因为写进了模型描述就自动成为
已证明定理。

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml/badge.svg)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

English documentation: [README.md](README.md)

## 项目定位

LeanPhy v1 沿用 Lean 的原生语法、类型系统、elaborator、tactic、Lake 构建和 CI
工作流。它提供物理领域的类型、定理、证明 tactic、表面记号和研究账本，方便物理学
家逐步把现有推导接入 Lean；项目本身不引入一套与 Lean 并行的证明逻辑。

v1 主要面向有限维、有限截断和有界对象。对于分析性或连续性的内容，库提供可组合
的接口，但要求使用者明确提供连续性、可积性、定义域、稳定性或收敛性证明。当前验收
基线包括 203 个 Lean 源文件、446 项内核回归能力、130 条负向 elaboration 测试，
以及覆盖 13 个领域包的研究账本（26 条已检查结论、13 条开放义务）。这些数字用于
描述库的覆盖和回归测试规模，不代表已经形式化了同等数量的完整物理论文。

## 能力范围

| 领域 | v1 已提供的内容 | 适用边界 |
| --- | --- | --- |
| 量子力学与量子信息 | Pauli/Dirac 记号、密度矩阵、POVM、CPTP/Kraus、Bell/CHSH、有限 Lindblad 模型、振子与 CCR | 以有限维、有限矩阵和显式代数假设为主 |
| 场论与高能代数 | 有限 Fock/CAR/CCR/Wick 恒等式、Clifford 与 gamma 矩阵、自旋量、迹、Ward 风格的代数步骤 | 场的存在性、无穷维极限和非微扰结论仍需单独证明 |
| 凝聚态与统计物理 | 格点、Hubbard、BdG、Berry、Jordan–Wigner、有限 Gibbs/Markov 核和转移矩阵 | 热力学极限和相变极限以显式义务表示 |
| 规范、经典、相对论、光学与流体 | 离散 Maxwell/Yang–Mills、外微分与 plaquette 恒等式、辛和 Lorentz 代数、ABCD/Jones 光学、有限体积守恒和离散涡量 | 连续场方程的正则性和全局存在性不由有限模型自动推出 |
| 数学与数值桥接 | Bochner 积分、支配收敛、Lax–Milgram、Banach 不动点、有界 Hilbert 算子、谱演算、谱隙、算子收敛、残差/能量预算、有限路径积分和逐 regulator 证书 | 每个分析结论都需要相应的假设或证明项，数值输出本身不构成证明 |

以下主题在 v1 中仍属于开放或条件性接口：一般无界 Hamiltonian 的自伴性、Stone
定理、一般谱测度、无穷维路径测度、Osterwalder–Schrader 重构、完整重整化极限、
Navier–Stokes 正则性和非微扰 QFT 存在性。详细边界见
[VERIFIED.md](VERIFIED.md) 与 [docs/verified-scope.md](docs/verified-scope.md)。

## 快速开始

安装 Lean 4.34.0 后，在仓库根目录运行：

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

完整发布门禁会额外运行声明审计、研究包账本、下游客户端、脚手架生成和负向
elaboration 测试：

```bash
./scripts/verify.sh
```

首次构建建议使用本地 ext4 或 overlay 文件系统。mathlib 的导入和缓存访问在 FUSE
或网络挂载上可能明显变慢。

## 一个最小的已验证推导

LeanPhy 使用普通 Lean 声明和 tactic。下面的例子把 CCR 假设交给一个已检查的对易子
定理；代码中的 `adag` 表示产生算符 `a†`：

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
```

公共入口包括 `LeanPhy.Minimal`、按领域选择的 `LeanPhy.Entry.*` profile，以及组合多
个领域时使用的 `LeanPhy.Entry.Physics`。`LeanPhy/Workflow.lean` 中的工作流记录命名
假设、模型、带证明的结论、依赖、证书和开放义务。`physics`、`physics_search`、
Dirac 记号、Einstein 求和、指标方差和量纲检查通过相应模块接入原生 Lean 工作流。

## 研究工作流

建议按以下顺序把一段推导加入项目：

1. 选择最小的 `LeanPhy.Entry.*` 入口，避免无关模块增加编译负担。
2. 把数学前提、物理约定、边界条件和近似范围写成类型、结构字段或定理参数。
3. 用已有定理和 tactic 证明代数步骤；需要外部 CAS 或数值计算时，导入带有
   `CertificateChecker.sound` 证明的证书。
4. 将结果登记为 `TheoryPackage` 或 `ResearchProject` 中的 checked claim，并列出
   依赖和仍未解决的 open obligation。
5. 运行 `leanphy_check` 和 `scripts/verify.sh`，同时检查人类可读报告与 JSON 报告。

LeanPhy 的信任边界可以概括为：

```text
显式假设 + Lean 证明项  ── Lean kernel ──>  已验证结论
```

运行时布尔值、未检查的 JSON、未经证书化的数值结果和隐含的连续极限都不会直接
获得定理地位。

## 仓库结构

```text
LeanPhy/                 按物理领域组织的库源码
  Mathematics/            分析、算子、谱、极限和证书
  Quantum/ QuantumInfo/   量子力学与量子信息
  FieldTheory/            CCR/CAR/Fock/Wick 代数
  HighEnergy/ GaugeTheory/ 高能与规范场论代数
  Condensed/ StatMech/     凝聚态和统计模型
  Classical/ Relativity/  经典力学与相对论结构
  Surface/                Dirac、Einstein、指标和量纲记号
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

默认报告保留开放义务并标记为 `VERIFIED-CONDITIONAL`；`--strict` 用于在仍有开放
义务时让 CI 失败。新增模块应提供可复用定理、明确假设、正向 smoke、必要的负向
测试和文档，具体要求见 [CONTRIBUTING.md](CONTRIBUTING.md)、
[docs/architecture.md](docs/architecture.md) 和 [docs/roadmap.md](docs/roadmap.md)。

版本为 `1.0.0`，Lean 和 mathlib 版本分别固定在
[lean-toolchain](lean-toolchain) 和 [lakefile.toml](lakefile.toml)。研究引用时请
同时记录提交号、工具链、mathlib 修订、入口 profile 和生成的账本 JSON；引用格式见
[CITATION.cff](CITATION.cff)。项目采用 [Apache License 2.0](LICENSE)。
