# LeanPhy v1.0

LeanPhy 是一个建立在 Lean 4 与 mathlib 之上的理论物理形式化库。它沿用 Lean 的语言、类型系统、编辑器支持、定理库、tactic、Lake 构建和 CI 工作流，并补充物理记号、领域对象、可复用定理以及研究账本。LeanPhy 与普通 Lean 项目使用同一个逻辑和 kernel，不另设一套证明系统。

项目的目标是让理论物理推导成为**可编译、可复现、可审计**的 Lean 文件。它适合把符号推导、有限模型和带明确假设的数学步骤交给 kernel 检查；它不会把尚未证明的物理或分析前提隐藏起来。

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

英文说明：[README.md](README.md)

## 先明确验证边界

LeanPhy 验证的是**条件性正确性**：在明确列出的假设成立时，结论是否由这些假设推出。一个通过检查的定理应理解为“若这些数学前提、物理约定和证书成立，则该结论成立”。

LeanPhy 不自动判断：

- 模型是否真实地描述了自然界；
- 连续极限、热力学极限或路径积分是否存在；
- 无界算子操作是否满足定义域和自伴性条件；
- 某个数学对象是否具有预期的物理解释。

这些问题必须作为显式命题、结构字段、外部证书，或研究账本中的开放义务出现。每条已验证结论都由 Lean kernel 检查证明项；外部程序或 CAS 的结果只有在 Lean 侧提供 `CertificateChecker.sound` 证明后，才能进入已验证层。未经检查的运行时布尔值、JSON、数值输出、极限或近似不会自动获得定理地位。

```text
显式假设与证书  ── Lean 证明项 ──>  Lean kernel  ──>  条件性已验证结论
```

## 当前状态与适用范围

版本 1.0.0 以有限维、有限截断和有界对象为主要工作范围；对无界算子、连续分析、数值计算和外部程序，库提供的是需要用户提交证明或证书的接口。当前回归基线包含 **209 个 Lean 源文件、473 项 smoke 检查和 141 条预期失败的 elaboration 测试**。研究账本包含 13 个领域包、28 条通过 kernel 检查的结论和 14 条开放义务。这些数字描述库和回归测试的覆盖面，不等同于已经形式化的完整物理论文数量。

| 领域 | 已提供的基础 | 仍需单独证明或登记的边界 |
| --- | --- | --- |
| 量子力学与量子信息 | Pauli 与 Dirac 记法、有限维量子态和密度矩阵、POVM、CPTP/Kraus 通道、Bell/CHSH、有限 Lindblad 模型、振子与 CCR 代数 | 无界算子定义域、自伴性、连续测量语义，以及有限模型与具体物理系统之间的对应关系 |
| 场论与高能代数 | 有限 Fock 空间、CAR/CCR 与 Wick 恒等式、Clifford/gamma 矩阵、自旋量、迹、Ward 型代数步骤、有限 EFT 展开和截断证书；非分次与分次 BRST 代数接口 | 场的存在性、无穷维极限、UV 完备性、重整化极限、具体 ghost 代数、BV 结构、异常消除和非微扰结论 |
| 经典、规范、相对论、光学与流体 | Poisson 代数、第一类约束理想、约束保持映射、弱等式、Dirac 可观测量、离散 Maxwell/Yang–Mills、外微分与 plaquette 恒等式、辛与 Lorentz 代数、ABCD/Jones 光学、有限体积守恒和离散涡量 | 规范固定、约化空间正则性、连续正则性、全局存在性、边界物理和湍流闭合 |
| 凝聚态与统计物理 | 格点、Hubbard、BdG、Berry、Jordan–Wigner、有限 Gibbs/Markov 核和转移矩阵 | 热力学极限、相变、实验参数标定，以及与连续理论的等价性 |
| 数学分析与数值桥接 | Bochner 积分、支配收敛、Lax–Milgram、Banach 不动点、有界 Hilbert 算子、谱演算、谱隙、算子收敛、残差/能量预算、有限路径积分和逐 regulator 证书 | 外部程序只提供可追溯数据；必须有 Lean 侧 `CertificateChecker.sound` 证明，结果才能进入已验证层 |

无界算子层使用 mathlib 的 `LinearPMap`，并在类型中保留定义域。`DenseDomainOperator` 提供形式伴随、闭性/可闭性、自伴性、图范数相对界和定义域保持的有界复合等接口；每个接口都要求用户提供相应证明。把一个对象命名为 `Hamiltonian` 不会自动证明它自伴，也不会自动生成时间演化。Stone 定理、自伴扩张、谱测度以及从 resolvent 到演化群的桥接仍属于开放义务。

`LeanPhy.Mathematics.SymmetryReduction` 处理受约束系统中的可接受态、群作用、轨道传输和不变可观测量。`ConstraintAlgebra` 和 `ConstraintMap` 处理约束生成理想、第一类闭合、弱等式、Dirac 可观测量以及保持约束理想的 Poisson 映射。它们不自动构造规范切片，不证明商空间是流形，也不把规范等价解释成物理等价。

`LeanPhy.Mathematics.BRST` 提供非分次的代数前置层：用户必须给出导子和幂零证明，库再定义闭元、恰元、同调关系及其基本传输定理。`LeanPhy.Mathematics.GradedBRST` 进一步提供齐次子空间、显式声明的奇次数移位和带 Koszul 符号的 Leibniz 规则，并在此基础上提供分次同调接口。两个模块都不构造具体 ghost 代数、BV 反括号、规范固定、路径积分测度、异常消除或物理等价定理；这些内容必须在后续模型中显式给出，或登记为开放义务。

逐模块的已验证内容和限制见 [VERIFIED.md](VERIFIED.md) 与 [docs/verified-scope.md](docs/verified-scope.md)。

## 快速开始

项目在 [`lean-toolchain`](lean-toolchain) 中固定 Lean 4.34.0。安装对应版本后，在仓库根目录运行：

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

发布验证脚本会进一步检查公共入口、下游客户端、研究账本、声明审计、项目脚手架和负向测试：

```bash
./scripts/verify.sh
```

首次构建建议使用本地 ext4 或 overlay 文件系统。mathlib 导入和缓存访问在 FUSE 或网络挂载上可能明显变慢。

## 最小示例：从 CCR 假设推出对易子结论

下面是普通 Lean 代码。`hCCR` 是显式给出的 CCR 假设；结论来自已经编译并通过 kernel 检查的定理：

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
```

有限 EFT 接口把截断阶数、系数界和误差预算写入定理参数；有限路径积分接口要求显式的归一化证书。缺少必要前提时，代码会在 elaboration 阶段失败，而不是产生无条件结论。

## 建议的研究工作流

1. 选择最小的 `LeanPhy.Entry.*` 入口，减少无关依赖和编译时间。
2. 将数学前提、物理约定、边界条件、截断范围和近似参数写成类型、结构字段或定理参数。
3. 用可复用定理和 tactic 完成代数步骤。若使用 CAS 或数值程序，通过带 `CertificateChecker.sound` 定理的接口导入结果。
4. 将结果登记为 `TheoryPackage` 或 `ResearchProject` 中的 `checked claim`；把尚未完成的分析、物理解释和连续极限写入 `open obligation`。
5. 运行 `leanphy_check` 和 `scripts/verify.sh`，同时检查人类可读报告与 JSON 报告。

账本中的 `VERIFIED-CONDITIONAL` 表示证明项已经编译并通过 kernel 检查，同时仍可能存在明确列出的开放义务。

## 仓库结构

```text
LeanPhy/                 按物理领域组织的库源码
  Mathematics/            分析、算子、谱、极限、证书与通用模型
  Quantum/ QuantumInfo/   量子力学与量子信息
  FieldTheory/            CCR/CAR/Fock/Wick 代数
  HighEnergy/             Clifford、gamma、自旋量和有限 EFT
  GaugeTheory/            规范场与离散几何代数
  Condensed/ StatMech/    凝聚态与统计模型
  Classical/ Relativity/  经典力学与相对论结构
  Surface/                Dirac、Einstein、指标和量纲记法
  Entry/                  按领域选择的公共入口
  Examples/               工作流和研究项目示例
Main.lean                kernel 回归入口
Prototype.lean           端到端闭环原型
Check.lean               研究账本 CLI
scripts/                 发布验证和负向测试
docs/                    架构、路线图和详细范围
```

常用入口包括 `LeanPhy.Minimal`、各领域的 `LeanPhy.Entry.*`，以及组合多个领域时使用的 `LeanPhy.Entry.Physics`。

## 报告、开发与引用

```bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
```

新增模块应提供可复用定理、明确假设、正向 smoke 回归、必要的负向回归和文档。开发规范见 [CONTRIBUTING.md](CONTRIBUTING.md)、[docs/architecture.md](docs/architecture.md) 和 [docs/roadmap.md](docs/roadmap.md)。

版本号为 1.0.0；Lean 和 mathlib 版本固定在 [`lean-toolchain`](lean-toolchain) 与 [`lakefile.toml`](lakefile.toml) 中。引用 LeanPhy 时请记录提交号、工具链、mathlib 修订、入口 profile 和生成的账本 JSON；引用信息见 [CITATION.cff](CITATION.cff)。项目采用 Apache License 2.0。
