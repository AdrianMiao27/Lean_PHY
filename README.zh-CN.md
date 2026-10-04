# LeanPhy v1

LeanPhy 是建立在 Lean 4 与 mathlib 之上的理论物理形式化库。它沿用 Lean 的语法、类型系统、编辑器、定理库、tactic、Lake 构建和 CI，并在此基础上提供物理对象、记法、可复用定理、按领域组织的入口模块和研究账本。

项目的目标是把理论物理推导写成**可编译、可复现、可审计**的 Lean 文件。LeanPhy 是 Lean 的物理领域扩展，与现有 Lean 项目使用同一套语言和内核，不另设一套证明逻辑。

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

English documentation: [README.md](README.md)

## 验证边界

LeanPhy 验证的是**条件性正确性**：在明确写出的假设下，结论是否确实由这些假设推出。LeanPhy 不判断模型是否描述真实世界，也不自动判断连续极限、路径积分是否存在，或物理解释是否成立；这些前提不会被悄悄提升为定理。它检查推导的逻辑有效性，把模型的物理适用性留给研究者和相应的实验、数学论证。

每条已验证结论都必须是 Lean kernel 检查过的证明项，或由带有 Lean 侧 `sound` 定理的外部证书接口导入。尚未完成的分析论证、数值可靠性论证和物理前提会保留在开放义务账本中。

```text
显式假设 + Lean 证明项  ── Lean kernel ──>  条件性已验证结论
```

运行时布尔值、未经检查的 JSON、没有证书的 CAS/数值输出，以及未在命题中明确陈述的极限或近似，都不会自动获得定理地位。

## 当前版本的范围

v1.0.0 主要面向有限维、有限截断和有界对象；对于无界算子、连续分析、数值计算和外部程序，库提供了要求用户提交证明或证书的接口。当前回归基线包含 **208 个 Lean 源文件、469 项 smoke 回归检查和 140 条负向 elaboration 回归**；研究账本包含 13 个领域包、28 条通过 kernel 检查的结论和 14 条开放义务。这些数字描述库和回归测试的规模，不代表已经形式化了多少篇完整论文。

| 领域 | 已提供的基础 | 需要单独证明或登记的边界 |
| --- | --- | --- |
| 量子力学与量子信息 | Pauli/Dirac 记法、有限维态与密度矩阵、POVM、CPTP/Kraus 通道、Bell/CHSH、有限 Lindblad 模型、振子和 CCR 代数 | 无界算子定义域、自伴性、连续测量解释以及从有限模型到物理系统的对应关系 |
| 场论与高能代数 | 有限 Fock、CAR/CCR、Wick 恒等式、Clifford/gamma 矩阵、自旋量、迹、Ward 风格代数步骤、有限 EFT 展开和截断误差证书；BRST 的非分次代数前置层 | 场的存在性、无穷维极限、UV 完备性、重整化极限、ghost 分次、Koszul 符号、BV 结构、异常消除和非微扰结论 |
| 经典、规范、相对论、光学与流体 | Poisson 代数、第一类约束理想、约束保持映射、弱等式、Dirac 可观测量、离散 Maxwell/Yang–Mills、外微分与 plaquette 恒等式、辛和 Lorentz 代数、ABCD/Jones 光学、有限体积守恒和离散涡量 | 规范固定、约化空间的正则性、连续正则性、全局存在性、边界物理和湍流闭合 |
| 凝聚态与统计物理 | 格点、Hubbard、BdG、Berry、Jordan–Wigner、有限 Gibbs/Markov 核和转移矩阵 | 热力学极限、相变、实验参数标定及其与连续理论的等价性 |
| 数学与数值桥接 | Bochner 积分、支配收敛、Lax–Milgram、Banach 不动点、有界 Hilbert 算子、谱演算、谱隙、算子收敛、残差/能量预算、有限路径积分和逐 regulator 证书 | 外部程序只能提供可追溯数据；必须有 Lean 侧 `CertificateChecker` 的 `sound` 证明，结果才可进入已验证层 |

无界算子层使用 mathlib 的 `LinearPMap`，并在类型中保留声明的定义域。`DenseDomainOperator` 提供形式伴随、闭性/可闭性、自伴证书、图范数相对界和定义域保持的有界组合；这些接口都要求用户提交相应证明。把对象命名为 Hamiltonian 不会自动得到自伴性，也不会自动产生时间演化。Stone 定理、一般自伴扩张、谱测度以及从 resolvent 到演化群的桥接仍是开放义务。

`LeanPhy.Mathematics.SymmetryReduction` 处理受约束系统中的可接受态、群作用、轨道传输和不变可观测量。`LeanPhy.Mathematics.ConstraintAlgebra` 进一步处理交换 Poisson 代数中的约束生成理想、第一类闭合、弱等式和 Dirac 可观测量的代数闭合；`ConstraintMap` 则要求映射保持 Poisson 括号并把源约束理想映入目标约束理想，从而传输弱等式。传输 Dirac 可观测量还必须显式提供目标约束理想的覆盖证明。上述模块都不自动构造规范切片、证明商空间是流形，或把规范等价解释成物理等价。

`LeanPhy.Mathematics.BRST` 在上述约束代数之上提供一个有界范围的 BRST 前置层：`BRSTDifferential` 要求用户给出显式的导子和幂零证明，并据此定义闭元、恰当元、同调等价及其基本传输定理。`PoissonBRSTDifferential` 和 `ConstraintBRSTDifferential` 进一步要求 Poisson 兼容性和约束理想保持，从而可以检查闭观测量的括号闭合以及弱等式的传输。这是一个**未引入 ghost 分次的代数种子**，不声称已经形式化完整 BRST/BV、规范固定费米子、路径积分测度、异常消除、规范等价或物理等价；这些内容仍须作为后续结构或开放义务明确给出。

完整的逐模块清单和限制见 [VERIFIED.md](VERIFIED.md) 与 [docs/verified-scope.md](docs/verified-scope.md)。

## 快速开始

项目在 [`lean-toolchain`](lean-toolchain) 中固定了 Lean 4.34.0。安装对应版本后，在仓库根目录运行：

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

发布验证脚本还会检查公共入口、下游客户端、研究账本、声明审计、项目脚手架和负向测试：

```bash
./scripts/verify.sh
```

首次构建建议使用本地 ext4 或 overlay 文件系统。mathlib 的导入和缓存访问在 FUSE 或网络挂载上可能明显变慢。

## 最小示例：从 CCR 假设得到对易子结论

下面是普通 Lean 代码。`hCCR` 是显式给出的 CCR 假设，结论来自已经编译并通过 kernel 检查的定理：

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
```

有限 EFT 接口把截断阶数、系数界和误差预算写入定理参数；有限路径积分接口要求显式的归一化证书。缺少必要前提时，代码会在 elaboration 阶段失败，而不是产生一个无条件结论。

## 推荐的研究工作流

1. 选择最小的 `LeanPhy.Entry.*` 入口，减少无关依赖和编译时间。
2. 把数学前提、物理约定、边界条件、截断范围和近似参数写成类型、结构字段或定理参数。
3. 使用可复用定理和 tactic 完成代数步骤。若使用 CAS 或数值程序，通过带有 `CertificateChecker.sound` 定理的接口导入结果。
4. 将结果登记为 `TheoryPackage` 或 `ResearchProject` 中的 `checked claim`；把尚未完成的分析、物理解释和连续极限写入 `open obligation`。
5. 运行 `leanphy_check` 和 `scripts/verify.sh`，并同时检查人类可读报告与 JSON 报告。

账本中的 `VERIFIED-CONDITIONAL` 表示相关证明项已经编译并通过 kernel 检查，同时仍可能存在明确列出的开放义务。

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
