# LeanPhy v1

LeanPhy 是一个面向理论物理的 Lean 4 / mathlib 形式化验证库。它复用 Lean 的语言、类型系统、编辑器、定理库、tactic、Lake 构建和 CI；在此基础上提供物理对象、记法、可复用定理、领域入口和研究账本。

LeanPhy 的目标是让理论物理推导成为**可编译、可复现、可审计**的 Lean 项目。它是 Lean 的物理领域扩展，不另造一套与 Lean 并行的证明逻辑或运行时模型。

## 验证边界

LeanPhy 验证的是**条件性正确性**：在明确写出的假设下，结论是否由这些假设推出。LeanPhy 不会因为模型声称描述真实世界，就把这一点变成定理；也不会自动证明连续极限、热力学极限或路径积分存在，更不会替研究者决定物理解释是否成立。

只有写成 Lean 命题并提交通过 Lean kernel 检查的证明项，或通过具有 `sound` 证明的外部证书接口导入的结果，才进入已验证层。未完成的分析论证、数值可靠性论证和物理前提会保留在开放义务账本中。换句话说：

```text
显式假设 + Lean 证明项  ── Lean kernel ──>  条件性已验证结论
```

运行时布尔值、未检查的 JSON、未经证书化的 CAS/数值输出和隐含的极限，都不会自动获得定理地位。

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

English documentation: [README.md](README.md)

## 当前版本能做什么

v1 重点覆盖有限维、有限截断和有界对象；对无界算子、连续分析和数值桥接提供带显式假设的接口。当前回归基线为 **205 个 Lean 源文件、457 个 smoke 检查项、137 条负向 elaboration 测试**；研究账本包含 13 个领域包、28 条带 kernel 证明的结论和 14 条开放义务。这些数字反映库与回归测试的规模，不等同于已经形式化的论文数量。

| 领域 | 已提供的基础 | 明确的边界 |
| --- | --- | --- |
| 量子力学与量子信息 | Pauli/Dirac 记法、有限维态与密度矩阵、POVM、CPTP/Kraus、Bell/CHSH、有限 Lindblad、振子和 CCR 代数 | 结果主要针对有限矩阵、有界对象和显式代数假设；无界定义域、自伴性和测量解释仍需单独证明或登记为义务 |
| 场论与高能代数 | 有限 Fock/CAR/CCR/Wick 恒等式、Clifford/gamma 矩阵、自旋量、迹、Ward 风格代数步骤、有限 EFT 展开和截断误差证书 | 不自动推出场的存在性、无穷维极限、UV 完备性、重整化极限或非微扰结论 |
| 凝聚态与统计物理 | 格点、Hubbard、BdG、Berry、Jordan–Wigner、有限 Gibbs/Markov 核和转移矩阵 | 热力学极限、相变和实验参数标定仍是独立义务 |
| 规范、经典、相对论、光学与流体 | 离散 Maxwell/Yang–Mills、外微分与 plaquette 恒等式、辛和 Lorentz 代数、ABCD/Jones 光学、有限体积守恒和离散涡量 | 连续正则性、全局存在性、边界物理和湍流闭合不会由有限模型自动产生 |
| 数学与数值桥接 | Bochner 积分、支配收敛、Lax–Milgram、Banach 不动点、有界 Hilbert 算子、谱演算、谱隙、算子收敛、残差/能量预算、有限路径积分和逐 regulator 证书 | 外部程序只能提交可追溯数据；只有 Lean 侧 `CertificateChecker` 的 soundness 证明能把结果提升为定理 |

无界算子层通过 mathlib 的 `LinearPMap` 保留显式定义域。`DenseDomainOperator` 提供形式伴随、闭性/可闭性、自伴证书、图范数相对界和定义域保持的有界算子组合；每一项都要求用户提交相应证明。把一个对象命名为 Hamiltonian 不会自动得到自伴性，也不会自动产生时间演化。Stone 定理、一般自伴扩张、谱测度和从 resolvent 到演化群的桥接仍在开放义务中。

`LeanPhy.Mathematics.SymmetryReduction` 为约束系统提供统一接口：用户声明可接受态、约束、群作用以及保持这些结构的证明，库据此验证有限步约束保持、轨道传输和不变可观测量在物理态商空间上的下降。它不会自动构造规范切片、证明商空间是流形，或把“规范等价”解释成物理等价。

更完整的逐模块清单和限制见 [VERIFIED.md](VERIFIED.md) 与 [docs/verified-scope.md](docs/verified-scope.md)。

## 快速开始

安装与仓库一致的 Lean 4.34.0（项目已在 `lean-toolchain` 固定版本），然后在仓库根目录运行：

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

发布验证脚本会进一步检查公共入口、下游客户端、研究账本、声明审计、脚手架和负向测试：

```bash
./scripts/verify.sh
```

首次构建建议使用本地 ext4 或 overlay 文件系统；在 FUSE 或网络挂载上，mathlib 导入和缓存访问可能明显变慢。

## 最小示例：带 CCR 假设的对易子推导

下面是普通 Lean 代码。`hCCR` 是明确给出的 CCR 假设，结论由已编译并通过 kernel 检查的定理得到：

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
```

有限 EFT 接口把截断层级和误差预算放进定理参数；有限路径积分接口同样要求显式的归一化证书。缺少这些假设时，代码会在 elaboration 阶段失败，而不是生成一个无条件结论。

## 推荐的研究工作流

1. 选择最小的 `LeanPhy.Entry.*` 入口，减少无关依赖和编译时间。
2. 把数学前提、物理约定、边界条件、截断范围和近似参数写成类型、结构字段或定理参数。
3. 用可复用定理和 tactic 完成代数步骤。若使用 CAS 或数值程序，通过带有 `CertificateChecker.sound` 定理的接口导入结果。
4. 将结果登记为 `TheoryPackage` 或 `ResearchProject` 中的 checked claim；把尚未完成的分析、物理解释和连续极限写入 open obligation。
5. 运行 `leanphy_check` 和 `scripts/verify.sh`，同时检查人类可读报告与 JSON 报告。

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

常用入口包括 `LeanPhy.Minimal`、各领域的 `LeanPhy.Entry.*` 以及组合多领域时使用的 `LeanPhy.Entry.Physics`。

## 报告、开发与引用

```bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
```

新增模块应提供可复用定理、明确假设、正向 smoke、必要的负向测试和文档。开发规范见 [CONTRIBUTING.md](CONTRIBUTING.md)、[docs/architecture.md](docs/architecture.md) 和 [docs/roadmap.md](docs/roadmap.md)。

版本为 1.0.0，Lean 与 mathlib 版本固定在 `lean-toolchain` 和 `lakefile.toml`。引用 LeanPhy 时请记录提交号、工具链、mathlib 修订、入口 profile 和生成的账本 JSON；引用信息见 [CITATION.cff](CITATION.cff)。项目采用 Apache License 2.0。
