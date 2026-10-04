# LeanPhy

LeanPhy 是一个建立在 **Lean 4 与 mathlib** 之上的理论物理形式化库。它不是
Lean 的 fork，也不是另一套证明逻辑：研究者仍然使用 Lean 的语法、类型检查器、
编辑器支持、定理库、tactic、Lake 构建和 CI 工作流；LeanPhy 只增加物理对象、
记号、可复用定理以及记录研究边界的账本。

> **定位**：把理论物理推导中可以形式化的数学步骤编译为 Lean 证明，并把尚未
> 解决的分析问题和物理前提明确登记为开放义务。

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

English version: [README.md](README.md)

## 先明确验证边界

LeanPhy 检查的是**条件性正确性**：在明确列出的数学假设、物理约定和证书成立
时，结论是否由这些前提推出。因而，一个 `checked claim` 应读作：

> 在所列前提下，该结论可以由 Lean 的证明规则推出。

LeanPhy 不会把下列问题自动变成定理：

- 模型是否足以描述真实世界或某个具体实验系统；
- 连续极限、热力学极限或重整化极限是否存在；
- 路径积分是否存在、收敛，或具有所需的物理解释；
- 无界算子的定义域、自伴性和时间演化条件是否满足；
- 一个形式化对象是否确实对应研究者所赋予的物理意义。

这些内容必须以显式命题、结构字段、用户提供的证书，或研究账本中的**开放义务**
出现。每个已检查结论都包含 Lean 证明项，并由 Lean kernel 重新检查。CAS、数值
程序或外部脚本只有在 Lean 侧提供 `CertificateChecker.sound` 之类的正确性定理
后，才能把结果带入已验证层；未经检查的布尔值、JSON、数值输出、极限或近似，
本身不会获得定理地位。

```text
显式假设/证书 ──> Lean 证明项 ──> Lean kernel ──> 条件性已验证结论
                         └── 未完成的分析与物理前提 ──> 开放义务账本
```

## 当前版本与适用范围

LeanPhy v1.0.0 的主要工作范围是有限维、有限截断和有界对象；对无界算子、连续
分析、数值计算和外部程序，项目提供的是带明确输入边界的接口，而不是自动完成的
物理定理。

当前回归基线为 **209 个 Lean 源文件、473 项 smoke 检查和 141 条预期失败的
elaboration 测试**。默认运行 `leanphy_check --project-json` 会报告 **8 个领域
包、15 条已检查结论和 8 条开放义务**；加入 `--broad` 后，报告覆盖 **13 个领域
包、28 条已检查结论和 14 条开放义务**。这些数字表示库和回归测试的覆盖面，
不表示已经形式化了相同数量的完整物理论文。

| 领域 | 已提供的可复用基础 | 仍需显式证明或登记的边界 |
| --- | --- | --- |
| 量子力学与量子信息 | Pauli 与 Dirac 记号、有限态与密度矩阵、POVM、CPTP/Kraus 通道、Bell/CHSH、有限 Lindblad 模型、振子和 CCR 代数 | 无界算子定义域、自伴性、连续测量语义，以及有限模型与具体物理系统的对应关系 |
| 场论与高能代数 | 有限截断 Fock 空间、CAR/CCR 与 Wick 恒等式、Clifford/gamma 矩阵、自旋量、迹、Ward 型代数步骤、有限 EFT 展开和截断证书；非分次与分次 BRST 接口 | 场的存在性、无穷维极限、UV 完备性、重整化极限、具体 ghost 代数、BV 结构、异常消除和非微扰结论 |
| 经典、规范、相对论、光学与流体 | Poisson 代数、第一类约束理想、约束保持映射、弱等式、Dirac 可观测量、离散 Maxwell/Yang–Mills、外微分与 plaquette 恒等式、辛与 Lorentz 代数、ABCD/Jones 光学、有限体积守恒和离散涡量 | 规范固定、约化空间正则性、连续正则性、全局存在性、边界物理和湍流闭合 |
| 凝聚态与统计物理 | 格点、Hubbard、BdG、Berry、Jordan–Wigner、有限 Gibbs/Markov 核和转移矩阵 | 热力学极限、相变、实验参数标定，以及与连续理论的等价性 |
| 数学分析与数值桥接 | Bochner 积分、支配收敛、Lax–Milgram、Banach 不动点、有界 Hilbert 算子、谱演算、谱隙、算子收敛、残差/能量预算、有限路径积分和逐 regulator 证书 | 外部程序只提供可追溯数据；进入已验证层仍需 Lean 侧 `CertificateChecker.sound` 证明 |

无界算子接口使用 mathlib 的 `LinearPMap`，并把定义域保留在类型中。`DenseDomainOperator`
为形式伴随、闭性/可闭性、自伴性、图范数相对界和定义域保持的有界复合提供接口；
每个接口都要求用户提交相应证明。把对象命名为 `Hamiltonian` 不会自动证明它自伴，
也不会自动产生时间演化。Stone 定理、自伴扩张、谱测度以及从 resolvent 到演化群
的桥接，仍是开放义务。

规范系统的 `ConstraintAlgebra` 与 `ConstraintMap` 处理约束生成理想、第一类闭合、
弱等式、Dirac 可观测量以及保持约束理想的 Poisson 映射。`BRST` 提供用户给出导子
和幂零证明后的非分次代数接口；`GradedBRST` 增加齐次子空间、奇次数移位、带
Koszul 符号的 Leibniz 规则和分次同调接口。它们都不声称已经构造完整的 ghost 代数、
BV 反括号、规范固定、路径积分测度、异常消除或“BRST 同调等于物理可观测量”；这些
内容必须在具体模型中补充，或留在开放义务账本中。

详细的逐模块清单和限制见 [VERIFIED.md](VERIFIED.md) 与
[docs/verified-scope.md](docs/verified-scope.md)。

## 快速开始

项目在 [`lean-toolchain`](lean-toolchain) 中固定 Lean 4.34.0。安装对应版本后，
在仓库根目录运行：

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

发布验证脚本还会检查公共入口、下游客户端、研究账本、声明审计、项目脚手架和负向
测试：

```bash
./scripts/verify.sh
```

首次构建建议使用本地 ext4 或 overlay 文件系统。mathlib 导入和缓存访问在 FUSE 或
网络挂载上可能明显变慢。

## 最小示例：从 CCR 假设推出对易子结论

下面是普通的 Lean 代码。`hCCR` 是显式给出的 CCR 假设；结论来自已经编译并通过
kernel 检查的定理：

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
```

这个例子验证的是“由 CCR 假设推出对易子恒等式”。它不证明存在满足 CCR 的无界
Hilbert 空间表示，也不证明该表示就是某个实验系统。有限 EFT 接口同样把截断阶数、
系数界和误差预算写入定理参数；有限路径积分接口要求显式的归一化证书。缺少必要
前提时，代码会在 elaboration 阶段失败，而不是生成无条件结论。

## 推荐的研究工作流

1. 选择最小的 `LeanPhy.Entry.*` 入口，减少无关依赖和编译时间。
2. 将数学前提、物理约定、边界条件、截断范围和近似参数写成类型、结构字段或定理参数。
3. 使用可复用定理和 tactic 完成代数步骤；若使用 CAS 或数值程序，通过带
   `CertificateChecker.sound` 定理的接口导入结果。
4. 将结果登记为 `TheoryPackage` 或 `ResearchProject` 中的 `checked claim`，把尚未
   完成的分析、物理解释和连续极限写入 `open obligation`。
5. 运行 `leanphy_check` 和 `scripts/verify.sh`，同时检查人类可读报告与 JSON 报告。

账本中的 `VERIFIED-CONDITIONAL` 表示证明项已经编译并通过 kernel 检查，同时仍可能
存在明确列出的开放义务。

可信性审计可以单独运行：

```bash
lake env lean scripts/axioms.lean
```

项目源码和验收入口不使用 `sorry`、`admit` 或面向应用的未检查公理。`#print axioms`
可能列出 Lean/mathlib 使用的标准基础公理（例如 `propext`、`Classical.choice` 和
`Quot.sound`）；这与把某个物理结论直接声明为公理不同。

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

常用入口包括 `LeanPhy.Minimal`、各领域的 `LeanPhy.Entry.*`，以及组合多个领域时使用
的 `LeanPhy.Entry.Physics`。

## 报告、开发与引用

```bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
```

新增模块应提供可复用定理、明确假设、正向 smoke 回归、必要的负向回归和文档。开发
规范见 [CONTRIBUTING.md](CONTRIBUTING.md)、[docs/architecture.md](docs/architecture.md)
和 [docs/roadmap.md](docs/roadmap.md)。

版本号为 1.0.0；Lean 和 mathlib 版本固定在 [`lean-toolchain`](lean-toolchain) 与
[`lakefile.toml`](lakefile.toml) 中。引用 LeanPhy 时请记录提交号、工具链、mathlib
修订、入口 profile 和生成的账本 JSON；引用信息见 [CITATION.cff](CITATION.cff)。
项目采用 Apache License 2.0。
