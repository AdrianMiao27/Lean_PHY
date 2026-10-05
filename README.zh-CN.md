# LeanPhy

LeanPhy 是一个建立在 [Lean 4](https://lean-lang.org/) 和
[mathlib](https://github.com/leanprover-community/mathlib4) 之上的理论物理形式化库。
它把推导中可以精确定义的数学步骤写成 Lean 代码，并交由 Lean kernel（内核）检查。
项目沿用 Lean 的语言、编辑器支持、定理库、tactic、Lake 构建和 CI，同时提供物理对象、
记号、可复用的证明证书，以及记录假设和未决工作的研究账本。

LeanPhy 是 Lean 的扩展库，不是 Lean 的分支，也不引入另一套逻辑系统。

> **一句话定位：** 检查“在明确前提下，结论是否由推导步骤推出”，并把尚未证明的分析
> 和建模选择保留在可审计的记录中。

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

English version: [README.md](README.md)

## 验证的是什么

LeanPhy 验证的是**条件性的数学正确性**。每条已检查结论都包含一个 Lean proof term，
并已经通过 Lean kernel 检查。换句话说：

> 在开发中写明的前提成立时，结论可以由 Lean 接受的证明规则推出。

这和判断一个模型在物理上是否真实是两件事。LeanPhy 不会自动把下列问题变成定理：

- 模型是否描述真实世界或某个具体实验；
- 连续极限、热力学极限或重整化极限是否存在、收敛并具有所需性质；
- 路径积分是否存在、是否收敛，或是否具有预期的物理解释；
- 无界算子的定义域、自伴性和时间演化条件是否成立；
- 一个形式对象是否确实具有研究者赋予它的物理含义。

这些内容必须以命题、结构字段、定理参数或正确性证书明确写入。尚未完成的分析证明、
数值认证、建模前提和物理解释，会登记在**开放义务账本（open-obligation ledger）**
中。账本是审计记录，不能替代证明。

外部 CAS、数值程序或脚本可以提供数据，但数据只有经过 Lean 侧的正确性定理（例如
<code>CertificateChecker.sound</code>）才能进入已验证层。一个未经检查的布尔值、JSON、
采样极限或数值近似，不会因为来自另一个程序就自动成为定理。

仓库使用以下三种状态标签：

| 状态 | 含义 |
| --- | --- |
| <code>kernel-checked claim</code> | 证明项已通过 Lean kernel；结论对其中明确列出的前提成立。 |
| <code>declared premise</code> | 推导使用的假设、约定或外部证书；它是否适用于目标物理系统，需要另行论证。 |
| <code>open obligation</code> | 尚未完成的分析、数值认证、连续极限或物理解释工作。 |

~~~text
显式前提/证书 -> Lean proof term -> Lean kernel -> 条件性已验证结论
                                      \
                                       -> 未完成工作 -> 开放义务账本
~~~

## v1.0 的范围

LeanPhy v1.0.0 以有限维、有限截断和有界构造为主要验证对象，同时提供无界算子、连续
分析、近似、数值证书和外部数据的接口。这些接口的作用是让缺少的前提可被准确记录；
它们不会替用户证明尚未完成的数学或物理结论。

当前验收基线包含 **211 个 Lean 源文件、478 项通过 kernel 检查的 smoke 回归项和 143 条
预期失败的 elaboration 测试**。默认运行 <code>leanphy_check --project-json</code> 会
报告 **8 个带证明的领域包、15 条已检查结论和 8 条开放义务**；运行
<code>--broad</code> 后报告 **13 个领域包、28 条结论和 14 条开放义务**。这些是库和
回归测试的指标，不代表已经形式化了相同数量的完整物理论文。

| 领域 | 已提供的可复用基础 | 仍需显式证明或登记的边界 |
| --- | --- | --- |
| 量子力学与量子信息 | Pauli 与 Dirac 记号、有限态与密度矩阵、POVM、CPTP/Kraus 通道、Bell/CHSH、有限 Lindblad 模型、振子与 CCR 代数 | 无界算子的定义域与自伴性、连续测量语义，以及有限模型与具体物理系统的对应关系 |
| 场论与高能代数 | 有限截断 Fock 空间、CAR/CCR 与 Wick 恒等式、Clifford/gamma 矩阵、自旋量、迹、Ward 型代数步骤、有限 EFT 展开、BRST 接口、低阶 Lie 模块上同调、有限 CAR ghost--antighost 适配器 | 场的存在性、无穷维极限、UV 完备性、重整化极限、完整 ghost 多项式代数、BV 结构、异常消除、Lie 群积分和非微扰结论 |
| 经典、规范、相对论、光学与流体 | Poisson 代数、第一类约束理想、弱等式、Dirac 可观测量、离散 Maxwell/Yang--Mills、外微分与 plaquette 恒等式、辛与 Lorentz 代数、Lie 表示、ABCD/Jones 光学、有限体积守恒和离散涡量 | 规范固定、约化空间正则性、连续正则性、全局存在性、边界物理、异常消除和湍流闭合 |
| 凝聚态与统计物理 | 格点、Hubbard、BdG、Berry、Jordan--Wigner、有限 Gibbs/Markov 核和转移矩阵 | 热力学极限、相变、实验参数标定，以及与连续理论的等价性 |
| 数学分析与数值接口 | Bochner 积分、支配收敛、Lax--Milgram、Banach 不动点、有界 Hilbert 算子、谱演算、谱隙、算子收敛、残差/能量预算、有限路径积分接口和逐 regulator 证书 | 外部程序只能提供可追溯数据；结果进入已验证层仍需 Lean 侧的正确性定理 |

无界算子接口使用 mathlib 的 <code>LinearPMap</code>，并把算子定义域保留在类型中。
<code>DenseDomainOperator</code> 为形式伴随、闭性、可闭性、自伴性、图范数相对界和定义域
保持的有界复合提供接口；每个接口都要求相应证明。把对象命名为
<code>Hamiltonian</code>，不会自动证明其自伴性，也不会自动生成时间演化。Stone 定理、
自伴扩张、谱测度以及从 resolvent 到演化群的桥接仍属于开放义务。

对于规范系统，<code>ConstraintAlgebra</code> 和 <code>ConstraintMap</code> 处理约束生成理想、
第一类闭合、弱等式、Dirac 可观测量，以及保持相应理想的 Poisson 映射。
<code>BRST</code> 要求显式给出微分和幂零证明；<code>GradedBRST</code> 进一步提供齐次分量、
奇次数移位和带 Koszul 符号的 Leibniz 规则。有限 CAR ghost--antighost 适配器是这些
接口的一个具体、由 kernel 检查的代数模型；它不等同于完整 ghost 多项式代数、BV 反括号、
规范固定、路径积分测度、异常定理或物理 BRST 上同调等价性。

<code>Mathematics.LieCohomology</code> 为规范理论、表示论和异常候选计算提供低阶代数接口。
作用和表示关系都显式保存，kernel 检查前两阶 Chevalley--Eilenberg 恒等式。该模块保留
见证项，不会暗中构造商上同调、把 Lie 代数积分为 Lie 群、证明异常消除，或把某个余循环
解释为物理可观测量。

逐模块清单和限制见 [VERIFIED.md](VERIFIED.md) 与
[docs/verified-scope.md](docs/verified-scope.md)。

## 快速开始

Lean 4.34.0 和 mathlib v4.34.0 固定在
[lean-toolchain](lean-toolchain) 与 [lakefile.toml](lakefile.toml) 中。在仓库根目录运行：

~~~bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
~~~

发布验证脚本会检查公共入口、下游客户端、研究账本、声明审计、项目脚手架和负向测试：

~~~bash
./scripts/verify.sh
~~~

建议使用本地 ext4 或 overlay 文件系统；在 FUSE 或网络挂载上，mathlib 导入和缓存访问
可能明显变慢。

## 最小示例

下面是普通的 Lean 代码。<code>hCCR</code> 是显式给出的正则对易关系；结论是一个已经
编译并通过 kernel 检查的定理：

~~~lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
~~~

这个例子验证的是“由 CCR 前提推出对易子恒等式”。它不证明存在满足 CCR 的无界 Hilbert
空间表示，也不证明该表示描述某个实验。有限 EFT 和有限路径积分接口同样要求显式的
截断、误差和归一化证书。缺少必要前提时，代码会在 elaboration 阶段失败，不会生成
无条件结论。

## 推荐的研究工作流

1. 选择最小的 <code>LeanPhy.Entry.*</code> 入口，减少无关依赖和编译时间。
2. 将数学前提、物理约定、边界条件、截断范围和近似参数写成类型、结构字段或定理参数。
3. 使用可复用定理和 tactic 完成代数步骤；若使用 CAS 或数值程序，通过带
   <code>CertificateChecker.sound</code> 定理的接口导入结果。
4. 将结果登记为 <code>TheoryPackage</code> 或 <code>ResearchProject</code> 中的
   <code>checked claim</code>，把尚未完成的分析、物理解释、连续极限和其他建模前提写入
   <code>open obligations</code>。
5. 运行 <code>leanphy_check</code> 和 <code>scripts/verify.sh</code>，同时检查人类可读报告
   与 JSON 报告。

账本中的 <code>VERIFIED-CONDITIONAL</code> 表示证明项已经编译并通过 kernel；这不等于模型
已经过实验验证，也不表示相关开放义务已经完成。阅读结果时，应同时查看对应条目的前提
和开放义务。

可信性审计可以单独运行：

~~~bash
lake env lean scripts/axioms.lean
~~~

项目源码和验收入口不使用 <code>sorry</code>、<code>admit</code> 或面向应用的未检查公理。
<code>#print axioms</code> 可能列出 Lean/mathlib 使用的标准基础公理，例如
<code>propext</code>、<code>Classical.choice</code> 和 <code>Quot.sound</code>；这与把某个
物理结论直接声明为公理不同。

## 仓库结构

~~~text
LeanPhy/                 按物理领域组织的库源码
  Mathematics/            分析、算子、谱、极限、证书与通用模型
  Quantum/ QuantumInfo/   量子力学与量子信息
  FieldTheory/            CCR/CAR/Fock/Wick 代数
  HighEnergy/             Clifford、gamma、自旋量和有限 EFT 接口
  GaugeTheory/            规范场、离散几何代数与有限 ghost 适配器
  Condensed/ StatMech/    凝聚态与统计模型
  Classical/ Relativity/  经典力学与相对论结构
  Surface/                Dirac、Einstein、指标和量纲记法
  Entry/                  按领域选择的公共入口
  Examples/               工作流和研究项目示例
Main.lean                kernel 回归入口
Prototype.lean           端到端工作流原型
Check.lean               研究账本 CLI
scripts/                 发布验证和负向测试
docs/                    架构、路线图和详细范围
~~~

常用入口包括 <code>LeanPhy.Minimal</code>、各领域的 <code>LeanPhy.Entry.*</code>，以及需要
组合多个领域时使用的 <code>LeanPhy.Entry.Physics</code>。

## 开发与引用

~~~bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
~~~

新增模块应提供可复用定理、明确假设、正向 smoke 回归、必要的负向回归、公共入口导出，
以及说明它如何与现有证书组合的文档。开发规范见
[CONTRIBUTING.md](CONTRIBUTING.md)、[docs/architecture.md](docs/architecture.md) 和
[docs/roadmap.md](docs/roadmap.md)。

引用 LeanPhy 时请记录提交号、Lean 工具链、mathlib 修订、入口 profile 和生成的账本 JSON。
引用信息见 [CITATION.cff](CITATION.cff)。项目采用 Apache License 2.0。
