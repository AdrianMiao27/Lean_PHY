# LeanPhy v1（中文说明）

LeanPhy 是建立在 Lean 4 与 mathlib 之上的理论物理推导验证库。它验证的命题是：

> 在显式给出的数学和物理假设下，结论确实由证明项推出。

LeanPhy 不把模型是否描述真实世界、连续极限是否存在、路径积分是否存在或物理解释
是否成立自动变成定理。每条已验证结论都由 Lean kernel 检查，未完成的分析和物理
前提进入开放义务账本。

## v1 已包含的能力

- 量子力学与量子信息：Pauli、Dirac 记号、密度矩阵、POVM、CPTP/Kraus、Bell/CHSH、
  Lindblad 有限模型、振子与 CCR；
- 场论和高能代数：有限 Fock/CAR/CCR/Wick、Clifford/gamma 矩阵、自旋量、迹与
  Ward 风格代数步骤；
- 凝聚态与统计力学：格点、Hubbard、BdG、Berry、Jordan–Wigner、有限 Gibbs、Markov
  核与转移矩阵；
- 规范、经典、相对论、光学和流体：离散 Maxwell/Yang–Mills、外微分、辛和 Lorentz
  代数、ABCD/Jones 光学、有限体积守恒和离散涡量；
- 数学与数值桥接：Bochner 积分、支配收敛、Lax–Milgram、Banach 不动点、有界
  Hilbert 算子、预解式、多项式谱演算、谱隙、算子收敛、残差/能量预算、有限路径
  积分和逐 regulator 重整化证书。

连续路径测度、OS 重构、一般谱测度、无界 Hamiltonian 的自伴扩张、完整重整化极限、
Navier–Stokes 正则性和非微扰 QFT 存在性仍是显式开放义务，详见
[VERIFIED.md](VERIFIED.md) 和 [docs/roadmap.md](docs/roadmap.md)。

## 快速开始

在安装 Lean 4.34.0 后，从仓库根目录运行：

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
./scripts/verify.sh
```

最后一个命令是发布门禁，会检查完整构建、446 项 smoke、130 条负向 elaboration
夹具、研究包 JSON、下游客户端、声明审计和无 `sorryAx`。首次构建建议使用本地
ext4/overlay 文件系统；网络或 FUSE 挂载上的 mathlib 导入可能很慢。

## 研究工作流

在 [`LeanPhy/Workflow.lean`](LeanPhy/Workflow.lean) 中，`TheoryPackage` 记录假设、
模型、kernel-checked claims、依赖、范围边界和开放义务。`ResearchProject` 支持跨
领域组合。外部 CAS/数值结果只能通过带 `sound` 证明的 `CertificateChecker` 进入
已验证结论，运行时布尔值和未检查 JSON 不具有证明地位。

推荐按领域选择入口：`LeanPhy.Entry.Quantum`、`LeanPhy.Entry.FieldTheory`、
`LeanPhy.Entry.Analysis` 等；跨多个领域时再使用 `LeanPhy.Entry.Physics`。`physics`、
`physics_search`、Dirac 记号、Einstein 求和、指标方差和量纲层均保持原生 Lean 工作流。

## 仓库结构和贡献

`LeanPhy/` 是按领域组织的库，`Main.lean` 是 kernel smoke 入口，`Prototype.lean` 是
端到端原型，`Check.lean` 输出研究账本，`scripts/` 保存发布验证与负向测试，`docs/`
保存架构、范围和路线图。新模块应提供可复用定理、明确假设、正向 smoke、必要的负向
测试和文档；详见 [CONTRIBUTING.md](CONTRIBUTING.md)。

版本、许可证和引用信息见 [CHANGELOG.md](CHANGELOG.md)、[LICENSE](LICENSE) 和
[CITATION.cff](CITATION.cff)。

