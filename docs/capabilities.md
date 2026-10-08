# LeanPhy 全局能力盘点

**2026-10-08 验证更新：** 最新单次全量运行被中断；本批专项及剩余回归现已分段通过，不能据此声称完整发布脚本已有成功终态。历史批次数字保留作比较；当前 R07 Euler 传输增量与客户端检查以 [VERIFIED 顶部记录](../VERIFIED.md) 为准。


对象是 `/mnt/data/tingchia/Lean_PHY` 的当前工作树，包含尚未提交的修改；不是仅审查 Git HEAD。最近盘点：2026-10-07。建设顺序见 [全局路线](roadmap.md)。本清单把已有实现、物理适用范围和验证状态分别记录；单项功能完成不代表对应研究领域已经完整覆盖。

文档入口见[导航](README.md)，目录职责见[项目文件布局](project-layout.md)。当前阶段状态以本页、[建设路线](roadmap.md)和根目录 [VERIFIED](../VERIFIED.md) 为准。

## 1. 当前判断与证据范围

项目已经具备大量可复用的有限量子对象、代数操作、条件性分析定理，以及一条较完整的 Lie／上同调／变形证书计算链。公共核心、准确的目标关闭与历史、编译声明检索及局部耦合变分已接入；有限 CAR 构造、实际有限时间响应与非对易 Gibbs 导数也已贯通。新增探索分支把条件、反例和模型修订接到同一账本；有限静态链已连接“有限作用量／能量 → 系综／量子热态 → 静态响应／温度导数 → 有限源误差”。此前批次增加了非交换逐阶运算、分块消元及有效源／读数、代数重场替换和逆残差界，并分别取得相应的集成与发布证据；本次有限频率、任意模式真空和有限格点 Ward／RG 出口已通过模块与客户端检查，完整发布检查仍待完成。但研究者常用的“模型 → 推导操作 → 物理可观测量 → 近似有效性”仍未普遍连通。新增有限源自洽已从实际权重与有限输入界推导适用域和解／读数误差。下一阶段的重点是补公共操作与模块转换，使已有工具能够共同处理新的模型。

本次枚举了全部库源文件，核对公共入口、构建与审计脚本，并按下表阅读相关定义、定理签名和关键实现。状态反映本仓库暴露的研究能力；“缺口”不意味着 mathlib 不存在可用基础，也不意味着每个文件的每个证明都已重新审查。

### 全局功能总览

从研究者的使用角度，项目当前是“已有若干可用推导链和大量公共基础”，还没有普遍覆盖从候选模型到受控物理结果的全过程。下表先给全局判断，后文逐项给源码证据。

| 功能组 | 当前可以直接复用 | 仍需完善的主要能力 | 对研究工作的影响 |
| --- | --- | --- | --- |
| 模型表达与物理约定（C01–C04、C07） | 量纲、有限指标、张量收缩、参数重索引、部分格点模型、任意有限费米占据、二次型和一般相互作用表达式 | 高效稀疏相互作用模型；不同表述间的态、算符、单位、基底和符号转换 | 新模型仍有较多重复建模与人工约定核对。 |
| 量子态、系综与谱（C05、C06、C08） | 有限密度矩阵、酉指数演化、Hermitian 热态、Gibbs／Markov、非对易热扰动与实际时间导数；新增由有理复矩阵残差认证的有限谱排除圆盘 | 一般时变演化、单个本征值／谱区间、稳定低能投影与更广参数域 | 有限态、静态与有限时间响应已有连接；部分谱域可从实际数据核验，完整谱分析仍需完善。 |
| 场论推导与算符操作（C09–C12） | CCR/CAR 恒等式、任意费米词正规化、一阶多分量变分、Noether／应力张量；新增实际 C² 场第一变分、区间作用量和流平衡 | 玻色／混合分级正规序、真实态 Wick 收缩；全局逆场坐标、导数依赖／高阶 EOM 冗余、协变／分级场及多维边界积分 | 新增点场替换的实际 Euler／变分流传输及正则域内方程对应，已通过专项检查；完整场论操作和多维积分电荷仍需完善。 |
| 关联、响应与自洽（C12、C13、C15、C19、C20） | 实际源／温度导数、非对易 Gibbs 导数、有限时间积分对易子响应、有限采样 Fourier 重构、接触项、有限源误差；新增实际有限源自洽映射、输入界到压缩域及解／读数误差；新增任意有限模式空占据真空的任意长度线性探针矩、CAR 接触项及词／表达式读数；新增有限权重对称到 Schwinger–Dyson/Ward 插入的桥 | 一般驱动／连续频率响应、一般真实态多点关联、局部临界／多分支及量子自洽 | 静态、有限时间扰动、有限网格频率读数和有限 Ward 插入已接通；一般 Gaussian／热态、时间排序／源插入、频率极限、余项控制与有限闭合模型之外的自洽仍有断点。 |
| 有效理论与尺度（C14、C17、C18） | 有限幂计数尾界、有限 blocking、非交换逐阶操作、精确分块消元、有效源／读数及代数重场作用量；新增有限能量圆盘内的一致逆界与消元误差；新增 finite RG 缺陷的配分函数、归一化读数和多阶段预算 | 更广低能适用域、能量无关酉约化、传播重场的导数展开、IBP/EOM 冗余及受控 RG | 有限矩阵证据已能约束实际有效算符、源和读数；有限 blocking 缺陷可以组合并传到读数，但算符／耦合投影、截断闭合、实际 beta 流和方案转换仍未完成。 |
| 对称、规范与拓扑（C11、C16、C28） | 约束与映射；较完整的有限 Lie／ghost 计算；局部能带几何代数 | 将对称计算接到物理场、作用量和观测量；从能带／投影构造拓扑量 | 对称专题的成熟度较高，物理解释桥和能带拓扑链仍需补齐。 |
| 数值辅助与近似控制（C19–C23） | 误差组合、残差传播、条件性连续桥、Lie 精确证书；新增有理复矩阵到实际逆、谱域及有效算符／源／读数误差的核验链 | 自动可靠的物理／舍入包络、通用区间与多项式证书、自动数值残差包络、局部稳定性认证、稀疏规模性能 | 有限矩阵链已消费真实候选数据；模型位于误差球内的证明仍需提供，不能把数值容差直接当作已证误差。 |
| 探索与复现（C24–C27） | 原目标绑定、假设分支、实际反例／失败记录、覆盖合并、显式修订复用、声明检索与独立审计 | 约定与适用域的语义检索、自动变更影响分析、跨项目探索协作 | 探索过程已有公共操作；修订时仍需调用方证明域／目标传输。 |

下一阶段的全局任务是减少上述各组之间需要手工重建的部分。不能以某个组新增定理较多，推断其它组已经可用；也不能把“调用方提供完整结论证明”的接口计为相应求解功能。

| 基线 | 本次核对结果 | 如何解释 |
| --- | --- | --- |
| 工具链 | `leanprover/lean4:v4.34.0`；固定依赖见 `lake-manifest.json` | 后续迁移必须在相同依赖上重验。 |
| 当前库源码 | `LeanPhy/` 下 374 个 `.lean` 文件、68,267 行；其中 `Examples/` 73 个 | 任意点数真空、Euler 传输、Gibbs 数值和传播重场匹配的专项检查已加入；当前新增范围的完整发布验证尚未完成。 |
| 最近完整验收的源码基线 | 357 个库源文件、65,037 行，包含 70 个示例模块 | 包含实际有限源反馈、输入界到自洽域、解／读数误差及能量／驻值桥；不代表原模型求解或临界理论。 |
| 领域入口 | 14 个 `Entry/` 模块，另有 `Minimal` 与完整入口 | `Workflow.Core` 独立于默认领域包，兼容入口保留。 |
| 历史自洽批次引理目录 | 64 项精选目录保留；编译索引 9,120 项公开声明，其中 4,268 个定理 | 实际类型、条件、源码及库内直接证明引用可检索；索引不替代完整声明审计。 |
| 历史自洽批次验证记录 | 777 项 smoke、378 条负向夹具、169 项 Python 测试（含 17 项公共层集成、4 项自洽回归）通过 | 全库审计覆盖 358 个模块、16,770 个声明／464 个私有声明；435 个源码、配置、脚本与数据文件符合冻结快照。 |

还有一份独立目录 `../Inspirations/Lean_phy`。该目录已有 `Workflow.Core`、编译声明索引、通用一阶变分、有限源响应等实现；当前仓库则有该目录没有的 H³、三阶变形联合搜索、物质 ghost 与完整研究项目审计工具。因此它们不是可以直接覆盖的同一版本。已按模块整合目标绑定、核心分离、索引、一阶变分和有限源响应；本仓库新增任意有限 Hermitian 量子热态、基底及响应桥。下表只计算**本仓库**的当前能力，原有 Lie／ghost 与完整审计继续保留。

## 2. 状态的含义

| 状态 | 判定标准 |
| --- | --- |
| 通用 | 在明确范围内接受可变模型／参数／指标，有实际操作与已写出的证明，可被下游复用。有限维并不自动降为“局部”。 |
| 局部 | 有真实计算或证明，但固定维度、特定模型、特定阶数，或尚未接通相邻研究步骤。 |
| 接口 | 有安全承载或传播条件的结构和定理，但关键求解、存在性或误差输入仍由调用方提供。接口有价值，不能算作相应物理问题已解决。 |
| 缺口 | 尚未找到可组合的公共实现；后续需要补功能或明确适配 mathlib。 |

同一能力可以同时具有通用工具、局部演示和未完成接口。以下 C 编号是本仓库本次盘点的稳定编号，不与另一目录自动对应。源码链接是证据入口；详细历史仍保留在 [VERIFIED.md](../VERIFIED.md) 和各专题指南中。

功能成熟度与验证状态分别记录：源码存在、模块编译、独立客户端集成、完整发布验证是不同证据。一次发布验证通过，只能证明相应源码和回归通过检查；它不会将条件性接口升级为求解器，也不会将有限模型升级为连续理论。下表中的“通用”始终受该行适用范围限制。

## 3. 模型、对象与物理约定

| 编号／研究需求 | 已有能力与源码证据 | 状态及适用范围 | 需要完善的功能 |
| --- | --- | --- | --- |
| C01 量纲与尺度 | [Dimensions](../LeanPhy/Dimensions.lean)：七个 SI 基量的整数幂；`Quantity` 限制加法、乘除及幂的量纲 | 通用的量纲记账 | 自然单位、无量纲化与恢复物理尺度的转换；将尺度接到 Hamiltonian、作用量及截断参数。 |
| C02 指标、张量与基底 | [TypedTensor](../LeanPhy/Surface/TypedTensor.lean)、[GenericTensor](../LeanPhy/Surface/GenericTensor.lean)、[IndexCalculus](../LeanPhy/Surface/IndexCalculus.lean)：有限指标收缩、上下标、混合张量组合 | 通用有限代数；部分度规操作限于四维约定 | 明确轨道／格点／自旋／Lorentz 指标空间；哑指标改名、基底变换、伴随与收缩的一致性。 |
| C03 模型、参数与可观测量传输 | [Model](../LeanPhy/Mathematics/Model.lean)、[ParametricModel](../LeanPhy/Mathematics/ParametricModel.lean)：合法态、一步演化、观测量、模型映射与参数重索引；映射可组合并传输读数；[Exploration](../LeanPhy/Workflow/Exploration.lean) 可拉回实际研究域／目标并证明修订传输 | 通用离散过程与研究谓词操作；新增一阶时间作用量到旧力学 jet 的方程一致性桥，其余互接不足 | 按描述类型建立适配器；静态模型不必虚构一步演化。参数域、态、算符、读数保持关系进入实际命题。 |
| C04 物理约定与表述转换 | [HamiltonianFlow](../LeanPhy/Quantum/HamiltonianFlow.lean) 明确使用 `exp(+ i t H)`；[FiniteFourier](../LeanPhy/Mathematics/FiniteFourier.lean) 有归一化与逆变换；各领域自带符号 | 局部一致；新增场标签单射重命名及时间作用量转换；新增热态与迹期望的酉基底转换；新增完整 Nambu／多体及轨道换基桥；其它约定未系统互接 | 完整 Nambu 共轭与复配对已接入；继续时间／Fourier、单位与尺度转换、一般粒子空穴混合；见第 6 节。 |
| C05 有限量子态与演化 | [FiniteDensity](../LeanPhy/Quantum/FiniteDensity.lean)、[HamiltonianFlow](../LeanPhy/Quantum/HamiltonianFlow.lean)、[FiniteThermalState](../LeanPhy/Quantum/FiniteThermalState.lean) 提供有限态与热态；新增 [DynamicalResponse](../LeanPhy/Quantum/DynamicalResponse.lean) 的实际 Heisenberg／态导数、图像读数一致性和非对易扰动；[TimeDependentEvolution](../LeanPhy/Quantum/TimeDependentEvolution.lean) 从非自治方程推出酉性与有序传输 | 通用有限工具，允许简并；响应首批已编译并集成，发布验证已通过 | 一般 ODE 存在性、任意实验室系驱动和时间有序多点关联仍开放；谱选择不是可微本征矢或数值求解器。 |
| C06 谱、能隙与低能子空间 | [HermitianSpectrum](../LeanPhy/Quantum/HermitianSpectrum.lean)、[SpectralCalculus](../LeanPhy/Mathematics/SpectralCalculus.lean)、[ParametricSpectralGap](../LeanPhy/Quantum/ParametricSpectralGap.lean)：有限 Hermitian 谱桥、多项式谱映射、显式谱隙证书；新增 [EffectiveHamiltonian](../LeanPhy/Quantum/EffectiveHamiltonian.lean) 的能量依赖消元、重构与二次读数；新增 [CertifiedResolvent](../LeanPhy/Quantum/CertifiedResolvent.lean)，从有理残差认证实际有限谱的能量圆盘排除域与一致逆界 | 通用有限代数与谱接口；有理证书现可产生有限圆盘的一致逆及误差，完整发布验证已通过 | 继续单个本征值／谱区间、稳定投影和更广参数域认证；证明能量无关酉约化及动态误差，圆盘排除不是完整谱分解。 |
| C07 多体与凝聚态模型构造 | [FiniteFermion](../LeanPhy/FieldTheory/FiniteFermion.lean) 构造实际占据表示；二次 Nambu／复配对桥保留；新增 [FermionPolynomial](../LeanPhy/FieldTheory/FermionPolynomial.lean)、[FermionEmbedding](../LeanPhy/FieldTheory/FermionEmbedding.lean)、[InteractingFermion](../LeanPhy/FieldTheory/InteractingFermion.lean) 将任意有限相互作用表与局部模式嵌入接到实际算符和热态 | 通用有限费米表达式和表示桥；新批次专项通过，完整发布验证已通过 | 高效稀疏后端、大系统性能、一般换基后的相互作用系数传输；有限实源自洽已接入，量子自洽及闭合误差仍缺；不等于完整多体求解器。 |
| C08 系综与统计过程 | [FiniteGibbs](../LeanPhy/StatMech/FiniteGibbs.lean)、[SourceEnsemble](../LeanPhy/StatMech/SourceEnsemble.lean)、[GibbsResponse](../LeanPhy/StatMech/GibbsResponse.lean)、[FiniteDetailedBalance](../LeanPhy/StatMech/FiniteDetailedBalance.lean)：实际有限指数系综、log Z 一阶／方向二阶导数、易感率、接触项、能量源 β 因子和热容；Markov 与详细平衡；新增 [SourceFeedback](../LeanPhy/StatMech/SourceFeedback.lean) 构造实际有限源自洽映射 | 通用有限静态工具；量子 Gibbs 导数已验收，新增有限实源反馈及输入界专项通过，完整发布验证已通过 | 局部／多分支及量子自洽、更一般非平衡过程、热力学极限和单位转换；有限响应范围见 C13。 |

## 4. 推导操作与物理结果

| 编号／研究需求 | 已有能力与源码证据 | 状态及适用范围 | 需要完善的功能 |
| --- | --- | --- | --- |
| C09 算符代数与正规序 | 原 CCR/CAR、外代数、对易子工具保留；新增 [FermionWord](../LeanPhy/FieldTheory/FermionWord.lean) 的任意词长终止算法和严格排序／语义证明，[FermionPolynomial](../LeanPhy/FieldTheory/FermionPolynomial.lean) 的精确表达式与恒等式检查 | 通用有限费米正规化，保留常数收缩、反对易符号与 Pauli 消去；新批次专项通过，完整发布验证已通过；玻色 Fock 模块仍为抽象 CCR | 玻色占据截断及边界修正、通用分级混合对象、高效系数收集和性能；实际态到多点收缩仍属 R05。 |
| C10 作用量与变分 | [Variational](../LeanPhy/FieldTheory/Variational.lean)、[PolynomialAction](../LeanPhy/FieldTheory/PolynomialAction.lean) 提供任意有限分量的一阶形式操作；[FieldEvaluation](../LeanPhy/FieldTheory/FieldEvaluation.lean)、[CurveJet](../LeanPhy/FieldTheory/CurveJet.lean)、[IntervalAction](../LeanPhy/FieldTheory/IntervalAction.lean) 连接实际场、符号方程与区间积分；新增 [PointTransformation](../LeanPhy/FieldTheory/PointTransformation.lean)、[RedefinitionVariation](../LeanPhy/FieldTheory/RedefinitionVariation.lean) 连接点场替换与实际一阶 Euler／边界变化；[EulerTransport](../LeanPhy/FieldTheory/EulerTransport.lean) 从密度导出 Jacobian 转置 Euler 传输、变分流及右逆／行列式条件下的方程对应 | 局部变分／区间积分已完整验收；点场替换专项通过，当前发布检查待完成 | 全局逆坐标及分支覆盖、高阶／导数依赖 IBP/EOM、协变／分级场、多维边界和区域正则性；见[场替换指南](field-redefinitions.md)。 |
| C11 对称、约束与守恒 | [SymmetryReduction](../LeanPhy/Mathematics/SymmetryReduction.lean)、[ConstraintAlgebra](../LeanPhy/Mathematics/ConstraintAlgebra.lean)、[ConstraintMap](../LeanPhy/Mathematics/ConstraintMap.lean)：轨道不变量、约束理想、弱等式及 Dirac 观测量传输；[EnergyMomentum](../LeanPhy/FieldTheory/EnergyMomentum.lean) 和 [IntervalAction](../LeanPhy/FieldTheory/IntervalAction.lean) 提供局部恒等式到实际剖面流的桥 | 通用代数约束与局部对称操作；新增一维 Noether 端点守恒和离壳积分平衡 | 多维空间积分电荷、边界物理、规范固定与约化条件；一维流结论不自动消去横向通量。 |
| C12 Wick 与关联函数 | [Wick](../LeanPhy/FieldTheory/Wick.lean)、[MultiWick](../LeanPhy/FieldTheory/MultiWick.lean)、[FermionicWick](../LeanPhy/FieldTheory/FermionicWick.lean)、[FiniteCorrelator](../LeanPhy/Mathematics/FiniteCorrelator.lean)：单模矩、递归收缩、费米符号与有限连通二点代数；新增 [FermionVacuum](../LeanPhy/FieldTheory/FermionVacuum.lean) 从 CAR 与实际密度真空消去条件推导任意有限模式、任意线性探针的二点／四点读数；[FermionVacuumWick](../LeanPhy/FieldTheory/FermionVacuumWick.lean) 推广到任意长度矩、奇数矩、接触项及整数词／符号表达式读数；[FermionUnitaryWick](../LeanPhy/FieldTheory/FermionUnitaryWick.lean) 将实际真空和生成元同步有限酉传输并保持任意有序矩 | 有限真空任意点数和共同酉传输是通用操作，已构造任意模式数空占据态；物理期望与反对称有序 kernel 分开，重复物理探针保留接触项 | 从满足明确条件的真实 Gaussian／准自由态证明任意多点收缩；重复指标、热态协方差、时间排序、源生成与连通展开共同校验。一般 Gaussian／热态与时间排序桥尚未完成，稠密配对递归的规模性能另验；仅定义 `gaussianMoment` 不等于证明某态服从 Wick。 |
| C13 Green 函数与响应 | [DynamicalResponse](../LeanPhy/Quantum/DynamicalResponse.lean) 从实际演化得到有限时间积分对易子响应、开关常值源的因果响应和探针接触项；[ThermalPerturbation](../LeanPhy/Quantum/ThermalPerturbation.lean) 从实际归一化 Gibbs 态得到非对易导数；[FiniteFrequencyResponse](../LeanPhy/Quantum/FiniteFrequencyResponse.lean) 在给定有限采样和 Fourier 系统上提供频率系数与逆重构 | 有限静态／常值扰动和有限网格 Fourier 操作可复用；R06 增量模块与客户端检查通过，完整发布检查待完成 | 一般 ODE 存在性、任意实验室系驱动、平稳态的时间差化简、连续谱／频率表示、输运极限和受控余项；有限网格重构不能替代这些结论，也不能把静态协方差代替一般量子响应。 |
| C14 形式展开与有效理论 | [FormalExpansion](../LeanPhy/Mathematics/FormalExpansion.lean)、[FormalBlockElimination](../LeanPhy/Mathematics/FormalBlockElimination.lean)：非交换乘法／逆／相似变换与保留阶数；[BlockElimination](../LeanPhy/Mathematics/BlockElimination.lean)：任意有限块、源、重构及线性读数；新增 [CertifiedElimination](../LeanPhy/Mathematics/CertifiedElimination.lean) 将实际逆残差接到消元误差；原 [EffectiveTheory](../LeanPhy/HighEnergy/EffectiveTheory.lean) 保留幂计数尾界；新增 [PropagatingHeavy](../LeanPhy/FieldTheory/PropagatingHeavy.lean)、[HeavyFieldMatching](../LeanPhy/FieldTheory/HeavyFieldMatching.lean)、[HeavyFieldInterval](../LeanPhy/FieldTheory/HeavyFieldInterval.lean) 的混合二次传播重场有限展开、源／读数、实际区间匹配与残差／端点预算 | 精确与形式操作已通过完整发布检查；新增有限矩阵证书消费链已通过完整发布检查。形式逆仍要求常数项为单位，形式等价本身不蕴含范数界；重场方程由密度变分导出，实际区域解释限于一维区间 | Green 函数与到精确解的一致误差、非二次重场、IBP/EOM 算符基、量子行列式及圈匹配、能量无关酉约化 |
| C15 有限路径和、源与变换 | [FinitePathIntegral](../LeanPhy/Mathematics/FinitePathIntegral.lean)、[FiniteSourceResponse](../LeanPhy/FieldTheory/FiniteSourceResponse.lean)、[FiniteActionResponse](../LeanPhy/FieldTheory/FiniteActionResponse.lean)、[FiniteSchwingerDyson](../LeanPhy/Mathematics/FiniteSchwingerDyson.lean)：有限复加权和、推前、真实指数源导数、作用量求值到负协方差插入；权重对称、单位 Jacobian 和有限 Ward 插入；与实概率期望和连通关联有证明的转换 | 通用有限操作；复源归一化逐点要求 Z ≠ 0，实非空系综有 Z > 0 证明；Ward 桥要求显式有限对称与 involution | 梯度表到实际离散化、连续测度与极限、时间排序；复／带符号权重不继承概率正性；有限 Ward 恒等式不自动成为连续 Schwinger–Dyson 方程。 |
| C16 规范、BRST 与对称变形 | [LieCohomology3](../LeanPhy/Mathematics/LieCohomology3.lean)、[LieDeformationThirdSearch](../LeanPhy/Mathematics/LieDeformationThirdSearch.lean)、[LieGhostComplex](../LeanPhy/GaugeTheory/LieGhostComplex.lean)、[LieGhostMatterCohomology](../LeanPhy/GaugeTheory/LieGhostMatterCohomology.lean)：实际 H²/H³、显式结构常数模型、参数合法域、障碍与三阶修正、ghost 幂零及低次物质桥 | 范围内较完整的计算链；不是全阶 BRST/BV 或物理谱 | 优先把这些 Lean 约束映射接到物理场内容、作用量与观测量；旧的外部符号生成器已从 v1.1 脚本集移除。物质全次数对应、负 ghost 次数、BV 等按实际阻塞推进。避免此主线独占开发。 |
| C17 粗粒化与重整化 | [FinitePathIntegral](../LeanPhy/Mathematics/FinitePathIntegral.lean)、[FiniteRGDiagnostics](../LeanPhy/Mathematics/FiniteRGDiagnostics.lean)：有限 blocking、配分函数和期望误差；`FixedPointDefect` 的逐点缺陷、分阶段组合和归一化读数证书；[Renormalization](../LeanPhy/Mathematics/Renormalization.lean)：给定减除和极限的传输 | 通用有限推前＋显式分母／插入界的误差接口；[有限格点研究客户端](../LeanPhy/Examples/FiniteLatticeResearch.lean) 已把 Ward、缩放和 RG 缺陷接成可审计出口 | 算符／耦合的投影、截断闭合与累计误差；实际 beta 流与方案转换；有限推前不等于已推导连续 RG。 |
| C18 高能运动学、振幅与算符基 | [Scattering](../LeanPhy/HighEnergy/Scattering.lean)、[Ward](../LeanPhy/HighEnergy/Ward.lean)、[DiracFierz](../LeanPhy/HighEnergy/DiracFierz.lean)、[ColorAlgebra](../LeanPhy/Particles/ColorAlgebra.lean)、[AnomalyCancellation](../LeanPhy/Particles/AnomalyCancellation.lean)：运动学、给定在壳条件下 Ward、显式 Fierz/颜色及给定粒子内容的反常系数算术；[HeavyFieldElimination](../LeanPhy/FieldTheory/HeavyFieldElimination.lean) 从任意轻场多项式和一个非零二次系数的辅助重场推导诱导作用量与插入；二次传播重场已接有限阶匹配及实际区间作用量 | 可复用代数＋局部物理链；重场操作只覆盖代数辅助场 | 从作用量获得顶角／树级收缩，操作 IBP/EOM 算符冗余并跟踪阶数；更广传播重场／Green 函数、行列式／测度、圈积分及一般散射仍缺。 |
| C28 拓扑与能带几何 | [Berry](../LeanPhy/Condensed/Berry.lean)、[Topological](../LeanPhy/Condensed/Topological.lean)、[Winding](../LeanPhy/Mathematics/Winding.lean)：两带代数、球面三重积、路径／绕数基础及部分能隙工具 | 局部几何与代数 | 从选定能带／投影定义曲率，固定归一化，连接规范变换、积分与不变量；体边对应和相变结论不能由能隙闭合单独推出。 |

## 5. 近似、证据和研究工作流

| 编号／研究需求 | 已有能力与源码证据 | 状态及适用范围 | 需要完善的功能 |
| --- | --- | --- | --- |
| C19 误差、残差与自洽 | [Approximation](../LeanPhy/Mathematics/Approximation.lean)、[CertifiedResidual](../LeanPhy/Mathematics/CertifiedResidual.lean)、[Contraction](../LeanPhy/Mathematics/Contraction.lean)、[ResidualInverse](../LeanPhy/Mathematics/ResidualInverse.lean)、[CertifiedElimination](../LeanPhy/Mathematics/CertifiedElimination.lean)；[FeedbackCertificate](../LeanPhy/StatMech/FeedbackCertificate.lean) 从有限输入界导出实际 Gibbs 自洽域及后验误差；[IntervalAction](../LeanPhy/FieldTheory/IntervalAction.lean) 提供实际 Noether 流累计误差；`FiniteRGDiagnostics` 将 blocking 缺陷消费为分母显式的归一化读数证书 | 通用误差传播；有限矩阵逆／消元、实际区间流和有限 RG 缺陷已有误差桥；新增有限 Gibbs 自洽域及解／读数后验界 | 原有限自洽及近似更新／读数预算批次已通过完整发布验证；局部稳定性、不确定实输入包络、闭合模型误差、有限 RG 的耦合投影和有限振幅响应仍需完善；[GibbsCertificate](../LeanPhy/StatMech/GibbsCertificate.lean) 新增可求值的指数／归一化读数包络，并实际消费为自洽残差及解／读数界；矩阵范数与区间误差的适用范围分别保留。 |
| C20 连续动力学与耗散 | [LinearFlow](../LeanPhy/Mathematics/LinearFlow.lean)、[ContinuousEvolution](../LeanPhy/Mathematics/ContinuousEvolution.lean)、[EnergyDissipation](../LeanPhy/Mathematics/EnergyDissipation.lean) 保留流及条件性预算；新增 [Duhamel](../LeanPhy/Mathematics/Duhamel.lean) 从实际指数导出有限时间差分、非对易导数和共轭插入积分；[TimeDependentEvolution](../LeanPhy/Quantum/TimeDependentEvolution.lean)／[DrivenResponse](../LeanPhy/Quantum/DrivenResponse.lean) 从实际非自治方程和连续解族导出有序传输与一阶响应 | 完备赋范代数中的实际操作＋更广连续接口；已由有限量子响应消费，新增 IntervalAction 连接实际剖面与流的积分预算 | 一般驱动系统、无界生成元定义域、统一稳定性和扰动余项；有限时间导数本身不提供有限振幅误差界。 |
| C21 无界算子与无限维谱 | [UnboundedOperator](../LeanPhy/Mathematics/UnboundedOperator.lean)、[InfiniteSpectrum](../LeanPhy/Mathematics/InfiniteSpectrum.lean)、[HilbertSpectrum](../LeanPhy/Mathematics/HilbertSpectrum.lean)：定义域、`LinearPMap`、闭性／伴随／自伴证书、resolvent 条件 | 通用定义域基础＋分析接口 | 按目标模型补实际自伴性、扩张、resolvent 到演化的桥；不先追求一套独立完整泛函分析库。 |
| C22 PDE、离散化与极限 | [FiniteElliptic](../LeanPhy/Mathematics/FiniteElliptic.lean)、[WeakPDE](../LeanPhy/Mathematics/WeakPDE.lean)、[DominatedConvergence](../LeanPhy/Mathematics/DominatedConvergence.lean)、[OperatorConvergence](../LeanPhy/Mathematics/OperatorConvergence.lean)：有限方程、弱形式、支配与算符误差到观测量收敛 | 范围内通用定理＋模型条件接口 | 为所选场论／多体链提供可核验的一致性、稳定性、定义域、支配与参数一致界；不以“有 Tendsto 字段”报告极限已建立。 |
| C23 外部计算与证书 | [ExternalCertificate](../LeanPhy/Mathematics/ExternalCertificate.lean)、[MatrixCertificate](../LeanPhy/Mathematics/MatrixCertificate.lean)、[matrix_certificate.py](../scripts/matrix_certificate.py)：精确有理复矩阵、实际残差重算、模型球与 soundness；[RationalExp](../LeanPhy/Mathematics/RationalExp.lean)、[GibbsCertificate](../LeanPhy/StatMech/GibbsCertificate.lean) 与 [数值生成器](../scripts/gibbs_certificate.py) 提供精确有理模型的指数／读数包络和实际自洽残差 | 矩阵核验已接入谱域／消元；指数核验已接自洽解和读数；Python 只生产候选数据，接受证明由 Lean kernel 计算；旧 Lie/SymPy 生成器不再作为发布依赖 | 一般不确定实输入、通用区间算术、其它函数与多项式物理证书、单个本征值认证和大规模稀疏性能仍缺；数据摘要不构成证明。 |
| C24 假设、猜想与研究账本 | [Workflow.Core](../LeanPhy/Workflow/Core.lean)、[Exploration](../LeanPhy/Workflow/Exploration.lean)：带证明结论、原目标索引、参数域／假设分支、反例与失败、覆盖合并、版本历史 | 通用工作流；分支和原目标绑定实际命题，修订产生新待证目标，复用需要显式证明；文本证据不关闭任务 | 仍需自动条件搜索、模型依赖的语义关联与变更影响；API 保证不等于不可篡改日志。 |
| C25 自动化、检索与诊断 | [Tactics](../LeanPhy/Tactics.lean)、[Library](../LeanPhy/Library.lean)：组合现有 tactic，64 项手工目录，区分大小写的子串检索 | 通用 tactic 入口＋[编译声明索引](../LeanPhy/Library/Index.lean)，保留精选目录 | 继续按研究操作、约定和适用域组织检索，并将未解任务定位到可编辑 Lean 目标；自定义命名空间使用其研究目录。 |
| C26 模块化与下游项目 | [Entry/Research](../LeanPhy/Entry/Research.lean)、[Scaffold](../LeanPhy/Scaffold.lean)、[audit_project.py](../scripts/audit_project.py)：入口 profile、模板、独立项目审计、产物与源码追溯 | 公共工作流／CLI／目录核心已分离；研究入口包含分支操作，报告与严格检查消费同一项目；完整声明审计和旧 CLI 保留 | 按实际研究需要继续拆分报告层，扩展任务模板与性能诊断；维护下游兼容。 |
| C27 证明与发布验证 | [Verification](../LeanPhy/Verification.lean)、[audit_library.py](../scripts/audit_library.py)、[verify.sh](../scripts/verify.sh)：覆盖未从总入口导出的模块、私有声明和传递公理依赖；正负回归、镜像一致性 | 已有较完整的验证设施 | 按研究链维护回归与复现实验；检查编译产物确属当前源码。公理审计不能发现“证明了错误物理命题”的建模问题，仍需语义验收。 |

## 6. 优先处理的具体问题

以下同时记录初始审查结果和当前处理状态。目标绑定及耦合总导数已修复并接入正负回归；其它物理约定与功能缺口仍待处理。

1. **C24 已修复：关闭义务绑定原始目标。** 原来按名称删除且接受任意新命题证明；现在命题在登记时保存，`ObligationRef` 从具体包读取目标，关闭只移除该条并保存原目标证明。相关证据不能关闭文本任务。同名换目标、不同包引用、只给较弱结论均有拒绝回归。这修复的是账本完成状态，不改变 Lean 的证明逻辑。
2. **C10 已修复：耦合变分使用全分量总导数。** 对 `L = v₀ v₁`，现在第 0 条残差包含 `−a₁`；新的一阶作用量接口进一步通过方程一致性桥验证旧力学表达。通用 jet 保留任意阶形式导数，旧三槽表示仅用于相应一阶力学方程，不作为一般高阶变分器。
3. **C04/C07/C28：形式恒等式需要准确的物理解释。** `BCS.bdg` 对复数输入采用两处相同的 `Delta`，证明的是复对称矩阵平方；一般复配对的 Hermitian 模型需要共轭条目和相应实参数条件。`Berry.berry_density` 证明球面三重积为 `sin θ`，还没有从选定能带导出曲率及其归一化。本批新增复 Hermitian 配对、完整 Nambu 与伴随兼容的 Majorana 构造，并修正旧 BCS／Berry／Majorana 的说明；实际选带曲率、时间和单位转换仍开放。
4. **C12–C18：名称覆盖需落实为研究操作。** 有限静态响应已从实际权重导出，量子热态已接到矩阵指数。旧 `FiniteResponse` 的代数接口没有时间／扰动导数，实际有限时间与非对易热响应已由 `DynamicalResponse`／`ThermalPerturbation` 补接；`FiniteFrequencyResponse` 现在补上给定有限采样网格的 Fourier 系数和逆重构，但一般驱动、平稳性、连续频率与余项仍缺。原 `FiniteEFT` 不求匹配系数，新消元工具仅覆盖明确的分块／辅助场范围，`MultiWick` 的递归不自动证明真实态期望。盘点以实际可复用操作及其物理输入为准，不能只按旧模块名称判断全库能力。
5. **C23：外部证据能力有明确适用范围。** 保留的有理复矩阵和 Gibbs 生成器已有真实数据到证明的链条；前者将残差与模型偏差合成，并由 Lean 独立检查实际逆、谱域和消元结论。新增有理指数／归一化 Gibbs 包络已经生成实际自洽残差，并保留输出舍入误差。旧 Lie/SymPy 生成器已移除，不确定实输入、通用区间／多项式证书及规模性能仍缺，R11 保持部分交付。

6. **C09 已校正说明，玻色表示构造仍缺：Fock 代数不等于已构造 Fock 空间。** `FieldTheory.Fock.BosonicMode` 在任意环中记录一对升降算符和 CCR 前提，没有占据数空间、真空或有限截断构造。已将两份 README 的“有限截断 Fock 空间”改为符合源码的抽象代数描述；本批已构造实际有限费米表示；玻色占据表示及其截断边界仍列入 R03/R04，二者不能混同。

## 7. 按研究任务评估可用性

| 目标研究任务 | 现在能够复用 | 当前最主要的断点 |
| --- | --- | --- |
| 凝聚态有限多体／能带探索 | CAR、有限态、热态、静态响应与谱、格点片段、有限 Fourier、残差预算 | 高效相互作用表达与规模化表示、一般驱动／频率响应和真实态多点关联、能量无关低能约化及一致误差、实际拓扑不变量；有限矩阵证书已能构造指定域内的逆与消元误差，通用动态低能约化仍缺。 |
| 高能与有效场论探索 | gamma／Fierz／颜色、Ward 代数、局部作用量与变分、实际场及区间积分、幂计数、约束与 ghost | 继续多维边界／电荷、顶角、高阶 IBP/EOM 冗余、传播重场与一般匹配；新增点场替换与实际一阶边界桥已专项通过、协变／分级场；一维剖面与辅助场消元均不代表这些任务已完成。 |
| 统计与非平衡理论 | 有限 Gibbs／量子热态与静态响应、详细平衡、Markov、谱隙／收敛证书 | 有限时间常值扰动已可求导；实际有限源自洽已编译集成；继续一般驱动、频率读数、临界附近稳定性与非对易自洽。 |
| 对称结构与候选变形 | 结构常数与参数域、H²/H³、障碍、有限阶修正、ghost 对应 | 与目标物理模型、作用量、约束和物理观测量的解释桥。此方向已有成果可用，但不代表其它方向成熟。 |
| 符号／数值辅助推导 | 精确 Lie 证书；有理复矩阵残差、谱排除域及有效读数误差；Lean 审计 | 补齐可靠包络、更多谱／自洽／多项式证据与规模性能，并使结论持续绑定实际模型。 |
| 人与 AI 的探索协作 | Lean 目标、条件分支、已证／反驳／失败记录、修订复用、声明检索与完整下游审计 | 条件／约定语义检索、自动依赖影响提示、跨项目协作；模型修改仍需实际重验。 |

### 从新问题到研究结论：哪些步骤还需研究者手工完成

| 研究步骤 | 已验收功能能接收／产出什么 | 仍需完善的系统功能 | 全局待办 |
| --- | --- | --- | --- |
| 表达候选模型 | 有限矩阵、格点片段、参数模型或一阶多项式作用量，可表达相应前提 | 有限费米任意相互作用表与局部嵌入已接入；继续稀疏后端及单位、场与态的表述转换 | R01/R03 |
| 整理并推导 | 代数恒等式、形式及实际场局部变分、区间作用量／流平衡、有限收缩递归及非交换逐阶操作；任意有限模式真空的任意长度矩与表达式读数 | 玻色／混合分级正规序、一般实际态的 Wick 桥、全局逆坐标与高阶／导数依赖替换；多项式点变换的实际 Euler／变分流及显式正则域已接入 | R04/R05/R07 |
| 得到物理预测 | 有限热态、静态及有限时间响应、有限采样 Fourier 重构、局部流；有限谱排除域、消元及有误差界的有效读数 | 多点动力学关联、一般驱动／连续频率、局部／量子自洽、更广低能适用域及传播重场匹配；有限源自洽已接入，已通过完整发布验收 | R06/R08/R10 |
| 比较候选理论 | 参数重索引、部分换基和模型映射、Lie／ghost 候选变形可复用 | 跨表述比较观测量，跟踪对称破缺、假设变化和不同近似方案的关系 | R01/R09/R12 |
| 评估近似是否可信 | 条件性残差传播、Lie 精确证书；有理复矩阵残差可产生逆与消元误差；区间残差可约束实际 Noether 流累计变化 | 扩展不确定实输入、通用区间／多项式及谱包络；现有有理 Gibbs 数值证书已自动提供实际残差，继续核验规模性能 | R08/R10/R11 |
| 保存探索过程并复验 | 原目标绑定、条件分支、反例与失败、覆盖合并、版本历史和显式证明复用 | 条件检索、自动变更影响分析和跨项目依赖重验 | R12 部分交付 |

这里的缺口有三种处理方式：已有公共功能优先补连接；固定模型或仅给定结论的接口补实际操作；尚无公共实现的环节再新建。凝聚态侧首先减少“耦合表到多体算符、态到关联、约化到有效读数”的人工步骤；高能侧首先减少“场内容到作用量操作、对称到物理约束、逐阶消元到算符匹配”的人工步骤。两侧共同消费参数域、证据和探索工作流。

更新本清单时，应记录新的公共输入、操作、输出、适用条件与验证入口。案例增加只更新案例覆盖；只有操作及其相邻桥实际交付后，才提升对应能力状态。

## 8. 公共功能指南与证据入口

能力范围由上表维护；用法与前提在专题指南中展开，实际检查命令、计数与历史批次统一见 [VERIFIED](../VERIFIED.md)。下面按研究操作导航，不再复制各批验收记录。

| 公共操作 | 使用入口 | 当前物理边界与对应交付 |
| --- | --- | --- |
| 场替换与源传输 | [场替换指南](field-redefinitions.md) | 一阶实交换场、多项式点替换、完整梯度 Jacobian、组合／显式逆、实际 Euler／变分流、正则域内方程对应及区间作用量导数；全局逆坐标、导数替换和高阶 EOM 仍缺。R07。 |
| 实际场与作用量 | [实际场、作用量与边界](action-evaluation.md) | 实际光滑场、区间第一变分、Noether 平衡及残差预算；多维边界、电荷、解存在和协变／分级场仍缺。R07/R09。 |
| 费米表示与真空关联 | [有限费米模型](fermion-models.md) | 任意有限模式 CAR、复配对与 Nambu 桥；实际空占据密度、任意长度探针矩、接触项及词／表达式读数。一般 Gaussian／热态、时间排序和基态选择仍缺。R03/R05。 |
| 相互作用表达式 | [费米算符表达式](fermion-words.md) | 任意词长正规化、符号系数、伴随、单射模式嵌入和实际表示；玻色截断、一般相互作用换基及大系统性能仍缺。R03/R04。 |
| 源、热态与响应 | [源响应](source-response.md)、[量子响应](quantum-response.md) | 有限静态、非对易 Gibbs 导数、有限时间 Kubo 型响应和给定网格的 Fourier 重构；一般驱动、连续频率及输运极限仍缺。R05/R06。 |
| 自洽与误差 | [自洽指南](self-consistency.md)、[数值 Gibbs](numerical-gibbs.md) | 从有限实源输入界导出全局压缩域、解／读数误差和驻值桥；有理指数包络已提供实际数值残差；临界／多分支、量子闭合和原模型的闭合误差仍缺。R10/R11。 |
| 消元与物理证书 | [有效理论](effective-theory.md)、[矩阵证书](matrix-certificates.md) | 精确分块、逐阶操作、有理复矩阵到实际逆、有限谱域和有效读数误差；新增混合二次传播重场的有限展开、源／读数与区间残差／端点关系；可靠舍入、稳定子空间、传播重场 Green 函数、非二次／圈匹配仍缺；二次传播重场的有限阶／区间操作已接通。R08/R11。 |
| 有限格点 Ward／RG | [有限格点指南](finite-lattice-rg.md) | 权重对称到单位 Jacobian 插入、blocking 缺陷到归一化读数与组合预算；耦合投影、连续尺度流和热力学极限仍缺。R13/R14。 |
| 假设分支与模型修订 | [探索工作流](exploratory-workflow.md) | 原目标绑定、条件分支、失败／反例、覆盖证明和显式修订；条件语义检索、自动影响分析与跨项目依赖重验仍缺。R12。 |

2026-10-08 的真空增量由 [FermionVacuum](../LeanPhy/FieldTheory/FermionVacuum.lean) 提供：`vacuumState n` 构造实际密度并证明消去条件，`vacuumOfOrder` 适配命名模式，`twoPoint`／`fourPoint` 从条件推导关联，`certificate` 自动生成有序四点证书。计算公式只需收集探针系数；显式占据表示的维度仍为 `2^n`，大系统性能须另行测量。该增量提升 C05/C07/C12 和 R05，当前完整发布检查待完成。

任意点数扩展由 [FermionicMoment](../LeanPhy/FieldTheory/FermionicMoment.lean) 的带符号位置递归与 [FermionVacuumWick](../LeanPhy/FieldTheory/FermionVacuumWick.lean) 的实际态证明提供。`moment_eq` 不要求输入 Wick 等式；`word_expectation` 和 `expression_expectation` 接现有相互作用层。C05/C09/C12 的有限真空链已延长，R05 仍缺一般 Gaussian／热态和时间排序；直接枚举配对不是大点数性能保证。

R08 本批提升 C10/C14/C18/C19：重场动能实际作用于轻场／背景 jet，质量与动能次序保留；`density_perturb` 产生方程，`action_matching` 和 `action_error` 消费实际区间积分。其误差目标是已替换作用量与匹配作用量之差，Green 函数和精确低能解仍需另证。详见[有效理论指南](effective-theory.md)。
