# 独立研究公共层、目标绑定与声明检索

本批推进全局路线 S1，并接入 S2 的耦合作用量链。目标是让研究者登记准确的待证命题、独立导入所需操作，并找到现有定理。实现从另一份本地开发目录按模块整合，保留本仓库原有默认领域包、64 项精选目录、Lie／ghost 工具、完整声明审计和下游项目验证。

对待证条件和竞争模型，可使用新增的 [`Workflow.Exploration` 层](exploratory-workflow.md)，保存实际参数域、条件分支、反例、失败尝试和修订历史。`Entry.Research` 已导入它；`Workflow.Core` 仍可独立使用。分支完成调用下述原目标绑定机制。

## 研究义务的语义

`ExternalObligation` 现在保存 `target : Option Prop`。登记数学任务时使用 `addObligationWitness`，命题实际进入包内；`ObligationRef package` 引用该包中一个有效索引，其 `Goal` 从对应记录读取。关闭任务时不能重新指定同名命题，也不能用另一条相关结论的证明替代原目标。

```lean
import LeanPhy.Workflow.Core

open LeanPhy.Workflow LeanPhy.Mathematics

def base := TheoryPackage.empty "residual study" "approximation"

def target (x : ℝ) : ExternalObligationWitness where
  metadata :=
    { name := "exact residual"
      statement := "the exact state has zero residual"
      source := "model" }
  proposition := ErrorCertificate x x 0

def pending (x : ℝ) := base.addObligationWitness (target x)

def checked (x : ℝ) :=
  (pending x).resolveObligation (base.addedObligationRef (target x))
    "residual proved" "zero residual" "ErrorCertificate.of_eq" [] []
    (ErrorCertificate.of_eq rfl)
```

这段代码演示目标生命周期，其零误差命题不代表已经认证了数值近似。真正的非零模型残差需另行证明后才能关闭相应任务。

关闭只删除该索引处的一条记录，`resolvedObligations` 保存原始目标及其证明。同名的其它任务仍保持原状；重复名称本身继续由账本诊断。`resolveObligationWitness ref ... derive proof` 可在证明目标后导出一个后续结论，但目标证明仍保存在历史中。

文本任务的 `target` 为 `none`，其 `Goal` 为 `False`，因此不能被普通相关定理关闭。`addObligationEvidence` 允许记录有限结果、局部界等证据，并保留该任务。将文本任务形式化，需要在模型声明中明确命题及其解释；Lean 不验证自然语言文字是否准确表达了这个命题。

包和引用是普通 Lean 值。修改包后需要构造合适的新引用；没有运行时命题相等判定。这也不是不可篡改日志：手工重建一个包可以丢弃记录。上述保证属于这些构造 API 与其类型，并不声称约束用户任意构造所有元数据。

## 导入与兼容

| 入口 | 用途 |
| --- | --- |
| `LeanPhy.Workflow.Core` | 账本、项目、目标、历史与报告；不导入默认物理包 |
| `LeanPhy.Workflow.Exploration` | 假设分支、覆盖证明、反例、失败历史与显式修订复用；不导入默认物理包 |
| `LeanPhy.CLI.Core` | `runWithCatalog manifest args entries`，目录默认空；只报告调用方的项目 |
| `LeanPhy.Library.Core` | 带证明目录条目及 `searchIn`、`namesIn`、`renderJsonIn` |
| `LeanPhy.Workflow.DefaultPackages` | 原有 default／extended／broad 物理包及其 manifest |
| `LeanPhy.Workflow`、`LeanPhy.CLI`、`LeanPhy.Library` | 保留原入口、CLI `run`／`runDefault` 与 64 项精选目录 |

`Entry.Research` 使用公共核心并继续导入 `LeanPhy.Verification`。`leanphy_init` 生成项目时也使用公共核心，仍复制完整下游验证器，检查所有本地源模块、实际编译产物及传递公理依赖。独立客户端的帮助信息不再广告其不支持的内置 profile 开关。

需要迁移的调用：

- 旧 `resolveObligation name membership ... arbitraryProof` 改为先登记命题，再传 `ObligationRef` 与其 `Goal` 的证明。旧 witness 按名称匹配的形式同样移除。
- `ExternalObligation` 因含有命题不再派生 `Repr`；使用报告函数输出运行时元数据。
- 原 API 的定义模块现在可能是 `Workflow.Core`、`Workflow.DefaultPackages` 或 `Library.Core`；命名空间保持不变。按定义模块审计或检索的客户端应更新筛选。
- JSON 保留原字段，新增开放义务的 `kind` 和包的 `resolved_obligations`。严格模式仍拒绝开放义务。
- 只导入 `Entry.Research` 的客户端若需要 `defaultProject` 等内置对象，应显式导入 `Workflow.DefaultPackages`。
- 旧 `Classical.fieldEulerLagrangeResidual` 已改用全分量 `fieldTimeDerivative`。旧 `fieldTotalDerivative x` 仍是单分量导子，不能作为耦合系统的总时间导数。详见[变分指南](variational.md)。

## 编译环境中的声明发现

```bash
lake build leanphy_index
lake exe leanphy_index --module LeanPhy.Condensed --kind theorem
lake exe leanphy_index --query 'euler quadratic'
lake exe leanphy_index --query 'ghost invariant' --json
```

索引含真实名称、Lean 类型和前提、定义模块、源码行、注释、公理依赖及证明项中对 `LeanPhy` 声明的直接引用。类型／证明／定义体的引用列表只筛选库内名称，不包含所有 mathlib 引用，也不是传递依赖图。检索在本地执行，忽略大小写并要求所有空格分隔的词匹配；不把字符串结果转换成证明。

内置 `IndexMain` 覆盖库源模块的导入闭包，包括总入口未导出的客户端模块。回归检查该闭包与实际库源码集合，防止新增模块漏入。索引只展示 `LeanPhy` 命名空间中有源码位置的公开安全声明，排除私有项、无位置的生成辅助声明及索引自身；完整证明审计仍由 `Verification` 独立承担，覆盖范围更宽。

用户可用 `physics_index myDeclarations` 为当前导入的 LeanPhy 声明生成索引。用户自有命名空间仍使用普通 Lean 导航及研究结论目录。源码改动后必须重建索引；直接执行旧二进制不会读取新的 Lean 源码。实际类型和证明引用比人工标签更可靠，但它们不等于研究层的完整依赖解释或物理适用性判定。

## 验证入口

```bash
lake exe leanphy_obligation_client --strict --project-json
lake exe leanphy_obligation_client --open --project-json
lake exe leanphy_obligation_client --duplicate --project-json
lake exe leanphy_variational_client --project-json
bash scripts/verify.sh
```

义务客户端检查精确目标关闭、文本证据保留、同名任务只关闭一条及历史输出；变分客户端保留光滑解与积分电荷的开放义务。负向回归拒绝目标替换、错误包引用、缺失目标证明，以及变分中漏边界、漏耦合、丢高阶导数和将非零误差当成精确守恒的操作。

当前仍缺全局物理约定互接、源与量子动力学响应、通用逐阶消元、一般数据证书核验，以及连续物理前提。公共层的改进不使这些任务自动完成；当前状态与后续顺序见[能力清单](capabilities.md)和[全局路线](roadmap.md)。
