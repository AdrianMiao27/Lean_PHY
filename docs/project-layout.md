# 项目文件布局

LeanPhy 现在按“可复用库—研究入口—可执行客户端—证据与文档”分层。目录的职责如下：

| 路径 | 职责 | 维护规则 |
| --- | --- | --- |
| `LeanPhy/` | 可复用 Lean 库，按 `Condensed`、`HighEnergy`、`FieldTheory`、`GaugeTheory`、`Quantum`、`StatMech`、`Mathematics` 等物理和数学边界分组。 | 新定理先放这里；不要把一次性报告或命令行解析混进库。 |
| `LeanPhy/Entry/` | 面向下游研究项目的轻量导入面。 | 只组合公共模块，不在入口中隐藏证明。 |
| `LeanPhy/Workflow/`、`LeanPhy/CLI/` | 研究账本、开放义务、报告和验证工作流。 | 与具体物理领域解耦。 |
| `LeanPhy/Examples/` | 可编译的研究包、回归和生成结果。 | 示例必须消费公共操作；生成文件集中在 `Examples/Generated/`。 |
| `Clients/` | 面向各研究包的 Lake 可执行薄客户端；文件名保留 `*Main.lean` 以对应目标名。 | 只负责调用入口和渲染结果；新功能不要复制到这里。 |
| 根目录 `Main.lean`、`Prototype.lean`、`Check.lean`、`ClientMain.lean`、`StrictClientMain.lean`、`Scaffold.lean` | Lake 默认 smoke、原型、账本、下游兼容和脚手架入口。 | 保持薄；不放领域证明。 |
| `examples/` | JSON 输入和外部计算报告。 | 输入可复现、报告可由脚本重新生成；不把报告当证明。 |
| `scripts/` | 声明审计、有限矩阵／Gibbs 证书、负向夹具和发布检查。 | 脚本只生成候选数据，Lean 内核检查证书；缓存留在 `__pycache__/`；旧的符号搜索生成器不再随 v1.1 发布。 |
| `docs/` | 能力清单、路线、专题指南和验收导航。 | 当前文档只保留一个能力入口、一个路线入口和一个验收入口；已删除的历史副本不再恢复。 |

根目录的六个基础入口是 Lake 与下游项目约定的一部分；其余客户端集中在 `Clients/`，不是第二套库。新增领域模块应遵循“库模块 → `Entry` 导入 → `Examples` 研究包 → `Clients` 薄客户端”的路径。新增专题文档先挂到 [文档导航](README.md)，再在[能力清单](capabilities.md)和[建设路线](roadmap.md)登记范围与缺口。
