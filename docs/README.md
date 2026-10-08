# LeanPhy 文档导航

这里按文档职责组织项目说明。根目录 README 负责项目定位和当前版本快照；本页负责索引；专题文档说明接口与边界；`VERIFIED.md` 只保存实际运行过的验收证据。

## 先看这些

| 文档 | 用途 |
| --- | --- |
| [能力清单](capabilities.md) | 按 C01–C28 维护源码入口、适用范围和仍缺的功能。 |
| [建设路线](roadmap.md) | 按 T0–T6、R01–R14 管理优先级、交付依赖和阶段出口。 |

## 系统和研究工作流

- [项目文件布局](project-layout.md)：库、入口、客户端、脚本、数据和文档的职责。
- [架构说明](architecture.md)：公共核心、物理层、证据层和导入边界。
- [研究公共层](research-core.md)：目标绑定、证明历史和声明检索。
- [探索工作流](exploratory-workflow.md)：假设分支、反例、失败和模型修订。
- [研究项目验证](research-project-verification.md)：把研究草稿接入独立审计。
- [声明审计](declaration-auditing.md)：公理、私有声明和传递依赖检查。

## 面向理论物理的专题接口

### 凝聚态和统计物理

- [有限费米模型](fermion-models.md) · [费米算符表达式](fermion-words.md)
- [量子响应](quantum-response.md) · [源响应](source-response.md)
- [自洽与误差](self-consistency.md) · [能带和几何缺口](capabilities.md)
- [有限格点、Ward 与 RG 误差](finite-lattice-rg.md)

### 高能、场论和规范理论

- [变分与作用量](variational.md) · [实际场与边界](action-evaluation.md)
- [场替换](field-redefinitions.md) · [有效理论](effective-theory.md)
- Lie／ghost／变形的有限代数接口见[能力清单](capabilities.md)和[架构说明](architecture.md)；
  v1.1 不再附带这些专题的外部符号生成器。

### 可核验的外部计算

- [指数与 Gibbs 数值证书](numerical-gibbs.md) · [矩阵证书](matrix-certificates.md)
- 外部候选数据只能通过 Lean 侧证书进入；保留的生成器和审计边界见
  [能力清单](capabilities.md)与[声明审计](declaration-auditing.md)。

## 验收

- [验收记录](../VERIFIED.md)：唯一的发布验证记录，包含实际命令、证据和限制。
专题指南描述的是局部接口，不能替代能力清单中的全局边界。新增功能时，先更新能力清单和建设路线；只有实际完成相应检查后，才更新验收记录。
