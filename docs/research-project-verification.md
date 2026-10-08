# 从研究草稿到可追溯的项目验证

`leanphy_init` 生成普通 Lean 项目，并附带独立的项目验证器。它会构建并审计
本地全部研究模块，包含未被 `Research.lean` 导入的草稿和可执行文件的 `Main` 模块。
验证完成后才输出项目账本；数学假设和未完成的物理解释义务仍然保留。

## 新建项目

在 LeanPhy 仓库中运行，将依赖路径改为实际的本地路径：

```bash
lake exe leanphy_init ../MyPhysics \
  --name my_physics --profile research \
  --leanphy-path ../Lean_PHY
cd ../MyPhysics
bash scripts/verify-leanphy.sh
```

`--leanphy-path` 相对于新项目目录，必须指向已有的 LeanPhy 仓库。
创建时会从该仓库复制 `scripts/audit_project.py`，因此验证器可以和研究源码一起保存、
版本管理和审阅。无需额外 Python 包，但需要 Python 3.11 或更高版本。
已有非空项目默认不会被覆盖；显式使用 `--force` 时只替换模板生成的文件。

初始项目包含 **0 条研究结论**和 1 条连续模型衔接义务。
审计通过只表示所检查声明的公理依赖符合规则，不会把空模板变成已完成的物理论文。

## 加入真实推导和候选计算

在 `Research.lean` 中写普通 Lean 定理，并把它的证明传给
`package.addTheoremWithAssumptions`。例如导入 `LeanPhy.Quantum.Pauli` 后可以使用：

```lean
theorem pauli_product : LeanPhy.Quantum.pauliX * LeanPhy.Quantum.pauliY =
    Complex.I • LeanPhy.Quantum.pauliZ := LeanPhy.Quantum.pauliX_pauliY
```

模板保留文件末尾的 `#leanphy_audit_module`，用于编辑时尽早发现问题。
项目级验证会重新导入编译后的完整文件，因此写在这条命令之后的声明也会被检查。
`Main.lean` 中的声明同样会被检查。

外部计算可以作为候选数据进入研究项目，但 v1.1 不再随库发布旧的
SymPy/Lie 生成器或其专题输入。当前保留的矩阵和 Gibbs 证书脚本只接受
精确有理数据；它们生成的 Lean 文件仍须由项目构建并通过 `CertificateChecker`
的 soundness 定理。原始计算报告仍然标为候选，项目审计只记录具体 Lean
文件是否通过检查。把候选定理加入研究账本仍需要显式导入模块并注册相应
证明，审计不会自动创造账本结论。

## 记录可复查的验证结果

每次使用新的输出路径：

```bash
bash scripts/verify-leanphy.sh \
  --report /tmp/my-physics-audit.json \
  --log /tmp/my-physics-audit.log
```

报告包含源码清单、源文件和构建配置哈希、实际编译产物路径及哈希、Lean 版本、
验证器哈希、审计数量和依赖清单。编译失败、禁止的公理依赖、验证期间的文件变化、
超时或缺失审计结果均不会写出成功报告。已有报告和日志不会被覆盖。

这里的 `project_axiom_audit_passed` 是编译与依赖审计状态，和研究账本的
`VERIFIED-CONDITIONAL` 等状态分开。项目仍有物理解释义务时，账本严格模式仍会拒绝
将它标为完全验证。报告是一次本地运行的可追溯记录，不是数字签名或新的数学定理。

## 源码范围与模块身份

验证器从 `lakefile.toml` 的包、库和可执行文件 `srcDir` 字段确定源码目录，枚举其中
所有 `.lean` 文件。新增文件必须属于 Lake 声明的库或可执行文件；无法构建的文件会导致失败，
不会被静默跳过。默认忽略隐藏目录、`.lake`、`.git`、`.venv`、`__pycache__` 和根目录的
`lakefile.lean` 构建配置。所选源码目录和完整文件清单会记录在报告中。

自定义 `lakefile.lean` 或需要明确选择源码目录时：

```bash
python3 scripts/audit_project.py --project-root . --source-dir src
```

`--source-dir` 可重复；对应的是 Lean 模块路径起点。嵌套源码目录使用最长匹配的路径起点。
目录必须位于项目内，不能通过符号链接重定向；同名模块、非法模块路径、缺失配置和空目录
选择都会报错。显式选择的目录之外的草稿不在该次审计范围内。

验证器使用 Lake 的**源文件目标**构建，并查询每个源文件的模块设置和实际 `.olean` 产物，
再把这些路径写入审计编译的 `--setup`。这一步避免项目 `Main` 与依赖库 `Main` 同名时，
按搜索路径导入了错误模块。互相冲突的依赖产物会导致失败。
使用 Lean 新模块系统的文件还会纳入其私有声明产物和相关 IR。

已安装的 Lean 工具链及依赖库编译产物仍在信任范围内。审计不会提供恶意代码隔离，
也不判断模型是否符合实验、连续极限是否成立或物理解释是否完成。
公理策略和已有全库审计的范围见[声明依赖审计指南](declaration-auditing.md)。
