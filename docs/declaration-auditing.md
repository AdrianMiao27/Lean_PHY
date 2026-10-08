# 声明、公理依赖与验证范围审计

`lake build` 通过并不自动意味着所有结论都只依赖项目允许的基础公理。
例如 Lean 可以接受带 `sorry` 的文件并产生警告，也允许用户声明额外公理。
LeanPhy 的依赖审计检查实际声明及其传递依赖，允许的基础仅为
`propext`、`Classical.choice` 和 `Quot.sound`。

## 在自己的研究文件中使用

```lean
import LeanPhy.Verification

theorem conditional_result (P : Prop) (h : P) : P := h

#leanphy_audit_module
```

将命令放在文件末尾。它检查当前模块中**位于命令之前**的所有声明，包含私有声明、
匿名例子生成的声明，以及定义在其他命名空间中的声明。显式定理假设仍然是合法假设；
审计不替你证明 `P`，也不接受把 `P` 改成未经证明的全局公理。

对于生成的候选文件，可在顶部加上 `import LeanPhy.Verification`，在末尾加上
`#leanphy_audit_module`，再编译整个文件。JSON 中的候选状态不能替代该检查。
编译和审计结果适用于实际检查的文件版本，后续修改需要重新检查。

从导入模块审计研究结果：

```lean
import MyResearch.Results
import LeanPhy.Verification

#leanphy_audit_modules [MyResearch]
```

这里的 `MyResearch` 是**定义模块**的前缀，并非声明的命名空间。命令检查已加载的
`MyResearch` 及其子模块中的全部声明；没有导入的文件不在这个命令的检查范围内。
`MyResearchOther` 不会被当作它的子模块。模块未加载或声明选择为空都会报错。
即使额外公理来自其他库，只要被所选声明的类型或证明间接依赖，也会被拒绝。

`#leanphy_audit_library` 对当前已加载的全部 `LeanPhy` 模块使用相同规则。
`LeanPhy.Entry.Research` 和总入口 `LeanPhy` 均导出这些命令。

新建项目现在自动携带项目验证器。它枚举本地源码，并绑定 Lake 实际构建的模块产物，
也会检查未导入草稿、可执行入口和写在内联审计命令之后的声明；详见
[完整研究项目验证](research-project-verification.md)。

## 发布检查覆盖每个源文件

```bash
python3 scripts/audit_library.py \
  --report /tmp/leanphy-library-audit.json \
  --log /tmp/leanphy-library-audit.log
```

此命令从当前源码枚举 `LeanPhy.lean` 和 `LeanPhy/**/*.lean`，构建并显式导入每个模块，
因此未被总入口重新导出的模块也会接受检查。它是 `scripts/verify.sh` 的必需步骤。
已有报告和日志不会被覆盖。

报告包含实际声明数、定理数、私有声明数、定义模块、所用基础公理、Lean 版本、
源文件及构建配置哈希、此次审计文件和日志哈希。仅在构建和审计成功，且检查前后源码
一致时写出成功报告。超时、编译失败、空结果或公理策略改变都不能产生成功报告。

需要用另一目录构建时，显式传入 `--build-root`。工具会在检查前后核对该目录的完整
库源码清单、工具链配置、Lake 配置和依赖清单与源目录一致；新增、删除、修改文件均会导致失败。
默认使用当前项目源码，不自动选择其他目录。

## 本次修复的覆盖漏洞

当前 `scripts/audit_library.py` 遍历完整环境，按声明所属模块选择，并拒绝空选择。回归测试先编译带问题的模块，
再在其他文件中导入审计，确认私有公理、外部命名空间、证明空洞、原生计算依赖和类型中的
传递依赖均不能逃过检查。独立的小项目还验证了未被总入口导出的源模块确实会被发布审计发现。

## 边界

审计命令是 Lean 元程序，报告是本次本地编译和依赖检查的记录，不是新的数学定理。
已安装的 Lean 工具链和导入依赖产物仍属于信任边界；此流程不提供恶意工具链隔离，
也不重新从零证明 Lean 内核正确性。源文件哈希用于追溯和一致性核对，不提供数字签名。

审计也不判断模型是否符合实验、不证明连续极限或收敛，不消除显式假设和研究报告中的
未完成义务。新增物理结论仍须有相应的数学证明和适用范围说明。
