# 假设分支、反例与模型修订

`LeanPhy.Workflow.Exploration` 提供独立于具体领域的研究问题与分支操作。它服务于这样的过程：提出适用范围较广的候选结论，先证明某些参数域，保留失败尝试与反例，再修订模型、目标或适用域。模块直接绑定 Lean 中的数据和命题；物理计算由已有的 Hamiltonian、作用量、消元等模块提供。

## 问题和分支的实际含义

`Question α` 保存参数／模型数据类型 `α`、基本适用域 `domain : α → Prop` 和目标 `target : α → Prop`。数据可以包含耦合表、场内容、探针或边界条件。问题的完整答案是：

```text
∀ x, domain x → target x
```

每个 `Condition α` 都有实际谓词，`Branch Q` 保存附加条件列表。分支的证明对象是：

```text
∀ x, Q.domain x → (分支中的所有条件在 x 成立) → Q.target x
```

因此，不需要先证明研究假设对所有参数成立，就能在该假设下继续推导。`AssumptionWitness` 则仍表示已经持有证明的假设，两者用途不同。条件名称、版本号、物理描述和问题来源都是供人阅读的元数据；重用相同名称不会使不同命题相等。

| 操作 | 必须提供的证据 | 得到什么 |
| --- | --- | --- |
| `Branch.refine` / `restrict` | 父分支证明 | 在更强条件下复用结果 |
| `Branch.discharge` | 分支证明，以及基本域蕴含全部附加条件的证明 | 原问题的完整答案 |
| `Branch.joinSplit` | 条件成立、不成立两个分支的证明 | 父分支证明 |
| `Branch.cover` | 每个子分支的证明，以及子分支覆盖父域的证明 | 父分支证明；支持重叠和一般指标类型 |
| `Branch.transport` | 新域包含于旧域，以及旧目标推出新目标的证明 | 模型／目标修订后的条件性结果 |
| `Branch.reindex` / `reindex_proof` | 参数／模型代入映射和旧证明 | 实际谓词随代入映射一起变换 |
| `Counterexample.refutes` | 一个满足基本域和分支条件、却违反目标的输入 | 该分支目标的否定 |

一般参数类型 `α` 不要求 JSON 编码器；报告不会自动序列化反例输入或 Lean 命题。具体反例输入保存在 Lean 的 `Counterexample` 声明中，候选账本消费它产生目标否定的证明。需要数据交换时，应另提供明确的模型编码。

分支可能没有任何可行输入。此时条件性定理可能是空真的，不能据此声称存在物理模型。`Branch.Feasible` 可另外证明分支非空；空分支也不能覆盖一个有输入的原始域。

## 从物理操作建立条件性任务

下面用已有的多项式辅助场消元操作建立可复用问题。`V` 和 `J` 是任意光场势及源；零重场系数仍包含在原始候选域中。

```lean
import LeanPhy.Workflow.Exploration
import LeanPhy.FieldTheory.HeavyFieldElimination

open LeanPhy.Workflow LeanPhy.Workflow.Exploration
open LeanPhy.FieldTheory.HeavyFieldElimination

namespace MyElimination

def question (V J : MvPolynomial Unit ℝ) : Question ℝ where
  name := "heavy Euler equation"
  revision := "v1"
  statement := "elimination solves the heavy equation"
  domainDescription := "all real quadratic coefficients"
  source := "HeavyFieldElimination.eliminated_heavy_equation"
  domain := fun _ => True
  target := fun m => eliminate m J (MvPolynomial.pderiv none (action m V J)) = 0

def invertible : Condition ℝ :=
  ⟨"invertible coefficient", "m is nonzero", fun m => m ≠ 0⟩

def branch (V J : MvPolynomial Unit ℝ) : Branch (question V J) :=
  (Branch.root (question V J)).refine "nonzero" invertible

theorem branchProof (V J : MvPolynomial Unit ℝ) : (branch V J).Goal := by
  intro m _ hc
  exact eliminated_heavy_equation m
    (hc invertible (by simp [branch, Branch.refine])) V J

def notebook (V J : MvPolynomial Unit ℝ) : Notebook (question V J) :=
  ⟨[(Candidate.propose (branch V J)).prove (branchProof V J)], []⟩

example (V J : MvPolynomial Unit ℝ) :
    ((notebook V J).toPackage "elimination" "auxiliary fields").obligationCount = 1 := rfl

end MyElimination
```

`toPackage` 总会登记原始量化目标。它不会因为所有候选都有结果，或因为已证明非零参数分支，就移除零参数处的任务。`Notebook.complete` 必须收到 `Question.Answer`，并调用现有的按目标索引关闭机制，保留原命题及其证明。

## 保留探索过程

`Candidate` 的每次 `prove`、`refute`、`fail` 或 `record` 转换都会保留此前结果。`Notebook.Ref` 指向具体不可变账本中的一个位置；`Notebook.record` 所需证据的类型从该位置读取，不能通过重名分支替换目标。

| 报告中的 outcome | 含义 |
| --- | --- |
| `pending` | 没有登记结果 |
| `branch_goal_proved` | 已证明包含附加条件的实际分支命题 |
| `branch_goal_refuted` | 已证明该分支命题的否定；不等于证明原正向目标 |
| `attempt_failed` | 记录一次失败尝试及原因，没有肯定或否定命题的逻辑效力 |

`Notebook.revise` 接受新的问题，允许参数类型、模型、域和目标改变。所有旧记录保留原命题与证据，并标记 `historical` 和 `superseded_by`；新版本从待证根分支开始。它不会自动判断某一变化是否影响证明。对已知仍适用的结果，可用 `transport` 或 `reindex_proof` 明确复用。

完成整个问题时，报告保留先前分支为历史记录，并加入实际原目标的已证记录。旧反例仍属于旧域／旧目标，不会被改写成新版本的反例。

## 两条物理链的集成验收

[ExplorationResearch](../LeanPhy/Examples/ExplorationResearch.lean) 接入了以下现有物理操作：

- 凝聚态复配对：实序参量分支证明旧实配对形式适用，`Δ = i` 给出该形式不能覆盖一般复配对的反例。修订使用带共轭的 Hermitian 块，直接复用公共平方关系，得到对任意复相位成立的新目标。
- 高能辅助场：非零二次系数分支证明代数重场方程被消元满足，零系数、非零源给出反例。把基本域修订为非零系数后，通过域与目标传输复用旧证明。
- 完整参数覆盖：源选择为 `J = m` 时，零系数分支也能直接证明；合并零与非零两支后关闭完整参数域的目标。

这些结论没有建立传播重场展开、稳定性或大质量近似；非零系数仅是代数可逆条件。

```lean
import LeanPhy.Examples.ExplorationResearch

open LeanPhy.Workflow.Exploration LeanPhy.Examples.ExplorationResearch

-- 反例和条件性结果不会关闭旧的正向目标。
example : pairingOpen.obligationCount = 1 := rfl
example : massOpen.obligationCount = 1 := rfl

-- 模型修订先产生新的待证根分支。
example : revisedPairing.candidates.length = 1 := rfl
example : (revisedPairing.toPackage "new question" "condensed matter").obligationCount = 1 := rfl

-- 有实际修订目标证明或穷尽分支覆盖之后才能关闭。
example : correctedPairing.Answer := corrected_pairing_answer
example : invertibleMassQuestion.Answer := invertible_mass_answer
example : regularizedQuestion.Answer := regularized_answer
example : coveredPackage.obligationCount = 0 := rfl
```

编译和报告：

```bash
lake build leanphy_exploration_client
lake exe leanphy_exploration_client --project-json
lake exe leanphy_exploration_client --strict
lake exe leanphy_exploration_client --closed --strict --project-json
```

默认报告含 5 个研究包、7 条已证命题和 2 个开放目标；其中负向结论的命题是原分支目标的否定。第三条命令应失败。`--closed` 选择已证明的三个修订／覆盖问题：3 条结论、0 个开放目标，可以通过严格检查。

现有包在没有探索记录时保留原 JSON 形状。有记录的包增加 `explorations` 数组；原有 `open_obligations`、`resolved_obligations`、`claims` 和严格检查继续使用同一研究项目。只导出声明时，声明描述也包含域和附加条件；最终数学含义仍以 Lean 命题为准。记录中的 `source` 是问题给出的来源元数据；实际逐项证明依赖由编译声明索引与全声明审计核对。

## 当前范围

该批提供证明绑定的分支、失败／反例区分、覆盖合并和显式修订复用。它不自动搜索条件，不从文本模型描述推断目标，不提供自动的跨项目变更影响分析，也不将账本变成不可篡改日志。给出求解算法、外部数值数据的正确性证书、连续极限或误差控制，仍是对应物理模块的工作。R12 因此是部分交付；完整声明审计与独立下游项目复验继续适用。
