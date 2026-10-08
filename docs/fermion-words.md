# 费米算符表达式、正规序与相互作用

本批推进全局 R03/R04，连接 C07/C09 的模型构造与 C05/C13 的实际有限态和动力学。输入是一张有限的“系数、算符字”表，允许任意词长、模式数和相互作用阶数；无需先展开占据空间矩阵。

## 公共操作和物理含义

| 模块 | 输入与输出 | 保证 |
| --- | --- | --- |
| [FermionWord](../LeanPhy/FieldTheory/FermionWord.lean) | 任意升降算符字 → 带整数系数的正规序展开 | 在任意复 CAR 表示中保持算符值；每项严格排序，保留收缩项与 Pauli 消去。 |
| [FermionPolynomial](../LeanPhy/FieldTheory/FermionPolynomial.lean) | 一般交换环上的耦合表 → 乘积、对易子、伴随、同类项合并与正规化 | 系数经显式环同态解释为复耦合；正规化差为零可证明原算符相等。 |
| [FermionEmbedding](../LeanPhy/FieldTheory/FermionEmbedding.lean) | 局部模式表、单射标签赋值 → 任意有限系统中的恒等式 | 允许改变模式顺序；独立模式不能映射到同一标签。 |
| [InteractingFermion](../LeanPhy/FieldTheory/InteractingFermion.lean) | 表达式、实际 CAR 占据表示与系数赋值 → 多体算符、热态、演化导数 | 复用实际有限表示和酉演化；带证明的 Hermiticity 保证物理 Hamiltonian。 |

`Letter ι` 的创建算符在前、湮灭算符在后，各块按调用者的 `LinearOrder ι` **升序**排列。外部工具可能采用不同顺序；例如 OpenFermion 的约定使用降序模式，导入时需要重新正规化。[OpenFermion 官方正规序说明](https://quantumai.google/reference/python/openfermion/transforms/normal_ordered)。这里没有直接导入其数据格式或依赖其计算结果。

`normalize` 和 `compile` 给出与原算符**相等**的 CAR 重写，包括收缩常数；它们不表示把收缩直接删去的冒号操作，也不执行真空能减除。伴随同时共轭系数、颠倒算符顺序并交换升降标记。`withAdjoint p = p + p†` **没有隐含的 1/2**，耦合计数由输入表负责。

## 检查一个可复用的局部恒等式

下面证明适用于任意复 CAR 表示；`decide` 在 Lean 内核中核验有限整数数据，`eq_of_compile_sub_eq_nil` 将它解释为实际算符恒等式。没有 `native_decide` 或外部计算公理。

```lean
import LeanPhy.Entry.Condensed

open LeanPhy.FieldTheory FermionWord FermionPolynomial

example {A : Type} [Ring A] [Algebra ℂ A] (M : MultiModeCAR (Fin 2) A) :
    FermionPolynomial.eval (Int.castRingHom ℂ) M
      (term 1 [ann 0, cre 0]) =
    FermionPolynomial.eval (Int.castRingHom ℂ) M
      (sub (scalar 1) (term 1 [cre 0, ann 0])) :=
  eq_of_compile_sub_eq_nil (Int.castRingHom ℂ) M _ _ (by decide)
```

`eq_of_local_certificate` 进一步接受 `g : Fin k → ι` 及其单射证明，把局部证书用于更大的系统。映射不要求保序；目标系统按自己的顺序再次正规化。若两个局部模式被合并，它们之间的 CAR 前提发生改变，该接口不能直接复用原证书。

这里的证书保证是单向的：正规化差为零可证明相等。非零输出或检查失败本身不证明某个表示中的算符不等，也不能作为探索账本中的正式物理反例；后者需要实际表示、态或读数上的不等证明。当前没有把正规形完备性或表示忠实性作为隐含前提。

## 任意相互作用接到实际态

一般系数环允许保留符号参数，`eval f M` 中 `f : R →+* ℂ` 显式完成参数赋值。可执行的 `compile` 还需要系数相等的判定；整数等精确数据可以用 `decide`，一般复参数可通过 `eval_normalOrder` 消费不依赖系数判等的正规序结果。任意矩阵元或符号参数系统的自动求解仍不是这个接口的功能。

```lean
import LeanPhy.FieldTheory.InteractingFermion

open LeanPhy.FieldTheory FermionPolynomial FiniteFermion

example (n : ℕ) (p : Expression ℂ (Fin n)) :
    (InteractingFermion.operator (modes n) (RingHom.id ℂ) (withAdjoint p)).IsHermitian :=
  InteractingFermion.withAdjoint_hermitian (modes n) (RingHom.id ℂ) (fun _ => rfl) p
```

`InteractingFermion.thermalState` 将任意已证 Hermitian 的有限相互作用接到已有的精确 Gibbs 密度。`expectation_normalOrder` 保持任意实际密度态中的期望，不要求态为 Gaussian。

`observable_derivative_of_certificate` 接受 Hamiltonian `H`、探针 `O` 和候选方程 `D`。内核核验 `compile ([H,O] − D) = []` 后，得到实际演化 `U(t) O U(−t)` 在 `t=0` 的导数 `i D`，其中 `U(t)=exp(+itH)`、ℏ=1；`H` 的 Hermiticity 另有证明。`expectation_derivative_of_certificate` 把同一结论接到实际初态读数。该证书不自动把零时刻方程升级成闭合的有限时间动力学或平均场方程。

`FermionVacuumWick` 进一步提供指定实际真空中的表达式读数：`vacuumValue p` 在系数环中用整数词矩求和，`expression_expectation f p` 证明该结果经参数赋值后等于实际 trace；`compiled_expectation` 允许先消费已有 CAR 正规化。完整 API、接触项与可编译用法见[任意点数真空关联](fermion-models.md#任意点数接触项与表达式读数)。它可读出相互作用的插入，仍须另证目标态与所用参考真空之间的关系。

## 验证与探索边界

[研究客户端](../LeanPhy/Examples/FermionWordResearch.lean) 有 7 条结论和 3 类开放义务。它检查可变模式数和任意复相互作用、实际热态，以及 `n₀n₁` 的对易子产生的三次算符项和真实演化导数。局部恒等式可以嵌入任意互异模式。

```bash
lake build leanphy_fermion_word_client
lake exe leanphy_fermion_word_client --project-json
lake exe leanphy_fermion_word_client --strict
python scripts/test_fermion_words.py
```

严格模式应失败：一般实际态的 Wick 定理、玻色截断边界、大系统性能与极限仍未完成。新增拒绝检查覆盖收缩常数、交换符号、Pauli 消去、伴随顺序／共轭、模式碰撞和相互作用方程的系数。

Python 专项测试用不同的冒泡重排算法生成比较数据，并独立计算占据态上的作用。覆盖两个模式长度 0–4 的全部 341 个词、每词 4 个初态；另有 68 个词的 Lean 证书、1024 个可选标签中长度 32 的有序词、零模式和复伴随。后者只验证符号操作不枚举占据矩阵，不能当作 1024 模多体计算已具备可行性的证据。

当前实现使用有限列表，同类项线性查找；收缩分支可能快速增长。尚无通用表达式规模界、高效哈希／稀疏后端、完整正规形唯一性或证书检查完备性定理。R05 已在独立模块中构造任意有限模式真空并推导一般线性探针的任意点数线性探针及整数词／符号表达式读数，但一般 Gaussian／热态 Wick、玻色截断修正与连续场分布仍需独立建设。R03/R04 得到通用有限费米操作；R05、R08、R10 和全局其它任务保持可见。完整发布状态见 [VERIFIED](../VERIFIED.md)。
