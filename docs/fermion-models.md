# 有限费米模型：从耦合表到多体算符

后续公共连接见[有限量子响应](quantum-response.md)：实际时间导数、有限时间扰动和非对易 Gibbs 导数已接入。本文包含任意有限模式空占据真空的任意点数线性探针递归、符号表达式读数和有序四点证书；一般 Gaussian／热态、一般驱动、连续频率表示和时间有序 Wick 仍待完善。

本批对应全局能力 C04/C05/C07/C09，以及 R01/R03/R04 的首批公共操作。输入可以是任意有限模式标签和复耦合表；模式可以包含格点、轨道和自旋。库构造占据空间上的 CAR 算符，再将二次 Hamiltonian、Nambu 系数、换基与有限热态接在一起。

## 输入、操作和表示

| 输入／操作 | 公共 API | 输出及证明边界 |
| --- | --- | --- |
| n 个模式 | `FiniteFermion.modes n` | `Occupation n` 上的实际矩阵；空间维数为 `2^n`，CAR、伴随和宇称串由构造证明。 |
| 带物理标签的模式 | `FiniteFermion.ofOrder e`，`e : ι ≃ Fin n` | 顺序显式进入构造；`namedModes ι` 也提供默认有限枚举。 |
| 任意二次耦合 | `FermionBdG.Coefficients ι` | 正常块 `hᴴ = h`、配对块 `Δᵀ = -Δ` 是输入证明；单个模式的对角配对为零。 |
| 多体 Hamiltonian／热态 | `Representation.hamiltonian`、`thermalState` | 实际占据空间的 Hermitian 算符和归一化 Gibbs 密度；复用有限量子热态工具。 |
| 双线性正规排序 | `MultiModeCAR.antiNormal_eq` | 导出迹常数和交换后的符号；不是任意算符字的完整正规序算法。 |
| Nambu 桥 | `nambu_energy`、`nambu_equation` | 从实际 CAR Hamiltonian 推出能量恒等式与算符对易方程。 |
| 轨道换基 | `MultiModeCAR.rotate`、`Coefficients.rotate`、`quadratic_rotate` | 同时转换算符和系数后，多体 Hamiltonian 保持；Nambu 酉换基保持有限谱隙。 |
| 粒子—空穴与 Majorana | `particleHole`、`partner_equation`、`occupation_majorana` | 共轭与模式交换显式；Majorana 自伴性消费实际伴随关系。 |

构造按 Kronecker 乘积递归，每增加一个模式使用已有总宇称串。CAR 证明不逐项枚举整个矩阵。**这不等于已有稀疏求解器或可扩展的大系统数值实现**：将语义矩阵完全展开仍有指数规模；运行时谱计算与大规模性能另行验收。

## 任意耦合表的公共用法

下面的 `K` 可以由任意 Hermitian 正常耦合与反对称配对构造，所有证明复用同一接口。给定复跃迁时，共轭关系必须在 `K.normal_hermitian` 中成立。

```lean
import LeanPhy.Entry.Condensed

open LeanPhy.Quantum LeanPhy.FieldTheory.FiniteFermion
open LeanPhy.FieldTheory.FermionBdG

noncomputable def researchH (n : ℕ) (K : Coefficients (Fin n)) :=
  (modes n).hamiltonian K

noncomputable def researchState (n : ℕ) (K : Coefficients (Fin n)) (β : ℝ) :
    FiniteDensity (Occupation n) := (modes n).thermalState K β

example (n : ℕ) (K : Coefficients (Fin n)) : (researchH n K).IsHermitian :=
  (modes n).hamiltonian_hermitian K

example (n : ℕ) (K : Coefficients (Fin n)) (i : Fin n ⊕ Fin n) :
    ⟦nambu (modes n).car i, researchH n K⟧ =
      act K.matrix (nambu (modes n).car) i :=
  nambu_equation (modes n).car (modes n).adjoint K i

noncomputable def labeledH {ι : Type} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (order : ι ≃ Fin n) (K : Coefficients ι) :=
  (ofOrder order).hamiltonian K
```

这里的 Nambu 指标是 `ι ⊕ ι`，多体态指标是 `Occupation n`。例如三模式时分别有 6 和 8 个指标；它们的 Hamiltonian 和密度对象不能互换。有限热态构造使用 mathlib 的谱存在性，不宣称已提供数值对角化程序。

## 已证明的物理约定

采用 `ψ = (c, c†)`，Hamiltonian 定义为

\[
H = \sum_{ij} h_{ij}c_i^\dagger c_j
  + \frac12\left(\sum_{ij}\Delta_{ij}c_i^\dagger c_j^\dagger
                  + \mathrm{h.c.}\right),\qquad
\mathcal H = \begin{pmatrix}h&\Delta\\\Delta^\dagger&-h^T\end{pmatrix}.
\]

`nambu_energy` 保留 `H = (ψ† ℋ ψ + tr(h)·1)/2`；`nambu_equation` 给出 `[ψ_i,H] = (ℋψ)_i`。后者是对易恒等式，尚未与已有 `HamiltonianFlow` 的 `exp(+itH)` 约定建立时间导数桥，因此不能直接报告一般动力学响应已经实现。

轨道换基采用 `c′ = Uc`，相应系数为 `h′ = UhU†`、`Δ′ = UΔUᵀ`。完整 Nambu 空间上的换基是 `diag(U, conjugate U)`。这覆盖轨道酉变换；一般混合粒子与空穴的 Bogoliubov `U,V` 变换及其对角化还未实现。

粒子—空穴操作显式共轭并交换两半，满足反线性、平方为恒等及本征方程伙伴关系。Majorana 采用 `γx = c+c†`、`γy = −i(c−c†)`，因此占据数为 `n = (1+iγxγy)/2`。约定参考 [Budich 与 Ardonne 的原文第 II 节](https://arxiv.org/html/1306.4459v2)；本批仅消费相应有限算符约定，没有实现文中的拓扑不变量。

旧 `Condensed.bdg` 保留为兼容的复对称代数块。一般复配对使用下面的 Hermitian 块，其平方含 `|Δ|²`，不是 `Δ²`：

```lean
import LeanPhy.Entry.Condensed

open LeanPhy.Quantum LeanPhy.Condensed
open LeanPhy.FieldTheory.FiniteFermion LeanPhy.FieldTheory.FermionBdG
open scoped Matrix

noncomputable def pairedH (ε : ℝ) (Δ : ℂ) :=
  (modes 2).hamiltonian (ComplexPairing.pairedModes ε Δ)

example (ε : ℝ) (Δ : ℂ) : (pairedH ε Δ).IsHermitian :=
  (modes 2).hamiltonian_hermitian (ComplexPairing.pairedModes ε Δ)

example (ε : ℝ) (Δ : ℂ) :
    ComplexPairing.block ε Δ * ComplexPairing.block ε Δ =
      ((ε ^ 2 + Complex.normSq Δ : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := ComplexPairing.square ε Δ

example (n : ℕ) (K : Coefficients (Fin n)) (U : FiniteUnitary (Fin n)) :
    ((modes n).car.rotate U).quadratic (K.rotate U).normal (K.rotate U).pairing =
      (modes n).hamiltonian K := quadratic_rotate (modes n).car K U
```

`ComplexPairing.block` 是两物理模式的约化块；`full_to_reduced` 证明它等于完整系数矩阵的指定子矩阵。它不是单个无自旋模式的完整 Nambu 配对模型。此子矩阵关系也不单独证明一般动力学子空间约化。

## 从实际多模真空推导四点关联

[FermionVacuum](../LeanPhy/FieldTheory/FermionVacuum.lean) 现在从实际态推导收缩公式。`FermionVacuum` 要求 CAR、产生／湮灭伴随、合法密度矩阵和 `ann i * rho = 0`；四点 Wick 等式不再是该构造器的输入。`FiniteFermion.vacuumState n` 对任意有限 `n` 递归证明空占据满足这些条件，包含零模式；`vacuumOfOrder e` 保留站点、轨道或自旋标签的显式次序。

`FermionProbe` 用两个独立复系数表表示
`P = Σᵢ (p.annᵢ cᵢ + p.creᵢ cᵢ†)`。系数没有隐含共轭，探针也不必是规范模式。实际有序二点读数是 `C(p,q) = Σᵢ p.annᵢ q.creᵢ`，公共定理给出
`⟨PQRS⟩ = C(p,q)C(r,s) - C(p,r)C(q,s) + C(p,s)C(q,r)`。

```lean
import LeanPhy.Entry.Condensed

open LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion

example (n : ℕ) (p q r s : FermionProbe (Fin n)) :
    (vacuumState n).expectation
      (p.operator (modes n).car * q.operator (modes n).car *
        r.operator (modes n).car * s.operator (modes n).car) =
      p.contraction q * r.contraction s - p.contraction r * q.contraction s +
        p.contraction s * q.contraction r :=
  (vacuumState n).fourPoint p q r s
```

下游需要 [FermionicQuasiFree](../LeanPhy/FieldTheory/FermionicQuasiFree.lean) 的有序四点证书时，可由同一真空与探针数据直接构造：

```lean
import LeanPhy.Entry.Condensed

open LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion

noncomputable def vacuumReadout (n : ℕ) (p : Fin 4 → FermionProbe (Fin n)) :
    OrderedQuasiFreeCertificate (Occupation n) (Fin 4) :=
  (vacuumState n).certificate p
```

反对称的是证书的有序 slot kernel；实际探针二点期望在交换时保留 CAR 接触项。重复物理探针不一定为零，例如同一个 `c + c†` 的真空四次矩为 `1`。原 `SingleModeVacuum` 和 `TwoModeVacuum` 保留为兼容的显式矩阵回归。

本批进一步从同一真空条件推导任意点数递归，见下一节。有限温热态、一般 Gaussian 态、时间排序、一般相互作用态和连续极限的 Wick 定理仍需独立证明；真空也不自动是用户 Hamiltonian 的基态。

## 有限酉传输：轨道旋转与自由淬火

`FermionUnitaryWick.transport U V` 同时将实际密度和每个 CAR 生成元按同一个 `FiniteUnitary` 共轭。`transport_moment` 由迹循环和乘积共轭严格推出

```text
⟨P₁ … Pₖ⟩_{UρU†, U c U†} = ⟨P₁ … Pₖ⟩_{ρ,c}.
```

因此 `transport_moment_eq` 把任意有限真空的 Wick 递归直接传到轨道基变换或给定的自由多体酉演化后。酉矩阵作用在实际占据空间 `Occupation n` 上；它与 `MultiModeCAR.rotate` 的单粒子轨道换基是不同层次的对象，不能把任意多体酉自动解释成单粒子 Bogoliubov 变换。

```lean
import LeanPhy.Entry.Condensed

open LeanPhy.Quantum LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion

noncomputable example (n : ℕ) (U : FiniteUnitary (Occupation n))
    (ps : List (FermionProbe (Fin n))) :
    (FermionVacuum.transport U (vacuumState n)).moment ps =
      FermionicWick.moment FermionProbe.contraction ps :=
  FermionVacuum.transport_moment_eq U (vacuumState n) ps
```

这个接口只证明共同酉传输的有限代数事实；它不构造任意驱动的存在性，不把传输态识别为相互作用基态，也不提供热态或连续／热力学极限的 Wick 因子化。

## 任意点数、接触项与表达式读数

[FermionicMoment](../LeanPhy/FieldTheory/FermionicMoment.lean) 按插入位置带符号地删除配对伙伴，并证明长度下降；重复探针保留为不同位置。[FermionVacuumWick](../LeanPhy/FieldTheory/FermionVacuumWick.lean) 用 CAR 将湮灭部分移到最右端，由实际密度的消去条件去掉末项，得到

\[
M(p_1,\ldots,p_{2m})=\sum_{j=2}^{2m}(-1)^j C(p_1,p_j)
M(p_2,\ldots,\widehat{p_j},\ldots,p_{2m}),\qquad M(\varnothing)=1.
\]

`moment_eq` 将实际 trace 连接到系数递归；`moment_odd` 证明所有奇数矩为零。公式不要求探针本身构成规范模式，收缩核也不要求在物理探针标签上反对称。

```lean
import LeanPhy.Entry.Condensed

open LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion

example (n : ℕ) (ps : List (FermionProbe (Fin n))) :
    (vacuumState n).moment ps = FermionicWick.moment FermionProbe.contraction ps :=
  (vacuumState n).moment_eq ps

example {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)
    (ps : List (FermionProbe ι)) (hodd : ps.length % 2 = 1) :
    (vacuumOfOrder e).moment ps = 0 := (vacuumOfOrder e).moment_odd ps hodd

example (n : ℕ) (before after : List (FermionProbe (Fin n)))
    (p q : FermionProbe (Fin n)) :
    (vacuumState n).moment (before ++ p :: q :: after) +
        (vacuumState n).moment (before ++ q :: p :: after) =
      (p.contraction q + q.contraction p) * (vacuumState n).moment (before ++ after) :=
  (vacuumState n).moment_exchange before after p q
```

最后一条是任意周围插入下的相邻交换关系。对重复 Majorana 探针，接触项通常不为零，不能直接交换后加负号。

创建／湮灭词使用只有 `ann i, cre i` 顺序才能非零的整数核。`FermionWord.vacuumMoment` 是可执行整数计算，`word_expectation` 证明其复数值就是实际期望。符号系数表的 `FermionPolynomial.vacuumValue` 在原系数环中计算；`expression_expectation` 再经环同态赋值。已有 CAR `compile` 保持该实际读数，接口是 `compiled_expectation`。

```lean
import LeanPhy.Entry.HighEnergy

open LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion FermionWord

example {R : Type} [CommRing R] (n : ℕ) (f : R →+* ℂ)
    (p : FermionPolynomial.Expression R (Fin n)) :
    (vacuumState n).expectation (FermionPolynomial.eval f (vacuumState n).car p) =
      f (FermionPolynomial.vacuumValue p) :=
  (vacuumState n).expression_expectation f p

example : (vacuumState 3).expectation
    (FermionWord.eval (vacuumState 3).car [ann 0, ann 1, ann 2, cre 0, cre 1, cre 2]) = -1 := by
  rw [(vacuumState 3).word_expectation]
  have h : vacuumMoment (ι := Fin 3) [ann 0, ann 1, ann 2, cre 0, cre 1, cre 2] = -1 :=
    by decide +kernel
  rw [h]
  norm_num
```

这为有限模式参考真空中的关联展开、含相互作用插入的矩和候选微扰系数提供可复用操作。它计算的是指定真空中的表达式读数；相互作用 Hamiltonian 的基态、一般 Gaussian／热态因子化、时间排序与展开余项没有因此获得证明。

当前递归直接枚举配对，没有 Pfaffian 消元或记忆化；偶数 `2m` 个稠密探针可产生 `(2m−1)!!` 个配对项。测试覆盖长度 0、1、3、6、8 的复探针，不能据此宣称大点数计算已可扩展。无需展开 `2^n` 维矩阵是语义桥的好处，不是整体复杂度保证。

## 验收与全局边界

`lake exe leanphy_fermion_client --project-json` 报告 19 条带证明结论和 3 类开放义务：相互作用与自洽、动力学关联、连续极限与拓扑。`--strict` 拒绝带这些未决任务的项目。该客户端不改变默认领域包的结论数量。

回归检查实际构造与耦合表的连接，并拒绝遗漏共轭、半因子、迹常数或宇称串，以及将非等距混合当成 CAR、将 Nambu 态当成多体态的错误。完整发布状态以 [VERIFIED](../VERIFIED.md) 为准。

上述表示构造之后，[费米表达式层](fermion-words.md) 已补任意词正规化、局部相互作用表和实际导数；[量子响应层](quantum-response.md) 已补非对易响应；实际态层已有任意有限模式真空、任意长度线性探针收缩、词和相互作用表达式读数及有序四点证书。一般相互作用截断、自洽解、一般 Gaussian／热态 Wick、时间排序、拓扑不变量和热力学极限仍未完成。玻色 `Fock.BosonicMode` 仍是带 CCR 前提的抽象算符结构；此处有限费米表示不使玻色截断自动满足精确 CCR。后续批次按[全局路线](roadmap.md)重新比较响应、作用量／匹配、物理证据与探索工作流的缺口。
