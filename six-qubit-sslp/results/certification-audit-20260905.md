# 20260905 全文 Lean certification 审阅

审阅目标：`documents/20260905/main.tex` 与 `supplementary.tex` 中已经作为事实陈述的数学内容，达到 Lean kernel certification。论文明确标注的猜想、未来工作，以及历史和工作流程叙述，不应被改写成未经证明的公理。

审阅结论：核心六量子比特分类已具备大量实质性证明，但目前不能宣称两篇全文已经完成。另有一处正文 Singleton 断言需要先补假设，原样并不成立。未完成项不只包括较大的二进制矩阵上界计算，还包括新版一般彩色正规形、四个开放轨道的已声称连续族构造、若干补充材料独立推论，以及通用算符/枚举子语义。README 同时保留了多个时代的状态说明，不能直接作为当前缺口清单。

## 1. 版本与审阅边界

- 本地提交：`481ef5c`，`eq:A-enumerator as an actual operator trace`。
- 实时读取 GitHub `sixqubit-classification` 分支头：`96fd68eb72332f9e8eb61b04fe70cbd3e62ca8c7`。
- 本地 `HEAD^{tree}` 与该远程提交的 `six-qubit-sslp` 子树均为 `ffe88979065681d6ee971f74abc01dcc80277507`；`git diff HEAD origin/sixqubit-classification:six-qubit-sslp --stat` 为空。因此审阅的跟踪文件与所指 GitHub 子目录一致。
- 主文 3,569 行，补充材料 12,630 行。主文有 13 个 theorem、13 个 lemma、4 个 corollary、1 个 proposition；补充材料分别有 19、24、11、39 个。只核查 README 的 headline 无法覆盖这些独立陈述及未编号公式。
- `main.tex` SHA256：`E110A4DBF1183D2C061CB19A55D22826483CCF5EBDFB8B26524472D35BA4CB80`。
- `supplementary.tex` SHA256：`57D8050FA0969E3DA5FA0C9F746D21587C423B0D2B4A96280BB290B9AF8ED89E`。
- 20260905 补充材料与本地 20260902 版无文本差异；主文有较大重排和新增内容。旧版标签/章节号不能直接充当新版覆盖证据。
- 本次进行源码审阅、现有验证器检查及缓存依赖上的公理审计；未进行全库冷构建。下文“已有”表示发现相应证明源码，不应读成“本次从零重建了其所有依赖”。

## 2. 已经具备的核心内容

| 内容 | 当前证据与边界 |
|---|---|
| `β₁,…,β₆`，尤其 `β₆ = 9` | 二进制分母界的生成证书已有内核证明；`MainTheory/Generated/BinaryBetaSixKernel/Certificate.lean`。不应再把 `β₆` 列为待办。 |
| 任意秩、距离二及以上的有限性 | `GeneralFinitenessRank`、`ProjectiveGroupGeneral`；`ZDetectionHypothesis.finite_intrinsicGroup_of_zDetects` 更贴近正文仅检测所有 `Z_j` 的假设。旧文档所称必须等待 Cartan 定理，已不是这一结论的阻塞。 |
| 秩二正规形与生成元 | `RankTwoSSLPCanonical`、`RankTwoGeneratorGeneral`、`SSLPConverse`；已有排序、原始性、两纤维、实际 KL 条件与群元素阶数。 |
| 六量子比特筛选/轨道主链 | `PaperReductionChain`、`CodeOrbitKey`、`CodeOrbitStatus`、`StageRecordCounts`、生成的 provenance/rank/orbit 证书。已有从代码进入目录的桥，不能继续照搬旧版“只证明单轨道”的描述。 |
| 51 个 no-go | 每轨道有真正 `SS.HasDistance` 输入的代码级封装；本次 gate 和 momentgate 检查全部通过。 |
| 15 个 realization orbits | `RealizationOrbits15.hasCompletion_iff_mem_realizationKeys`、`card_realization_orbits`、`realizationKeys_orderDistribution`。其中轨道 1–4 的非空性已经成立。 |
| 11 个已解决的非空枚举子像 | `WImages`、`WImageSettled62` 及轨道 7、8、9、45 的 universal/family 模块；连同 51 个空像及 4 个仍开放的完整像形成正确划分。 |
| 内禀群阶与 C5 刚性 | `IntrinsicOrderAudit.natCard_mem`、`natCard_le_five`；`OrderFiveCodeRigidity.luEquivalent_canonical_of_orderFive` 从任意具有五阶元素的代码出发，已把入口、排除及 LU 传输接通。 |
| A 枚举子的真实算符迹 | `PauliKernelTrace.trace_pauliKernel_mul_projector` 与 `Aco_eq_sum_normSq_trace` 已证明，不再只是把 frame 内积和称为 trace。 |

以上结论与下文独立推论/附加条款的缺口可以同时成立：可以用不同的正确证明完成最终分类，而没有形式化论文中每一个单独声称的中间命题。

## 3. 应优先补齐的实质性缺口

### 0. 先修正 Singleton 断言的 K=1 边界

`main.tex:343`–`:349` 把距离至少 d₀ 与所有 weight<d₀ 算符的标量压缩等价；`:355`–`:358` 随后无附加条件写出 `K≤2^(n−2(d−1))`。两者在 K=1 时冲突：任意归一化秩一投影 `P=|ψ⟩⟨ψ|` 对每个算符 E 都有 `PEP=⟨ψ,Eψ⟩P`，所以前一判据在任意距离阈值成立。取 n=1、K=1、`ψ=|0⟩` 和 d₀=2，后一公式却要求 `1≤1/2`。

`CodeSpec.ExactCode` 的 `positiveRank : 0<K` 允许 K=1，`SS.HilbertKL` 的定义也确实存在此边界。这不是“缺一个 Lean 证明”，而是原文断言缺假设。最小修正是在 Singleton 断言中增加 `K≥2`；若一定要纳入 K=1，则必须另行约定秩一距离并修改前述 iff。六量子比特 K=2 的结论不受影响。形式化指数时也不应把整数负指数改成自然数截断减法来掩盖冲突。

本次已新增并实际运行 `results/certification-audit-rank-one-20260905.lean`：证明任意 rank-one frame 满足 `HasDistance`、具体 `|0⟩` 的归一化，以及上述有理数/整数指数不等式为假，并将这些条件组装为单个 `rankOne_counterexample` 存在性定理。Lean 退出码 0，四个定理的公理依赖均仅为标准三项。

### A. 新增的一般彩色 SSLP 正规形及其逆向

**论文位置**：`main.tex:1339`，`thm:general-sslp-normal-form`，并包括 `eq:general-sector-probabilities`、`eq:general-sector-moments`。

当前已有任意 K 的谱分解、扇区分解与有限 lift 基础设施，但尚未找到一条覆盖这一定理全部字段的源码陈述：排序的原始角向量、在 `ZMod m` 中的互异颜色、首颜色为零、颜色 gcd 为一、正的扇区重数且总和为 K、扇区落在 `(q/m)γ` 纤维，以及由这些数据构造代码并证明逻辑阶恰为 m 的逆向。现有 `SSLPConverse` 明确使用 `OrthonormalFrame n 2`，不能充当任意 K 的逆向。

**实施**：新增通用彩色 datum/normal-form 结构，复用 `GeneralSpectralSectors`、`PhaseSectorFull`、`GeneralLiftOrder`；把 X 翻转和置换的语义传输推广/组装到任意 K。证明颜色映射、互异性及 gcd 与精确阶的等价；逆向从纤维内正交子空间建立总 frame。再由对角 KL 推出所有 `|J| < d₀` 的 occupation moments，并把扇区概率与 `Π_α(x,x)/k_α` 接起来。

**验收**：一个任意 `(n,K,d)` 的 forward theorem 和一个任意 K 的 converse theorem；颜色/gcd/纤维/重数不作为应当推导却额外假设的字段。

### B. 轨道 1–4 的五个连续族包含关系

**论文位置**：`main.tex:3356`，`eq:four-open-L-inclusion`；`:3362`，`eq:four-open-M-inclusion`。

正文已经声称：

- `L([0,1]) ⊆ W_r`，对 `r = 1,2,3,4` 全部成立。
- `M([2/3,1]) ⊆ W_1 ∩ W_4`。

目前 `MainTheory/WImageOrbit1.lean:97` 只给出第二行的 W1 半边。该文件开头明确记录 W4 半边及 L 四个包含关系缺少精确代数族。`OpenOrbitsRealized` 的单个 witness 只证明非空，不能证明整段连续区间。

**实施**：先从本地配套构造文稿 `documents/20260905/623/orbit1_so5_bd4_c4_construction.tex` 提取可验证的精确族；建立带实参数和必要平方根的幅度公式，证明每个参数值的支持、正交归一、完整 weight≤2 KL 及 A/B 系数。需要多个参数图时明确覆盖整个闭区间，包含零幅度和端点。最后导出 4 个 L 包含关系及 1 个 M→W4 包含关系。现有 M→W1 证明可保留。

**验收**：每个 `t`/`α` 都构造真实代码；不能用数值拟合、几个采样点或只有端点的 witness 代替。

这五项是论文已经声称成立而 Lean 尚未完成的内容。`W₂=W₃=L([0,1])` 等反向包含在论文中明确是猜想；证明这些猜想不是完成现有已证明内容的前提。

### C. `β₇=18`、`β₈=42`、`β₉=120` 的上界

**论文位置**：`main.tex:1623`，`eq:small-beta`；`:2154`，六量子比特距离二的 `q≤18`。

`BinaryBetaSevenLower`、`BinaryBetaEightLower`、`BinaryBetaNineLower` 已提供达到 18、42、120 的矩阵证书；其文件说明和定理类型均只覆盖下界/attainment。缺少 `BetaBound 7 18`、`BetaBound 8 42`、`BetaBound 9 120`，因此缺少相应 `BetaExact`。这不阻塞依靠 β6 的六量子比特距离三分类，但确实阻塞论文全部数值陈述，尤其 d=2 的具体截止值 18。

**实施**：作为独立计算证明项目。优先 β7；先选择可证明完备的对称归约、剪枝与证书格式，测量生成和内核检查成本，再扩大到 β8、β9。复用现有二进制矩阵/逆矩阵清分母层，外部程序只产生候选、等价见证或覆盖树；Lean 必须验证覆盖完备性、变换的合法性和每个叶子的上界。已有下界矩阵不必重做。

**验收**：以上三个通用 `BetaBound`，并与现有 attainment 组合为三个 `BetaExact`。不能只导入外部表的最大值，或只验证搜到的极值矩阵。

### D. 一般距离三的真实仿射秩，以及 Z-only 假设下的尖锐扇区界

**论文位置**：`main.tex:1938`，`thm:d3-bound`；`:2021` 的后续分类界；`:1738` 的定量群界。

`BetaAtPivotRank.FreshSparsePhase.order_le_betaOf_rank_le` 证明了任意 n 下相对于 `F.basis.rank` 的界。`SupportAffineRank` 定义真正的 support affine rank 并把它用于代码入口，但该模块的代码变量是 `ExactCode 6 2 3`。尚需把一般 n 的所选 pivot rank 与论文两实际支持的共同仿射维数接通，并导出具有完整代码级假设和原文 r 语义的结论。这是语义桥/定理组装缺口，不能据此否认已经完成的 `q≤β_n` 或六量子比特入口。

另外，`SharpSectorBound.hasPrimitiveLift_le_beta_sectorCount` 仍要求 `2≤d`；`ZDetectionHypothesis` 在仅有所有 `Z_j` 可检测时给出的是 `β_(n+K−1)`。还需以实际不同本征值数 ℓ、在同一个较弱假设下给出 `β_(n+ℓ−1)`。

**实施**：推广 support-point/affine-rank 定义，证明支持零点时 affine direction 等于 linear span，证明 supported basis 的 rank 与该 span 的 rank 一致，并接回普通 code 的 normal form；若用有理秩表达 r，同时说明与实仿射维数相等。尖锐 Z-only 界可复用 canonical sector resolution，把 `R.zDetects hd` 替换为已经证明的 `resolution_zDetects R hZ`。末端定理还应保留目标距离 d，而不是只留下弱化后的距离三对象。

## 4. 补充材料独立陈述与表格的剩余工作

这些缺口主要涉及“全部内容”的覆盖，不等于对应轨道的最终 no-go 或枚举子像失败。

| 论文位置 | 已有与缺少 | 实施方式 |
|---|---|---|
| `supplementary.tex:2645`，`cor:o8raisinggram` | Orbit8 已有 saturation、ladder、支持及最终枚举子像；尚未找到原文 G+ 的定义、`G+² = ½G+` 和完整谱陈述。 | 定义实际 raising-vector Gram 矩阵，从 ladder 内积和饱和条件推出投影关系、秩及谱。 |
| `supplementary.tex:3298`，`cor:o9magnitudes` | 最终模块有 A/B 与权二 Pauli scalar；明确的 `1/12` 数据在 witness 等局部分支中，尚未找到对任意允许代码都成立的“10 个 1/12 加 1 个 1/6”结论。 | 在正确的归一化/坐标规范下继续 K4 支持与 Hafnian 归约，形成普遍幅度模平方定理。 |
| `supplementary.tex:7751`，`prop:q4o31momentnormal` | 已有 MomentSystem 和所需的正向线性后果；缺原文 rank 23、dimension 9 及完整 iff 参数化。 | 精确行消元证书、双向重构，再给出解空间维数。 |
| `supplementary.tex:12065`、`:12112` 的 parity 几何/连通性命题 | `ParityFour` 采用另一条不等式路线完成 no-go，没有实现这些一般几何命题本身。 | 若保留全文覆盖目标，分别形式化有限支撑/凸几何与连通性陈述；不必重写已经正确的 no-go 证明。 |
| `supplementary.tex:3959` 的 `lem:twoedge`、`:9765` 的 `lem:m3lift-fullrank`、`:10937` 的 `lem:m2-fullrank-matching` | 具体轨道的有限消元已覆盖所需实例；一般长度、实际代码及可逆 restricted-character matrix 版本尚未找到。 | 从通用满秩线性系统与 KL 行桥导出一般物理代码陈述；两复数的代数引理本身不等于通用代码引理。 |
| `supplementary.tex:89` 起的 66 轨道表，及 `:12456` 起分 `(q,m)` 统计表 | 主链总数、逻辑阶分布和部分 rank-stage 行已证明；尚缺每行 LP 仿射维数、轨道 multiplicity ν，以及完整细分统计的语义核查。 | 把表行接到 certified directory，计算 ν 为实际轨道等价类纤维的基数；用有理 rank/active face 证明 d_LP，补齐所有分组。 |
| `main.tex:2920`，`six:eq:lpdim` | active-face 最大支持秩不等于 LP affine dimension；尚未找到 `dim P = |U0|+|U1|−rank A_U` 的通用定理。 | 从严格正的 active-face 点证明 affine hull 等于约束方程解空间，再用 rank-nullity；同时支撑补充表格和 Orbit31 维数。 |

一般“有理系数 LP 存在实可行点 iff 存在有理可行点”的文字陈述也宜单独补定理。当前有限筛选已有实分离证书路线，不能把这一通用引理的缺少误报成整条有限筛选不可靠。

此外，若保留全文每个精确数值 display 的覆盖目标，还应把补充材料 `:272`–`:292` 的 q9 covariance/行列式和 `:442`–`:454` 的 orbit36 指定 moment minor 等纳入矩阵证书。最终 no-go 的替代证明不会自动验证文中另外打印的矩阵数值。

## 5. 正文预备知识、语义和示例

如果“全部内容”包括预备知识中作为定理/事实陈述的内容，这一组也必须入账；引用文献本身不构成 Lean 证明。

1. **B 枚举子的算符迹**（`main.tex:374`）。A 的迹桥已存在；B 仍是 frame matrix elements 的 Frobenius 和。新增一般矩阵 M 与 frame projector 的恒等式 `Tr(M P M† P) = Σ_ab |⟨ψ_a,Mψ_b⟩|²`，专门化到 Pauli，并核对 Bco 自带 K 因子及论文的 `1/K` 归一化。源码起点：`PauliKernelTrace`、`CodeSpec.BWeight`、`SixQubit/BEnumerator.lean:42`。
2. **一般 n,K 的多项式 MacWilliams 公式**（`main.tex:385`–`:396`）。`SixQubit/MacWilliams` 已有任意 n,K 的 `pauli_duality`、`subset_duality`、`frob_of_KL`；完整系数变换 `bco_transform_six` 则固定 n=6、K=2。需定义通用齐次多项式、证明 Krawtchouk/二项式求和并组装正文多项式公式及 `A_w=B_w`。已有 Parseval 核心可复用。
3. **一般 LU 下枚举子不变性与单次张量积表达**（`main.tex:409` 及随后段落）。当前有置换、位翻转、逻辑 frame 相位等不变性；尚未找到任意单量子比特 U(2) 的 A/B 不变性。`ClassificationLevels.LUEquivalent` 是 elementary LU 的等价闭包；其与正文“一个置换乘一个本地张量积”的 iff 也尚未找到。可证明单站点共轭在 Pauli 空间诱导保范变换，再组合各站点及置换；另证明 elementary 操作可重排和合并。
4. **五量子比特 rationalization 示例**（`main.tex:1132`–`:1300`）。未找到该显式族的专门模块。应证明六个基串上的精确幅度、归一化、所有权一 KL、权二 `Z₂Z₃` 的反例、随 t 不变的逻辑三阶作用、无理 t 的物理无限阶、t=1/6 的原始六阶 lift，以及 t=0 的三阶 lift 和 `q_min=3`。有限部分用内核算术验证，实参数部分用指数/有理化理论。
5. **Singleton 与精确距离**（`main.tex:358`；补充材料如 `:3870`）。`SS.HasDistance ψ d` 定义的是检测所有 weight<d 的 Pauli，即距离至少 d。`ExactCode` 中 exact 指精确 KL 等式，本身不表达“不能达到 d+1”。六量子比特 rank-two 的特殊上界有短路线：现有 MacWilliams 正规式与七行变换可推出 `B₃−A₃ = 20 + 10 A₁ + 4 A₂ + A₃ > 0`；而 `HasDistance 4` 强迫 `B₃=A₃`，矛盾。该代数等式在本次审阅中已作独立符号检查，仍需写入 Lean。这能给出任意此类代码的精确距离三，无须先形式化一般 Singleton；但正文一般 `(n,K,d)` 的 Singleton 公式仍是独立义务。
6. **一般 Knill–Laflamme 恢复 iff 与 Eastin–Knill**（`main.tex:336`、`:475`）。已有 scalar-compression 等核心 KL 语义，但没有找到恢复信道存在性 iff，也没有找到针对所有 transversal gates 的 Eastin–Knill 定理。后者不能由仅对一个固定基底下 diagonal subgroup 的有限性代替。这两项应作为独立背景形式化工作包，尤其 Eastin–Knill 规模明显较大。

另一个较细的 literal-scope 项是 Smith normal form 的 `UCV` 对角化及整除链存在性。当前 `DeterminantalFactor`/`PaperSmithFactor` 已无条件把清分母量接到 `|det|/gcd(adjugate)`，并给出所需整除结论；不要把它再报成整个尖锐清分母定理缺失。若需要原文完整 SNF 对角式本身，还应补构造/存在性与对应关系。

`thm:sslp-completeness` 还使用“决定完整 KL 多项式系统、审计内禀群并取商”的程序性语言。`SSLPPipelineExact` 已给出正规形覆盖与代码重构，但尚未给出一般 n 下显式多项式编码、求解器/群审计输出和最终商之间的完整程序规格。证明数学覆盖性不要求实现一个可执行实闭域求解器；不过若要把这段文字也认证为算法正确性，应另外陈述 solver sound/complete 的接口并证明结果集合/商与代码集合相符，不能仅将重构同一个正规形称为整个程序已经验证。

补充材料 `:3841` 仍把轨道 1–4 的存在性称为 unresolved，与当前主文和 `RealizationOrbits15` 不一致。应更新为仅完整枚举子像仍未确定；不能据这段旧文字把已经完成的非空性再次列为待办。

## 6. 信任边界与本次检查

“fully kernel”可以允许 Lean/mathlib 的标准逻辑公理 `{propext, Classical.choice, Quot.sound}`；目标不是零个逻辑公理。生成器可以不受信任，只要生成结果的正确性、覆盖性和到论文对象的语义连接均由内核证明。单纯有 Python 脚本不构成缺口，单纯有 `#print axioms` 也不证明陈述就是论文的陈述。

本次已经执行：

- `tools.verify.check_sources()`：通过。
- `python tools/run.py verification/gate.py`：51 passed，0 failed，0 unchecked。
- `python tools/run.py verification/momentgate.py`：通过，所有已声明矩条件均匹配真正的 weight≤2 条件。
- `python tools/run.py verification/momentgate.py --selftest`：3 项 inventory 破坏与 1,063 项字段/顺序/内容破坏全部检出，missed 0、not injected 0。
- rank-one 边界反例的独立 Lean 检查：退出码 0，无错误/警告，四个定理仅依赖标准三项公理；交付源码为 `results/certification-audit-rank-one-20260905.lean`。

**公理审计通过**：三个 audit 源码列出的 1,046 个不同目标全部在 Lean 已检查的环境中存在；它们的合并传递公理依赖恰为 `{propext, Classical.choice, Quot.sound}`，退出码 0，用时 56.2 秒。合并集合只含标准三项，意味着每个目标的依赖集合都包含于该允许集合。

本次没有完成原包装器逐个 `#print axioms` 的运行：其在重复遍历大量共享证明约 14 分钟后被主动停止，随后改用**同一个 Lean 官方 `Lean.CollectAxioms.collect`**，对所有目标共享 visited 集合，并显式拒绝找不到的目标和任何不允许的公理；没有自制证明依赖遍历算法。审计源码保存在 `results/certification-audit-axioms-20260905.lean`，可用 `lake env lean -j 1 results/certification-audit-axioms-20260905.lean` 重跑。执行摘要在 `results/certification-audit-checks-20260905.txt`。

**FiniteLift 定点复验也通过**：导入缓存中的相关签名已经是当前 `det ≠ 0`/`inverseDenominator` 接口，并非旧 SmithWitness 接口；再执行 `lake env lean -j 1 -E warning MainTheory/FiniteLift.lean`，21.1 秒、退出码 0、无诊断，未写入新的编译缓存。旧 stamp 因此不能作为缓存仍采用旧数学接口的证据。

仍未进行全库冷构建；以上检查不能替代所有当前源码及依赖的一次完整重编译，不声称全量当前源码构建已通过。

已发现的工程问题：

- 当前 audit 源码的 `#print axioms` 数量为 `434 + 592 + 20 = 1046`；README 的 953 以及旧 `results/axiom-audit-maintheory.txt` 已落后。本次全部 1,046 个目标的合并传递依赖检查已通过，历史报告仍需统一更新。
- 17 个活跃模块源码 mtime 晚于对应 olean；其中一些只是时间戳变化且有匹配的成功构建哈希，但 `MainTheory/FiniteLift.lean`、`MainTheory/PhaseSectorBridge.lean` 与保存的成功构建哈希不一致。两份旧哈希匹配提交 `2832319`：PhaseSectorBridge 此后是 docstring 变化；FiniteLift 曾有从 Smith-witness 到 nonsingularity 的接口变化，但本次缓存签名检查及当前源码复验均通过。问题是构建溯源记录未统一更新，不能仅凭时间戳/stamp 宣布证明无效。
- `tools/check-readme-names.py:57` 起没有把 Lean 子进程非零退出码作为失败条件，只搜索 `unknown`。无 `unknown` 的其他失败可能被报告为 `all present`。这不使 Lean 内核不可靠，但使该包装检查可能报假阳性。
- `tools/verify.py` 没有调用 gate、momentgate 及其 selftest；因此其“end to end”入口还不包含论文数据对应检查。
- `tools/verification/mkmanifest.py:37` 固定读取已不存在的根目录 `six_qubit_sslp.tex`；README 推荐的 manifest 再生成命令不再适用于当前权威稿件。
- 本地跟踪文件中没有 `.github` CI；跟踪的 `__beta*` 历史 stage 目录不在活跃库 globs 内，应明确其档案身份，避免把它们计入当前证明覆盖。
- 全量 `lake build` 与 `tools/build_lean_serial.ps1` 的资源策略需要统一。每个 Lean worker 的 `-j 1` 不等于限制 Lake 同时启动的模块数。

## 7. 建议实施顺序与验收

**第一批：修正陈述并建立可持续验收。** 先补 Singleton 的 K≥2 假设。建立与两个 TeX 哈希绑定的 claim manifest：每个定理、独立推论、已声称公式和表格行，都记录标签、假设/结论、对应 Lean 名称、状态和未完成原因；猜想单独标记。修复验证器退出码，统一接入语义 gate，更新 audit 输出；建立能追踪依赖变更的串行/受限并行构建，执行一次当前提交的完整源码验证。

**第二批：补易于复用的语义和小结论。** B 的 trace、通用枚举子定义与 KL 系数等式、五量子比特例子、Z-only 尖锐扇区界、真实仿射秩接口；随后 Orbit8 Gram、Orbit9 幅度推论和 Orbit31/LP dimension。每项都导出直接对应论文陈述的 theorem。

**第三批：两个主体数学工作包并行。** 任意 K 彩色正规形及逆向；轨道 1–4 的五个连续族包含关系。后者先复用精确构造，不把求解完整 W1–W4 反向包含的研究问题混入该任务。

**第四批：完整表格与数值上界。** 表格从已认证目录生成并证明每一列的语义；β7 上界先做，β8、β9 独立规划证书规模。大型生成只产出待检见证，不扩大内核信任边界。

**第五批：背景理论全覆盖。** 通用 LU invariance、Singleton、恢复版 KL、Eastin–Knill，以及若需要的完整 Smith 正规形。它们的成本与“六量子比特分类主结论”的成本分开记录，但在字面全文目标下不能无声略过。

最终完成条件应当同时满足：没有未解释的已声称数学 claim；每个对应 Lean theorem 的假设不比论文偷偷更强、结论不比论文更弱；从干净或正确失效的依赖构建得到全部 proof artifacts；所有交付定理的传递公理依赖均在允许集合；所有有限证书均验证覆盖性；表格和显式代表与本版稿件一致。
