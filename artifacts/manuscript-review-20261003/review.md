# 20261003 文稿与仓库审阅

审阅日期：2026-10-03。对象：`documents/20261003`、本地 Lean 仓库、GitHub
`xh-xihe/dyadic-lifts` 的 `sixqubit-classification` 分支。

当前结论：**新增的 orbit 2、3 精确证书有可复现的实质进展；全文尚不能标为
fully kernel Lean certification。** 数学证明、精确计算、Lean 定理，以及论文与
Lean 定理的对应审阅，应分别记录。

本次核对了完整目录的版本差异和文件哈希、最新提交、现有发布审阅记录、关键
数学陈述、两份新增枚举器证明的分析桥接及有限证书、Lean 信任检查和文稿编译。
这不表示为既有台账中 1542 个 `unreviewed` 条目完成了逐条语义认证。
本报告没有更改文稿、证明或原有覆盖状态。

## 1. 版本与远程状态

| 对象 | 本次核对结果 |
| --- | --- |
| 本地提交 | `46c7b5315069c0b24f5bbe1749a3ba28f84d8eeb` |
| GitHub 分类分支提交 | `cb992a9c286be8c846ecabb3d77568cc8174d97f` |
| 本地 tree / 远程 `six-qubit-sslp` tree | 都是 `1e6416c9ef459a3db7b431839f503b7b2121bb97` |
| 远程默认分支 | `main`，提交 `8eb16e2f31b512b3bebc8d8a276bd2efd720d706` |
| `20261003/main.tex` | 与 `20260929/main.tex` 字节相同，2694 行 |
| `20261003/supplementary.tex` | 与 `20260929/supplementary.tex` 字节相同，14769 行 |
| `20261003/references.bib` | 与 20260929 字节相同 |
| 完整新目录 | 111 个文件；91 个与上一目录相同，20 个新文件属于 orbit 2、3 证书包 |

上一目录的 11 个 `out/` 编译产物没有复制到新目录，不是正文内容删改。
远程引用通过实际 `git ls-remote --heads origin` 核对；本地已存在的远程对象
与其哈希一致。本地仓库是远程的子目录，因此两个 commit 哈希不同并不表示
内容不同。网页抓取没有成功，远程判断以 Git 的引用和 tree 核对为依据。

两个主文件的 SHA-256：

```text
main.tex
fb694c01b1144ce99d9a6d602c1a2629269bdd4c906a95fe9654f43f54a70958
supplementary.tex
a0f59088de371644a396fdd40ac218e4be803949b174a095c3233606c324cb37
```

完整目录哈希在 [inventory.json](../artifacts/manuscript-review-20261003/inventory.json)。

## 2. 按优先级排列的发现

### F1 — 高：全文验收仍明确失败，新日期尚无发布台账

`python tools/verify.py --paper-version 20261003 --only release` 实际失败，缺少
`results/paper-claims-20261003.json`。不仅 README 仍指向 20260929，最新日期也尚未
建立对应的声明、正文、勘误及 orbit manifest 记录。

因为两个主文件完全相同，20260929 的结果可以用于判断它们目前的情况，但不能
据此声称新增的两个片段也已纳入认证。现有台账实际是：

| 文稿 | covered | partial | unreviewed |
| --- | ---: | ---: | ---: |
| main.tex | 97 | 55 | 53 |
| supplementary.tex | 6 | 3 | 1489 |
| 合计 | 103 | 58 | 1542 |

正文审阅记录有 291 项：107 covered、121 tracked、34 gap、29 nonmath。
还有未纳入该记录的未改动正文。**这些是对应审阅的数量，不是已证明数学的
百分比；不能把 1542 未审阅项说成 1542 个尚无 Lean 证明的定理。**

实际执行的 `claims`、`prose-review`、`errata` 都失败。`axioms` 通过仅说明
所审计声明的信任基础合格，不会把这些失败变成全文验收通过。

处理：先确定最终合并稿，再建立该稿绑定的台账；逐项补桥接、复审、保留明确
标注的 conjecture。不能复制旧的 `covered` 状态来替代复审。

### F2 — 高：新版主文件仍保留不正确或缺限定的陈述

以下问题与 20260929 的勘误记录一致，本次重新核对了对应文字。

| 位置 | 问题 | 建议 |
| --- | --- | --- |
| main.tex:274–277 | 无条件 Singleton 界，在目前 KL 距离定义下对秩一不成立 | 按此前作者决定继续记录反例；若未来修改，补 `K >= 2` 限定 |
| main.tex:172–176 | 介绍中把 projective diagonal group 的有限性说成无条件结论 | 补固定 product basis、single-site Z detection（例如 d >= 2）条件 |
| main.tex:269–272 | 把所有 Pauli 的逻辑对角矩阵元要求都解释成平方振幅的矩条件 | 限于对角 Z 型错误；X/Y 型的对角矩阵元也依赖振幅相位，属于完整 KL 层 |
| main.tex:1825–1827 | 把 q_min 描述为对所有 physical representatives 的最小值 | 与 eq:qmin 一致，限定为 reduced diagonal representatives |
| main.tex:684–686 | rational replacement 被描述为不改变 homogeneous component | 改为保留矩阵像、两解之差属于 kernel；变化的正是 homogeneous direction |

有限性反例：取 `span{|00>, |10>}`，是一个距离一的秩二码。
`D(phi,0)` 在码上实现 `diag(1, exp(2 pi i phi))`，包含连续圆群；irrational phi
有无限 projective order。这是直接数学反例，本次没有新增其 Lean 证明。

q_min 问题也不只是措辞偏好：若允许任意码保持物理酉矩阵，可以把逻辑作用
调相至 m 次方为 identity，再在码的正交补上取 identity，得到物理阶 m。
这与文中例子 `q_min = 12 > m = 6` 使用的限制性最小值不是同一对象。

### F3 — 高：两个新枚举器结论尚未接入论文，也尚未接入 Lean

新增片段声称：

```text
W_2 = W_3 = { L(alpha) : 0 <= alpha <= 1 },
L(alpha) = (1, alpha, 1-alpha, 0, 11+4 alpha, 16-alpha, 3-3 alpha).
```

位置：orbit 2 片段:44–61；orbit 3 片段:75–81。
这两份证明的范围是选定物理 logical involution 的完整 enumerator image，
包含零振幅及奇异层；不是完整 LU 分类。

本次复跑的有限精确证据全部通过，分析归约中也没有发现新的明显推理断点：

- Orbit 2：从互补 purity 和 KL 推出 inactive pair flatness、active reflection；
  从 mixed KL 得到同一个 antiunitary，再用谱饱和导出 32 个 Pauli 坐标。
  四次证书检查 528 个 monomial、36 个零坐标、111 个正定块，共 492 个正坐标。
  这里同时工作的 antiunitary 与全部十二个 single-active Paulis 是关键前提。
- Orbit 3：先用六份有理 dual 得到五类零质量及 `A1+A2+A3=1`；随后将编码器
  写成一个 amplitude vector，构造实际编码器的正 three-copy averaged moment。
  六次恒等式以 211 个约束项消去 `3 N^3 A3 + 1280 V`，其中 V 是显式 cubic
  square 的平均，因而非负。`--exhaustive-target` 已重算全部 120 个目标行。
- 两份 reverse inclusion 的 split-qubit 构造都拉回至 pure perfect-five code；
  权重不超过二的物理错误拉回后仍只作用在不超过两个旧物理站点上。
  Singleton 在这里使用 K=2，不受秩一勘误影响。

但没有对应的新 Lean theorem 或 kernel replay；现有活跃 Lean 目录中未找到这些
新增 certificate、sextic 或 common-antiunitary 的开发。文件哈希、Python 成功
日志、甚至精确有理算术都不能替代这个缺口。

主文:2466–2468、2508–2529、2679–2681，补充材料:60–62、5333–5345、5682 起，
仍把 W_1 到 W_4 都写成未解决；主文摘要仍写 11 个已确定集合。
主文件没有 `input` 这两个片段。接受并合并新证明后，已确定集合应为 **13/15**，
剩余对应 W_1、W_4。15 个 realizable classes、51 个 no-go 以及 unrestricted
global conjecture 的范围不会因此改变。

处理：合并两个片段并统一摘要、表格、Result III、open-status 段及讨论；再分别
formalize 分析归约和有限证书，最后给出直接针对实际码的 WImage equality。

### F4 — 中高：Smith 桥接已补上，剩余的是对象与量词对应

[MainTheory/QECCSmithBridge.lean](../MainTheory/QECCSmithBridge.lean) 是有效的新增
进展。本次重新编译该文件成功。它用双向 divisibility 证明 cokernel exponent
等于 sharp inverse denominator，再对应实际 Smith witness 的 last factor；
对 nu >= 1，把 QECC.smithBeta 与 betaOf / BetaExact 接上。

但仍需要下列桥接，不能因这个文件通过就把整节或全文标为 covered：

1. **给定 gate 与内部选择的 representative。** QECC 的一般阶界及距离三阶界
   保存的 sourceRepresentative 是证明内部选出的 reduced representative。
   论文距离三 corollary 使用给定 D(theta) 的 eigenspace projector supports 和
   affine dimension。需证明相同 projective action 的逻辑 spectral projector
   在适当重标号下相同，及 rank-one diagonal support 等于 eigenvector support。
   或给出从指定 representative 出发的 theorem，再保留现有 existential wrapper。
2. **一般 K 的组合结论。** normal form 与 uniform order bound 各自的 existential
   witness 尚未在一个公开结论中统一。应对 bounded representative 直接构造
   SSLP outer data、colors、moments、KL completion，得到同一 witness 的有限搜索
   完备性；不是再证明一份独立的存在定理。
3. **66 个 keys 对论文 candidate classes。** 要包括 moment feasibility、
   support-dimension 条件及 `(q,m)` 保留的等价关系，并绑定 paperOrbitId 与
   表格行编号。现有 15 个 key 的 realizability 结果不自动完成这份定义对应。
4. **类级 W_r 的不变性。** 现有结论主要是表格代表的 `Levels.WImage`。应把
   completion transport 与 A-enumerator 的 permutation/flip/swap invariance
   合成公开定理，再提升为整个 candidate class 的 image equality。
5. **两条抽象 lemma 及七量子比特例子。** common-mean rational replacement 的
   论文抽象支持/子空间版本、positive-affine-moments 的任意有限实点集版本，以及
   worked example 的实际 supports、KL 距离二、C6 和最小物理阶 12 仍需对齐。

这些多数是已有证明库之间的接口收尾；不能据此判断数学陈述为假，也不应为了
适配现有 Lean 类型而默认缩小论文定理范围。

### F5 — 中：补充材料仍有 gate、bit convention 和引用问题

- supplementary.tex:2822–2842 的 orbit 7 cited gate，按 S=diag(1,i) 的字面读法
  在 theta=0 不保持所引 family；已有 kernel counterexample。
  S 换成 adjoint 的修正证明目前覆盖 five-qubit core。枚举器集合本身已有另一
  explicit family 的证明，因此应分开修 gate 引用与维持枚举器结论。
- supplementary.tex:4122 起 orbit 9 的六位 Dirac strings 需要明确哪端是 qubit 1。
  尾部:14735 起确实给出了 **CSV mask** 编码 `sum x_j 2^(j-1)`；这不能自动消除
  此处字面字符串与 `(x_1,...,x_6)` 次序的歧义。按左端为 qubit 1，`000111`
  对 `(1,1,1,1,1,2)` 的 subset sum 为 4，即 mod 3 为 1，不属于所写的 L0 fibre。
- supplementary.tex:5772 的硬编码 “Corollary III.4” 已失配；当前 rank-two
  corollary 是 III.5。应使用 label-based cross-reference。

### F6 — 中：审稿人端的重放材料和路径仍不完整

`.gitignore` 明确基于未公开合作者文稿的分发边界排除 `documents/`，本次也未修改
该规则。`git ls-files documents` 没有输出。因此 GitHub 当前有 Lean 与旧版本审阅
记录，但没有新版主文件或 orbit 2、3 包；只给仓库链接，审稿人无法完成与本地
相同的全部 source-binding 和新增证书检查。

另一个实际复现的限制是 `paper_release.binding` 在传入 `source_dir` 后仍读取
默认 `root/documents/version` 的文件来比较；`validate_review` 也依赖默认路径。
即使给出哈希完全一致的私有输入，缺少默认目录的 checkout 仍会 FileNotFound。
当前 README 把该参数描述为 table parser 的选项；它还不能充当整个验收流程
可移植的 private-source override。

处理：保留私有分发边界，提供有授权的 review bundle 或私有获取说明；或者让
所有来源检查读取同一显式输入目录，并与已记录的 SHA-256 比较。新的两个包
及其证书也要加入明确的来源绑定，而不是仅绑定 main/supplementary 两个文件。

### F7 — 低：orbit 2 表格的验证描述超过随附脚本的实际检查

orbit 2 片段:638–646、694–695 说每一块的 characteristic polynomial 已由 verifier
检查。随附脚本:239–288 实际重建矩阵并做 rational LDL positivity，**没有**
characteristic-polynomial 检查。其 positivity 证明已经足够，不影响 A3=0 结论。

本次额外用精确 SymPy charpoly 独立核对了全部 111 块，全部与表格一致。建议
把该额外 verifier 一并提供，或将文中描述改为实际执行的 LDL 检查。

## 3. 实际运行的检查

| 检查 | 结果与边界 |
| --- | --- |
| 两包 SHA256SUMS | 18/18 文件一致；manifest 自身不列在自身清单中 |
| Orbit 2 精确四次证书 | 通过；再生成的 blocks JSON 与分发 JSON 完全相同 |
| Orbit 3 六份 scalar dual | 通过；再生成 JSON 完全相同 |
| Orbit 3 六次证书 + exhaustive target | 通过；metadata JSON 完全相同 |
| Orbit 2 表格 charpolys | 111/111 独立精确核对通过 |
| QECC 原包与 root port | 46 个原有 module 字节相同；另外 3 个仅加兼容 import / genInjectivity option；root 相同 |
| Smith bridge fresh Lean elaboration | 通过，warningAsError=true |
| Bridge / QECC Audit dependency closure | 3932 模块内容验证缓存通过，0 个重建 |
| 完整本地 Lean source build driver | 14244 模块内容验证缓存通过，0 个重建；不是此次重新编译所有文件 |
| 20260929 release binding | 通过；两个主文件与本次版本字节相同 |
| source forbidden-token sweep | 14244 Lean sources clean |
| audit-names / named-results freshness | 通过 |
| transitive axiom gate | 1859 roots；仅 Classical.choice、Quot.sound、propext |
| 51 no-go modules 的 manifest / moment transcription | 全部通过；两组 mutation selftests 通过 |
| tools/tests | 116 passed，8 skipped，18 subtests passed |
| 20260929 claims / prose-review / errata | **失败**，不能算完整 release |
| 20261003 release binding | **失败**，缺少该版本 ledger |
| main / supplementary XeLaTeX 编译 | 都成功；未发现 unresolved ref/cite；有少量 overfull boxes 和 PDF bookmark 警告 |
| 静态 labels / refs / bibliography | 1560 labels、938 refs；无重复 label、缺失 ref 或缺失 citation key |

只有有限证书及列明的检查被实际执行。这里不把 numerical controls 当作 proof，
也不把未逐项复审的语义对应算作已验收。

日志及重算 JSON 位于 [artifacts/manuscript-review-20261003](../artifacts/manuscript-review-20261003/)。
主文和补充材料编译时复制至 `tmp/manuscript-review-20261003/tex`，没有写回原稿。

## 4. 建议的推进顺序

1. **统一最终稿与勘误记录。** 合并 orbit 2、3，统一 13/15 与 W1/W4 状态；
   Singleton 按已接受的“暂不改正文、记录反例”决定处理。其余文字修改由作者
   按本报告的具体位置决定，定稿后绑定 source hashes。
2. **先补已有库的对象桥接。** given-gate sectors/supports、class-level WImage、
   66 keys/numbering、general-K 同 witness 的 completeness。这一批最能直接
   提升主文核心定理的可审阅性。
3. **Orbit 2 kernel certification。** 分析归约 → 32-coordinate quartic identity
   → 每块 exact rational LDL certificate → 实际码 A3=0 → interval attainment
   → `WImage_orbit2` / class-level equality。
4. **Orbit 3 kernel certification。** scalar duals → 429 zero equations → 实际
   编码器的 positive moment → 269-coordinate exact identity → A3=0 与 attainment
   → `WImage_orbit3`。可考虑先将 Haar twirl 归约为所需有限阶 moments 的显式
   有限平均，但必须证明这些 moments 与实际编码器桥接；不能把 reduced moment
   coordinates 当作任意自由变量后直接宣称覆盖所有编码器。
5. **其余正文逐项复审与全套 release 验收。** 两个抽象 lemma、七量子比特 worked
   example、旧补充材料及全部正文引用；对数学 conjecture 维持明确身份。
6. **提供审稿人重放包。** 指定 branch/commit、pinned toolchain、来源哈希、
   私有稿件的获取/输入方式、新 certificate 与 Lean sources、成功及预期失败
   的检查说明。发布状态只在完整 gates 满足既定条件后改变。

Orbit 1、4 的完整枚举器 converse、unrestricted m=1 global conjecture，以及一般
LU family classification 仍是数学研究问题。若最终稿继续把它们明确列为
conjecture/open problem，认证应准确保留这种身份，不能把猜想当成已证定理。
