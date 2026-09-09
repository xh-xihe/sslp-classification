# 2026-09-08 全文 kernel Lean formalization 盘点

结论：尚未完成。核心六比特分类与大量一般定理已有形式化，但仍有明确数学缺口、全文对应关系未完成、当前源码构建与公理验收未通过。不能把已证核心分类与全文完成混同。

## 核对版本

- 本地 `master`: `0d4b1ec91bf2c8c5ed04f0659bcd2a286df70384`。
- GitHub `sixqubit-classification`: `f05c05bd8ce877052ad0d32ee444e6ac919b54ee`，经 `git ls-remote` 和只读工作区的 `git fetch --no-tags` 核对。
- 本地根目录与远端 `six-qubit-sslp` 子目录的 Git tree 均为 `d4631a3d52ed55e76f53a722e5db95f559003b5e`，`git diff --name-status HEAD FETCH_HEAD:six-qubit-sslp` 为空。提交号不同来自仓库布局不同，认证代码没有本地/远端差异。
- 开始审阅时工作区干净。本次只新增盘点报告并运行检查，不修改 Lean 证明和论文。

## 本次实际检查

| 检查 | 结果 | 解释 |
|---|---|---|
| 禁止信任绕过的源码扫描 | PASS，6699 个 Lean 文件 | 源码扫描通过不等于内核编译通过 |
| 已登记生成目录覆盖、SHA、依赖顺序 | PASS，819+1101+11+40 文件 | 仅覆盖该检查列出的四个生成目录 |
| 当前两篇 TeX 哈希、66 行基本字段、51 个 no-go 映射 | PASS | 不代表表格全部统计列均获数学证明 |
| gate、moment gate 及破坏测试 | PASS | 现有语义与负控制检查通过 |
| 源码层声明名称解析 | PASS | 是源码解析，不是加载当前内核环境 |
| 全文 coverage gate | **FAIL** | 首个阻断是 `main.tex:eq:physical-diagonal-stabilizer` 未核对 |
| Lean 声明存在性检查（README 与 ledger） | **FAIL** | 已缓存入口不能解析多项当前源码名称；不能据此把全部名称判为源码中不存在 |
| 当前联合公理审计 | **FAIL** | 首个错误：`MainTheory/CodePreservingUnitary.olean` 不存在；尚未进入完整根集合的公理收集 |
| 内容验证构建计划 | 6699 模块，1529 无验证 stamp | 有 stamp 的模块也要验证当前输入和依赖；不是说剩余模块都已通过 |

本次没有启动耗时的全库重建，因此没有宣称全库编译失败；明确发现的是缺失构建产物和没有当前完整验收。`.lake/build/certification/success.json` 不存在；保留的 `previous-success.json` 仅覆盖 51 模块（29 重建、22 缓存），不能充当全库证明。

本次日志：`tmp/audit-inventory-20260908-checks.log`、`tmp/audit-inventory-20260908-axioms.log`、`tmp/audit-inventory-20260908-build-plan.log`、`tmp/audit-inventory-20260908-labels.log`。检查程序写入的 `tmp/verification/axioms.json` 已反映这次未通过的尝试，不能再引用旧成功结果为当前提交背书。

## 已有进展，不应继续按旧报告列为缺口

- 核心 66 候选轨道、51 排除、15 实现，以及 11 个已确定枚举子像的形式化链。
- 全部四个 L 连续区间包含，以及 M 区间在 W1 与 W4 的交集包含；明确反向猜想保留猜想身份。
- 一般 KL 恢复 iff、实际 CPTP 恢复、Singleton、Smith 标准形存在性、任意局部酉枚举子不变性。
- `MainTheory/EastinKnill.lean` 已有任意有限且可不同的物理子系统维数的 no-universality 定理，并有实际 ExactCode 接口；不是仅有对角群有限性。
- 66 行的 `paperKey` 双射、实际存活记录的全部 multiplicity 及其总和 216 已有定理。
- 原先仅两行的 LP 维数实例，现扩展为 01、02、05、10、31、66 六行。
- 新增 phase-sector、一般彩色正规形、parity proviso、orbit 26/30 中间引理、协方差像空间、order-five 任意代码枚举子等论文接口。

这些是当前源码层和既有开发记录支持的进展列表；本次当前环境的联合公理审计未通过，不能把它表述成对所有这些新增源码已经重新独立验收。

## 明确还要处理的内容

1. **β7、β8、β9 的普遍上界。** 当前 `BinaryBetaSevenLower`、`BinaryBetaEightLower`、`BinaryBetaNineLower` 只有达到 18、42、120 的下界；全文源码搜索未找到对应 `BetaBound 7 18`、`BetaBound 8 42`、`BetaBound 9 120` 的证明。`GramPrefixBound` 是真实剪枝定理，但不等于覆盖所有二值矩阵的最终证书。`eq:small-beta` 与 `eq:6qubit-d2-bound` 因此仍不完整。这不是要求证明新的研究猜想，而是补齐论文已断言数值的形式化。六比特距离三主分类使用已证 β6=9，不因该缺口自动失效。

2. **完整 SSLP 管线的最终商与输出语义。** `thm:sslp-completeness` 的覆盖、cutoff、裸 KL 完成数据的逆向等已有证明，ledger 仍正确保留 partial。尚缺一般最终 intrinsic audit 与所选代码等价关系的商，确实返回目标分类数据的端到端声明。应形式化实际完成集合到实际 projector 等价商的映射及其可靠性、满射性/精确性；不能拿 66 个 support keys 当作 66 个代码等价类，也不必为此解决所有轨道的 LU 刚性。

3. **全部表格列的内核绑定。** `tools/verification/mkmanifest.py` 的正则读取统计列，但 `parse_table` 返回值仍不保存 r_*、d_LP、ν；因此 paper gate 的绿色不能证明这三列。ν 已有完整数学定理，LP dimension 的专门数值包装目前只有六行；需把剩余表项逐行映射到已有定理或补证，并提供全 66 行入口和对应检查。`supplementary.tex:tab:66orbits` 等表格条目仍未核对。

4. **逐式和 prose 的审阅收尾。** 当前 ledger 共 1597 项：313 covered、8 partial、2 conjecture、1274 unreviewed。其中正文 160 covered、8 partial、2 conjecture、91 unreviewed；补充材料 153 covered、1183 unreviewed。两篇 prose_review 均 unreviewed。未核对数量绝不是未证明数学命题数量，更不能计算成完成百分比；其中大量是定义、证明中间式和已有证明尚未映射的内容。应逐项确认或有依据地标注为说明性内容，不能直接批量视为完成。

5. **构建与最终验收。** 当前 `.olean` 和入口缓存落后于源码，至少最新 `CodePreservingUnitary` 的目标文件缺失。须完成内容/依赖验证的全库串行构建，修复真实编译和声明引用问题，随后重跑当前全部根的传递公理审计与 `python tools/verify.py`。本次 axiom gate 中止不能诊断为发现了额外公理；它意味着尚未核验到那一步。

## 文档状态也需要修正

旧 `certification-progress-20260905.md` 仍把 Eastin–Knill 和表格 multiplicity 留在进行中，已落后。README 的“正文所有 unreviewed displays 都已核对”与当前 ledger 中仍有 91 项正文 unreviewed 不一致。`label_sweep.py` 确实得到正文 33/33、补充材料 93/93 个 named results 在 Lean 中有引用，但标签出现仅是导航覆盖；不能据此推出定理每个子句、独立显示式、prose 和当前构建全部完成。

合理的完成顺序是：补最终 β 证书与管线商语义；补全表格绑定及全文审阅并同步状态文档；锁定源码版本，完成串行构建和全部验收。论文明确的 W1–W4 反向猜想不需要在这一认证任务中被解决。
