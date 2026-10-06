# 全文认证持续实施记录

目标仍在进行。初次审阅见 `certification-audit-20260905.md`；该报告记录的是实施前快照，不应把其中所有缺口继续当作当前状态。

## 已完成的新证明

- `MainTheory/PauliKernelBTrace.lean`：任意矩阵的真实投影压缩迹；接到 B 的 `1/K` 归一化。
- `MainTheory/KLWeightEquality.lean`：任意 n、K 下 KL 推出低权 A=B。
- `MainTheory/SixQubitExactDistance.lean`：六量子比特秩二代码不能检测所有权三 Pauli；距离至少三时距离恰为三。
- `MainTheory/SharpSectorZDetection.lean`：仅假设检测各 Z_j，使用实际不同本征值数的尖锐界与最小 lift。
- `MainTheory/RealSupportAffineRank.lean`、`D3AffineRankBound.lean`、`D3AffineNormalForm.lean`：任意 n 的真实实仿射支撑秩、翻转/置换不变性、原逻辑作用上的 sharp-r lift、保留目标距离的完整正规形及同一 q 的 Smith 整除证书。
- `MainTheory/FiveQubitRationalization.lean`：显式归一化代码、完整权一 KL、ZZ 权二反例、共同均值、参数族及辅助线性系统；无理 t 的真实物理算符无限阶；同一内禀类的三阶和六阶 lift、六阶分母最小性、q_min=3。
- `MainTheory/MacWilliamsPolynomial.lean`：任意 n、K 的齐次多项式 MacWilliams 公式及系数归一化。
- `SixQubit/Orbit8RaisingGram*.lean`：实际升算符 Gram 的平方关系和具有完整重数的特征多项式。
- `SixQubit/Orbit9Magnitude*.lean`：任意允许代码的普遍幅度模式；在原始64点cube上每字恰有10个1/12和1个1/6。
- `MainTheory/GeneralSectorMoments.lean`：任意正重数扇区的真实投影对角概率及所有低于距离阈值的二进制矩相等。
- `MainTheory/GeneralColoredTheory.lean` 及其依赖：任意 K 的彩色标准形与逆向，保留原内禀类及目标距离；正扇区维数之和、实际本征子空间、完整纤维、原始颜色与精确逻辑阶。
- `MainTheory/LPDimension.lean`、`LPActiveDimension.lean`、`LPRationalFeasibility.lean`：实际非负 LP 可行集的活跃坐标与仿射维数；有理系数下实可行性、有理可行性及严格正坐标可行性的等价。
- `SixQubit/Orbit31Moment*.lean`：实际矩方程的双向参数化、23×32 系数矩阵秩23与非负矩多面体仿射维数9。
- `MainTheory/FlipCharacterObstruction.lean`、`FullRankFlipObstruction.lean`、`MatchedFlipObstruction.lean`：two-edge/full-rank/matched-ten 通用实际 KL 障碍，保留零概率边界。
- `MainTheory/LocalUnitaryEnumerators.lean` 及其依赖：任意局部 U(2) 与置换下的实际 A/B 枚举子不变性；LU 等价闭包与单次局部张量积及置换表示等价。
- `MainTheory/QuantumSingleton.lean` 及其依赖：实际 ExactCode 在 K≥2 时满足 2(d−1)≤n 和 K≤2^(n−2(d−1))；从 Pauli KL、任意低权张量算符、实际分区矩阵单位和纯度不等式贯通。
- `MainTheory/SmithNormalFormExistence.lean` 及五个依赖模块：任意非奇异整数矩阵的真实双侧可逆 U,V、正因子与完整整除链，最后因子等于 sharp inverse denominator 及 det/gcd(cofactors)。四个根传递公理审计通过。
- `MainTheory/ParityFourConnectivity.lean`、`ParityFourPolytope.lean` 及依赖：实际 full-parity 归一化非负矩概率族与 L1≤1 参数化双向等价及唯一性；真实可行集仿射维数4、正概率支撑图及坐标切片的 Hamming-one 连通性（允许空切片）。
- `MainTheory/QuantumRecovery.lean` 及依赖：实际投影 KL 方程与 CPTP Kraus 恢复的完整 iff；任意 ancilla 下完全正性；未归一化错误集的一致恢复、低权错误线性包中全部 TP 噪声的共同恢复与 floor((d−1)/2) 纠错半径。12个语义根的传递公理审计通过。
- `MainTheory/WImageOrbit4M.lean`：实际六比特支撑和完整 Pauli 系数证书推出 M([2/3,1])⊆W4，包含两个端点；11个生成模块逐一内核编译通过，重生成哈希一致。
- `MainTheory/WImageOpenL.lean`：全部40个生成系数模块与统一语义入口通过内核检查，得到 L([0,1])⊆W_r（r=1,2,3,4）；M 的入口也已合并为论文原文的 W1∩W4 包含。连续参数和全部端点均覆盖。
- `MainTheory/ParityFourPaper.lean`：补齐逐式 Fourier 表达、所有二阶 Fourier 系数为零、内部严格正性、边界非零坐标的 sign 求和恒等式与实际正支撑充要条件。

上述文件均已逐个以 Lean 4.27.0 编译，无警告；所选根的联合传递公理审计持续更新。还没有完成全库当前源码冷构建，不能据此宣布全文最终通过。

## 文稿与验收

- 正文 Singleton 的陈述补上 K≥2，避免已内核证实的 rank-one 反例。
- 补充材料旧的“轨道1–4存在性未解决”改为完整枚举子像未解决；十五轨道已有精确实现。
- 验收包装器修复非零退出码漏报，采用 Lean 官方收集器共享遍历、公理白名单、生成数据哈希、当前两文稿和66行表对应、实际语义与反向破坏测试。
- `tools/build_lean.py` 提供按依赖顺序单进程、内容及依赖哈希验证的构建；旧缓存不自动升级为认证缓存。
- 工具回归测试和当前非 Lean 语义/数据检查通过；另以真实 Lean 正反例检验缺失声明、额外公理和警告拒绝。编译器标志统一修正为 `-DwarningAsError=true`。
- 更新后的联合公理审计已通过1171个目标（`tmp/verification/axioms.json`），联合依赖仅 `Classical.choice`、`Quot.sound`、`propext`；此后加入的目标仍需下一轮审计。实际内容验证串行构建已从源码成功重建完整 `SS` 入口的13个模块，仅验证该依赖闭包，不能代替全库构建。
- `tools/paper_claims.py` 建立覆盖清单，同时纳入未标号公式和独立 prose review。初始解析1597项候选，**这不是1597项数学缺口**；大部分需要把已有证明逐项登记核对。任何未核对项目使最终完整性检查失败。

## 当前并行工作

- β7–9：外部精确原型已完成 n7、n8 高行列式 Gram 分支探索；正将覆盖、对称变换和剪枝不等式逐一形式化。原型数值结果还不是内核证明。
- Eastin–Knill：不假设有限生成的有界指数酉群有限性已经编译；任意有限维局域系统的实际横向逻辑作用及去除全局相位的忠实表示正在接合。
- 完整66行表的实际列语义；现有证书已支持全部三列的独立精确生成输入复核，仍待 Lean 语义包装及生成秩证书。

## 仍需完成的主要工作

1. 四个开放轨道的完整反向像仍是文稿明确标注的猜想；已声称的连续族正向包含全部完成，无需把猜想改成假设。
2. β7、β8、β9 上界与精确值；β7 对应六量子比特距离二的18截止值。
3. 所有表格列和分组统计的实际语义；当前66行解析器未保存 r_*、d_LP、ν 这三列，不能以文稿哈希绑定代替其数学证明。
4. 独立数值矩阵等逐式覆盖核对。
5. 所有 transversal gates 的 Eastin–Knill。
6. 完整 SSLP 程序规格、逐项论文覆盖核对、全库源码构建和最终全部验收。

后续更新应保留未完成项，不能用缩弱结论、外加未证明假设或数值采样换取完成状态。
