# SSLP class 36：审稿人复验指南

本套件包含标准案例的原始证据 ZIP、独立启动器 `sslp_reproduce.py` 和本指南。
不需要模型、网站连接码或原研究仓库，也不包含未发表文稿。
启动器只组织环境检查和执行；数学结论来自实际运行的 Lean 证书。

## 准备环境

需要 Python 3.10 以上、Git、[elan](https://github.com/leanprover/elan) 和可用网络。
安装的 Lean 版本由包内 `lean-toolchain` 固定为 `leanprover/lean4:v4.27.0`。
依赖源码按 `lake-manifest.json` 的具体提交获取，不执行 `lake update`。
mathlib 使用发布方的编译缓存；本项目的 11 个证明模块会在新目录重新编译。
因此这不是从源码重建整个 Lean 或 mathlib 的流程。

首次安装和缓存需要较多下载及磁盘空间。建议预留 25 GB；实际占用取决于平台。
只对从预期发布者获得的套件执行以下命令。SHA-256 能检查文件是否改变，不能自行证明发布者身份。

先安装固定 Lean 工具链：

```text
elan toolchain install leanprover/lean4:v4.27.0
```

然后解压本套件，进入含 `sslp_reproduce.py` 的目录。

Windows PowerShell：

```powershell
python -m venv .venv
$sslpPython = Join-Path (Get-Location) '.venv/Scripts/python.exe'
& $sslpPython -m pip install sympy==1.14.0 mpmath==1.3.0
& $sslpPython sslp_reproduce.py prepare class36-verification.zip --directory case-check --sha256 EXPECTED_BUNDLE_SHA256
& $sslpPython sslp_reproduce.py fetch case-check
& $sslpPython sslp_reproduce.py doctor case-check
& $sslpPython sslp_reproduce.py run case-check --output fresh-run --timeout 3600
```

Linux：

```sh
python3 -m venv .venv
.venv/bin/python -m pip install sympy==1.14.0 mpmath==1.3.0
.venv/bin/python sslp_reproduce.py prepare class36-verification.zip --directory case-check --sha256 EXPECTED_BUNDLE_SHA256
.venv/bin/python sslp_reproduce.py fetch case-check
.venv/bin/python sslp_reproduce.py doctor case-check
.venv/bin/python sslp_reproduce.py run case-check --output fresh-run --timeout 3600
```

若 Linux 的 venv 提示缺少 ensurepip，请按该发行版说明安装 Python 的 venv 支持。
这些命令不删除现有文件；`case-check` 和 `fresh-run` 必须是新目录名。
已完成的固定提交依赖可在重试 `fetch` 时继续使用；不完整或被修改的 checkout 会被拒绝，
不会自动 reset。改用新目录重新开始，或先人工检查具体失败日志。

## 看哪些结果

- `doctor` 逐项报告 Python、SymPy、mpmath、elan、固定提交依赖、mathlib 缓存和构建锁。
  它只检查就绪情况，不认证证明，也不把文件存在当成内容正确。
- `case-check/fresh-run-reproduction.json` 记录本次系统、初始本地缓存数量、耗时和新证据哈希。
  若 `initial_local_cache` 两项为 0、`kernel.rebuilt` 为 11，说明本项目证明模块从零构建。
- `case-check/fresh-run/evidence.json` 和 `lean.log` 是新执行的数学检查结果。
  应看到 `kernel.status = passed`，以及七个证明根仅使用
  `Classical.choice`、`Quot.sound`、`propext`。
- `case-check/fresh-run-execution.log` 保留环境检查、模块构建和证书执行日志。
  `setup-logs/` 保留安装依赖与获取缓存的日志。
- ZIP 自带的 `evidence.json` 是历史记录；`prepare`、`fetch`、`doctor` 都不能把它变成本机新证明。

失败、取消或超时不构成数学上的“不存在”结论。若 Lean 拒绝输入，应查看具体失败义务；
当前证明适配器只支持标准逻辑基，通过数值或精确 KL 的其他逻辑基也可能被它拒绝。

## 复验修改后的输入

先保留 `case.json`，把工作台导出的精确码字文件另存为 `candidate.json`。
该文件的 schema 应为 `sslp.code-instance.v1`，不是仅保存滑块参数的实验文件。
完成环境准备后，在 `case-check` 中使用同一 Python 环境运行：

```text
python tools/sslp_explorer.py verify candidate.json --lean --output candidate-run
```

这里的 `python` 须指向上文创建的 venv，例如 Windows 使用 `& $sslpPython`，
Linux 使用 `../.venv/bin/python`。新输入不会继承标准案例的证书。

## 范围和信任边界

证书涵盖输入振幅与标准码字相等、归一化、正交性、距离至少 3，以及假设 ζ⁵=1 时
固定物理相位层对任意逻辑叠加态的作用。它不涵盖全文、分类穷尽性、最小门阶或基本门编码器。

从网络重新获取依赖并在另一个操作系统重建，比同机复用已有依赖提供更多可复现性证据；
它仍不等于另一台物理机器或独立审稿人已经完成复验。启动器不自动声称独立机器验收。
可向作者提供 `fresh-run-reproduction.json`、`fresh-run/evidence.json` 和执行日志用于对照。
提交前检查本地路径等环境信息；其中不需要模型密钥或本机连接码。

## English quick reference

Use Python >= 3.10, Git, elan, and the pinned Lean 4.27.0 toolchain. Create a
Python virtual environment with `sympy==1.14.0 mpmath==1.3.0`. Run `prepare`
with the published ZIP SHA-256, then `fetch`, `doctor`, and `run`, as above.
Only `run` executes the fresh input-bound kernel certificate. Dependency
fetching uses exact Git revisions and the mathlib publisher cache. Read
`fresh-run-reproduction.json` and `fresh-run/evidence.json`; old bundled logs
are historical evidence. This single-instance certificate does not establish
whole-manuscript coverage or an elementary-gate encoder. The launcher has not
been tested on macOS; Windows and Linux evidence are documented separately.
