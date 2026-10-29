# PR #1 合并报告：Teichmüller 空间形式化阶段成果

报告日期：2026-10-29（北京时间）。

本报告说明 相对于 `main` 的交付内容、代码规模、数学完成程度与验证边界，供合并审阅和后续使用。数学状态取自当前来源台账与既有验收记录；本次整理没有重新进行全库数学审查。

**这次合并交付了一批完整证明、定义、复用接口与完整条件定理，以及可追溯的来源和未证命题说明。整项 Teichmüller 形式化仍未完成。** 224 个纳入范围的笔记编号目标中，105 项已证、12 项已定义、25 项复用、60 项有条件、22 项集中未证。登记中仍有 93 个具体未证命题；主值二阶变分是原文有证明、目前内部形式证明尚未补完的缺口。

**代码量方面，`LowDimensionalTopology/` 排除整个 `External/` 后，本 PR 新增 193,326 行、删除 106 行；其中 `.lean` 文件新增 193,298 行。** 这个目录范围约占本 PR 全部新增行数的 8.58%。其余新增内容包括第三方形式化、参考资料、数学笔记源文件、审查台账和开发工具，不能全部称为新写的数学证明。

## 1. 报告基准与统计范围

### 1.1 新增行数的准确口径

下表前两行是互不重叠的范围，末行为合计：

| 范围 | 变更文件数 | 新增行 | 删除行 | 净增加 |
| --- | ---: | ---: | ---: | ---: |
| `LowDimensionalTopology/`，排除 `External/` | 1,351 | **193,326** | **106** | **193,220** |
| PR 中的其余文件 | 2,211 | 2,060,732 | 72 | 2,060,660 |
| **整个 PR** | **3,562** | **2,254,058** | **178** | **2,253,880** |

在第一行的 1,351 个文件中，1,350 个是 `.lean`：1,342 个新文件、8 个修改文件，合计新增 **193,298** 行、删除 **106** 行、净增加 **193,192** 行。余下一个新文件是 `LowDimensionalTopology/Unproved/README.md`，共 28 行。仓库根目录的 `LowDimensionalTopology.lean` 不在所问目录内，且在本次比较中没有变化。

这里统计的是 diff 的插入、删除行，包含空行、注释、导入语句、定义、命题陈述和证明。它既不是剔除注释后的有效代码行数，也不等于独立定理数。排除 `External/` 是明确的路径口径，不表示剩余每一行都具有独立原创性，也不表示每个文件内的结论都无条件成立。

### 1.2 排除 External 后的目录分项

下表路径均相对于 `LowDimensionalTopology/`，各行互不重叠：

| 路径 | 变更文件数 | 新增行 | 删除行 |
| --- | ---: | ---: | ---: |
| `Geometry/Teichmuller/` | 809 | 132,989 | 0 |
| `Geometry/Quasiconformal/` | 142 | 20,669 | 0 |
| `Geometry/Surfaces/` | 155 | 18,545 | 83 |
| `Geometry/Hyperbolic/` | 100 | 9,798 | 23 |
| `Unproved/`，含 28 行 README | 97 | 5,435 | 0 |
| `Geometry/Fuchsian/` | 20 | 1,691 | 0 |
| `Geometry.lean`，公共导入入口 | 1 | 1,347 | 0 |
| `Geometry/Auxiliary/` | 11 | 1,277 | 0 |
| `Geometry/SeveralComplexVariables/` | 6 | 750 | 0 |
| `Geometry/Mobius/` | 5 | 470 | 0 |
| `Geometry/Polygon/` | 3 | 222 | 0 |
| `Geometry/DiscreteGroups/` | 1 | 83 | 0 |
| `Geometry/Complex/` | 1 | 50 | 0 |
| **合计** | **1,351** | **193,326** | **106** |

`Unproved/` 中的 96 个 Lean 文件新增 5,407 行，主要用于陈述具体命题、保留参数化接口及其必要定义；不能把这些行数都当成已经完成的证明。`Geometry.lean` 的 1,347 行增加主要是导入项，也不能解释为 1,347 个新增定理。

### 1.3 为什么整个 PR 有两百多万行

本 PR 同时带入几类体量较大的内容：

- [第三方形式化](LowDimensionalTopology/External/)：本次比较有 407 个新增文件，保留原作者、许可、固定上游与本地适配记录。详细归属见 [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)。
- [参考资料](docs/references/)：包括指定参考书及提取文本、LearningMath 的完整源文件与图形资料；不能按全部新增行数计算本轮证明工作。
- [既有 Geometry 审查记录](docs/geometry-audit/)及 [Teichmüller 来源台账](docs/teichmuller/coverage.json)：例如，前者的 `coverage.json` 单个新增文件就有 313,414 行。这些行记录审查与来源，并非 Lean 证明。
- [Archon 工具接入](.internal/archon/README.md)及其固定上游源码、来源清单和开发检查。它们属于开发工具，不属于所问的数学源码目录。

因此，评估本次合并时，应分别考察数学接口和证明、外部代码复用、来源资料及工程记录，而不是以整个 PR 的新增行数衡量新数学成果。

### 1.4 统计方法

本次行数统计通过 GitHub API 完成：整个 PR 的文件数和新增、删除行数取自固定基准时的 PR 元数据；所问目录的计数取自完整文件树与分页文件统计；其余文件一行由差额计算。下列本地 `git diff` 命令作为复算入口提供，本轮没有在本地执行这些命令。

统计时先比较两个固定提交的完整文件树，确认目标范围共有 1,351 个变更文件且没有删除文件，再对照 PR 文件统计。大型 diff 接口曾把三个非空 Lean 文件的新增行数返回为 0；改用每页 20 个文件重新核对全部目标文件，并直接读取这三个 Git blob，确认它们分别为 156、73、198 行，已全部计入上述总数。不能直接把大分页中这些 0 当成实际行数。

## 2. 数学范围与状态口径

数学陈述以 Imayoshi–Taniguchi 的 *An Introduction to Teichmüller Spaces* 英文原著第 1–8 章为准，以 LearningMath 第二十部分及其实际 TeX 确定本轮目标和证明范围。明确排除笔记 §76.2.4／英文 §7.2.4 与 Kodaira–Spencer 形变理论的联系；普通注记、例和脚注通常不单列，目标证明确实需要的内容另行追踪。附录 A、B 没有被声称整体形式化。范围依据见 [任务约定](docs/teichmuller/AGENTS.md)及[来源与实现映射](docs/teichmuller/coverage.json)。

“224 个编号目标”按中文笔记的编号统计，其中包含定义、引理、命题、定理、推论与补充结论；它不是英文原书有编号定理的总数。321 条未编号支持定义记录还可能与编号目标链接到相同数学对象。因此，551 是来源记录总数，不能称为 551 个互不重叠的定理。

| 状态 | 本报告采用的含义 |
| --- | --- |
| 已证 | 当前目标已有完整证明，没有集中登记的未证输入；仍保留定理通常的数学假设。 |
| 已定义 | 数学对象或概念已有实现；不把定义本身计作证明。 |
| 复用 | 由既有完整 Lean 实现承接目标，来源与映射保留在台账。 |
| 有条件 | 后续结论已有完整证明，具体尚未证明的输入仍作为显式前提。 |
| 集中未证 | 有具体数学内容的 Lean `Prop`，并登记来源、原因及消费者，但没有该命题的证明。 |

这些含义来自 [PROGRESS.md](docs/teichmuller/PROGRESS.md) 和 [unproved.md](docs/teichmuller/unproved.md)。尤其应区分“定义一个命题”与“拥有这个命题的证明”：`def : Prop` 本身不承认该命题成立，不等于新增公理。

## 3. 当前完成程度

### 3.1 来源记录总表

| 来源记录类别 | 已证 | 已定义 | 复用 | 有条件 | 集中未证 | 合计 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 笔记编号目标 | 105 | 12 | 25 | 60 | 22 | 224 |
| 未编号支持定义记录 | 0 | 210 | 48 | 61 | 2 | 321 |
| 英文补充及分离义务 | 2 | 0 | 0 | 4 | 0 | 6 |
| **来源记录合计** | **107** | **222** | **73** | **125** | **24** | **551** |

6 条补充记录包括英文 2.15、3.11 两条已证结果，以及测度叶状结构交数识别、TT 张量与二次微分对应、原生张量 L² 配对性质、水平度量几何四条条件义务。上述各类记录待处理数均为 0，但机器台账仍保留 `IN_PROGRESS` 和 `full_atomic_scope_complete = false`；待处理为 0 表示已经给出明确处置，不能据此宣称所有证明义务完成。

### 3.2 各章编号目标

| 原著章节／笔记章号 | 编号目标 | 已证 | 已定义 | 复用 | 有条件 | 集中未证 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 第 1 章／70：亏格 g 的 Teichmüller 空间 | 14 | 7 | 4 | 1 | 2 | 0 |
| 第 2 章／71：Fricke 空间 | 34 | 14 | 3 | 15 | 2 | 0 |
| 第 3 章／72：双曲几何与 Fenchel–Nielsen 坐标 | 25 | 5 | 1 | 0 | 11 | 8 |
| 第 4 章／73：拟共形映射 | 51 | 39 | 3 | 2 | 6 | 1 |
| 第 5 章／74：Teichmüller 空间 | 23 | 11 | 0 | 1 | 10 | 1 |
| 第 6 章／75：Teichmüller 空间的复解析理论 | 49 | 19 | 1 | 6 | 12 | 11 |
| 第 7 章／76：Weil–Petersson 度量 | 16 | 8 | 0 | 0 | 7 | 1 |
| 第 8 章／77：Fenchel–Nielsen 形变与 WP 度量 | 12 | 2 | 0 | 0 | 10 | 0 |
| **合计** | **224** | **105** | **12** | **25** | **60** | **22** |

各章的未编号支持定义记录数依次为 45、31、38、23、39、65、61、19，共 321 条。逐项原著定位、笔记编号、Lean 声明和未证依赖见[按章进度](docs/teichmuller/PROGRESS.md)及[机器台账](docs/teichmuller/coverage.json)。

### 3.3 93 个未证命题与 15 个已有证明接口

[集中登记](docs/teichmuller/unproved.json)按唯一 ID 计数，共 108 项：**93 项 `UNPROVED`，15 项 `PROVED`**。这里的统计单位是具体前置命题或参数化接口，与上表中的编号目标不同。

- 93 项包含条件定理使用的具体前提；不能与 22 个集中未证编号目标相加，也不能相互替代。
- 15 项表示原参数化命题已经有实际证明接口，其中部分仍接收其他未证输入。它们不能直接加到 105 个无未证输入的已证编号目标中。
- 数据定义的消费者与条件定理的消费者分别登记；构造一个显式接收未证输入的数据对象，不算证明该输入。

例如，对角核控制和混合核控制已有证明接口，但仍显式依赖完整主值二阶变分等输入。这些接口的完成没有消除完整主值分析的缺口。详见[未证命题中文说明](docs/teichmuller/unproved-guide/README.md)。

## 4. 值得报告的数学成果

以下是当前分支已经交付的代表性结果；具体状态以固定提交的台账为准。这是成果与接口的说明，不以此替代对全部声明的逐项核对。

### 4.1 标记曲面、覆盖与一般 Teichmüller 构造

环面周期参数的 PSL(2, Z) 轨道判别、有序标记环面的参数唯一性，以及 Beltrami 系数的复合律和轨道商描述已有完整证明。对应入口包括[环面模型](LowDimensionalTopology/Geometry/Surfaces/Euclidean/NormalizedTorusModel.lean)、[有序标记环面](LowDimensionalTopology/Geometry/Surfaces/Euclidean/NormalizedOrderedMarkedTorus.lean)、[Beltrami 复合律](LowDimensionalTopology/Geometry/Teichmuller/BeltramiComposition.lean)和[实际轨道描述](LowDimensionalTopology/Geometry/Teichmuller/RealizedBeltramiOrbits.lean)。

覆盖部分包含指定基点的提升及其正则性保持，以及阿贝尔基本群曲面的分类。另已证明：对实际上半平面全纯自同构的阿贝尔子群，若其非单位元无内部不动点且原作用正常不连续，则该子群是循环群，平凡群也包括在内。一般高亏格曲面上的两种 Teichmüller 构造比较（70.18）及度量商重建（70.27）目前仍是条件定理，保留曲面分类、实现等具体输入；不能由环面结果推断这些一般比较已无条件闭合。

### 4.2 双曲几何、裤分解与 Fenchel–Nielsen 坐标

Schwarz–Pick、圆盘最短测地弧、闭测地线长度与双曲元素平方迹之间的关系等结果已有证明；相关入口见[Schwarz–Pick](LowDimensionalTopology/Geometry/Hyperbolic/Models/Disk/SchwarzPick.lean)、[测地弧](LowDimensionalTopology/Geometry/Hyperbolic/Geodesic/PoincareGeodesicArcs.lean)和[闭测地线长度](LowDimensionalTopology/Geometry/Surfaces/Hyperbolic/OriginalClosedGeodesicLength.lean)。

裤分解与 FN 坐标已经有对象、几何数据和相应条件接口，完整 FN 坐标同胚（72.20）仍属有条件结果。75.34 的 Hubbard 分解是条件证明，有限曲线束的延拓（75.35）、完整测地领口族及若干曲面拓扑前置仍集中未证。这里不能把“已有 FN 坐标接口”表述成所有裤分解存在性和图示几何均已证明。

### 4.3 拟共形分析与英文 Hilbert 三引理

英文 Lemma 4.38、4.39、4.40（笔记 73.51–73.53）均已有完整证明。这三条是明确追加的英文证明目标，不能因中文笔记原先省略或未完成而从范围中排除。

所交付内容包括实直线 Hilbert 变换的 Riesz 估计、实际平面 Lᵖ 有界复线性算子的构造，以及在同一实际算子与原测试函数范围下的 `Tφ = −S(Sφ)` 分解。证明接口保留 p ≥ 2、同一连续常数族、A₂ = 1 及相应主值识别。入口见 [RealHilbertRiesz](LowDimensionalTopology/Geometry/Quasiconformal/RealHilbertRiesz.lean)、[CircularHilbertLpConstruction](LowDimensionalTopology/Geometry/Quasiconformal/CircularHilbertLpConstruction.lean)和[分解存在性](LowDimensionalTopology/Geometry/Quasiconformal/CircularHilbertFactorizationExistence.lean)。

### 4.4 Bers 理论、模群作用与长度谱

已证内容包括实解析拟共形代表、实际 Bers 投影在一般系数处的导数、参考曲面变换的双全纯等价、原 Teichmüller 空间上的模群正常不连续作用，以及闭曲面长度谱的离散性等。代表入口见[一般系数处的 Bers 导数](LowDimensionalTopology/Geometry/Teichmuller/NativeNonzeroBersIntegralKernel.lean)、[参考变换](LowDimensionalTopology/Geometry/Teichmuller/ReferenceChangeBiholomorphic.lean)、[模群作用](LowDimensionalTopology/Geometry/Teichmuller/NativeModularProperAction.lean)和[闭长度谱](LowDimensionalTopology/Geometry/Surfaces/Hyperbolic/OriginalClosedLengthSpectrum.lean)。

完整 Royden 结论、Kobayashi 与 Teichmüller 距离相等、Stein 性、若干 Mumford 紧性与拓扑输入仍集中未证；Nielsen–Thurston 分类（75.52）是保留这些相关前提的条件结果。

### 4.5 Weil–Petersson 解析基础与曲率

自守二次微分的再生公式、Poincaré 级数的绝对及局部一致收敛、Bergman 投影及其自伴性、无穷小平凡 Beltrami 系数的零化子刻画等已有完整证明。入口见[再生公式](LowDimensionalTopology/Geometry/Teichmuller/HalfPlaneQuadraticReproduction.lean)、[Poincaré 级数](LowDimensionalTopology/Geometry/Teichmuller/DiskPoincareSeries.lean)和[Bergman 投影](LowDimensionalTopology/Geometry/Teichmuller/NativeBergmanProjection.lean)。

WP 局部系数的完整光滑性（76.23）仍集中未证；WP 模群不变性（76.24）、Kähler 性（76.25）、Ricci／标量／全纯截面曲率的负性（76.29）目前均为条件定理。原生张量 L² 配对、TT 对应与水平几何也保留各自的具体输入。分析基础已经推进，不能据此省去这些全局与变分前提。

### 4.6 FN 形变、Wolpert 公式与长度收缩

简单闭测地线长度的一阶变分（77.6）已有完整证明。原 FN 扭转的级数公式、长度对偶与互易性，以及 77.12 的 Wolpert 辛形式公式和 77.13 的长度坐标向量收缩公式已有完整条件证明，按各条声明保留实际标记、相应 FN 参考和匹配见证，并使用原书规定的归一化。77.9 的互易性允许两条原简单闭测地线使用各自独立的完整 FN 参考及左侧标签，也允许两条曲线相交。

令角度为 Θ、裤边长度为 ℓ，并取缩放扭曲坐标 τ = ℓΘ/(2π)。当前采用的英文约定为：

$$
g_{\mathrm{WP}}=2\operatorname{Re}h_{\mathrm{WP}},\qquad
\omega_{\mathrm{WP}}=\sum_j d\tau_j\wedge d\ell_j,\qquad
\iota_{\partial/\partial\ell_j}\omega_{\mathrm{WP}}=-d\tau_j.
$$

辛形式公式的系数为一。匹配参考、FN 光滑逆与运输、原书图示中的侧别和反射几何等具体前提仍显式保留。源码入口见[长度变分](LowDimensionalTopology/Geometry/Teichmuller/OriginalGeodesicPeterssonVariation.lean)、[Wolpert 公式](LowDimensionalTopology/Geometry/Teichmuller/OriginalFNBookSymmetricSelection.lean)和[长度收缩](LowDimensionalTopology/Geometry/Teichmuller/OriginalGeodesicBookLengthContraction.lean)。

## 5. 尚未完成的部分及合并后的使用边界

最需要保留的内部缺口是 `weil-petersson-principal-value-second-variation`。英文原著和中文笔记均给出了具体证明，当前缺的是这些主值、收敛、参数微分、交换与展开步骤的完整内部形式证明。它不能被改称为“原文没有证明”或“仅外引文献”，也不能因为下游已得到条件定理而改记为已证。

此外，曲面拓扑和分类、若干图示几何、拟共形平滑化、Eichler jets、WP 光滑性、FN 运输与反射等前置仍各自保留为具体命题。它们的完整陈述、来源、未证原因、已有 producer 和实际消费者见 [unproved.json](docs/teichmuller/unproved.json)，阅读版见 [unproved.md](docs/teichmuller/unproved.md)。

本阶段按既定预算安排暂缓补证这些登记命题。合并不会改变它们的逻辑状态：调用条件定理仍需提供相应输入；不能把登记命题、数据定义或结构名称当成该输入已经获证的依据。未交付草稿保存在恢复分支，未计入本报告的完成数量。

整项任务的最终完成标准仍按[任务约定](docs/teichmuller/AGENTS.md)保留，其中包括实际通过 `check_coverage.py --require-complete`。普通台账一致性检查允许保留未完成义务，其通过不能代替整项最终验收。本次报告没有宣称该最终门槛已满足。

## 6. 来源对照、归一化与复用

当前台账有 53 条来源修正记录，见 [source-differences.md](docs/teichmuller/source-differences.md)。这些记录包括原著与笔记差异、实现修正、归一化选择以及对先前误读的撤回，不能简单称为“发现 53 个数学错误”。会直接影响读者理解的例子包括：

- 高亏格曲面的基本群使用全部换位子乘积为单位元的曲面群关系。
- 全局 Beltrami 系数按实际坐标变换律拼接，不能当成普通全局标量函数。
- 本书 Teichmüller 距离采用 `inf log K`，二次微分 L¹ 范数采用 `2∬|φ|`；不同常数约定会传递到后续公式。
- WP 度量与辛形式采用英文原著的规范，77.12 不带额外的 1/2，77.13 保留负号。
- 英文扫描缺印刷页 213、重复 217；该来源限制已记录，不能通过统一页偏移掩盖。

来源差异文件含历史状态叙述；判断某条目前是否已证或仍有条件，应优先使用当前 `PROGRESS.md`、`coverage.json` 与 `unproved.json`。

复用方面，Mathlib 是必需基础库；`External/` 的已有形式化与本地适配保留真实作者、许可证、固定上游提交和对应清单。本 PR 的规模包括这些复用成果，不将它们重新署名为从零编写的工作。完整信息统一见[来源与致谢](THIRD_PARTY_NOTICES.md)。Archon 的来源、内置组件与本地适配边界另见[工具致谢](.internal/archon/NOTICE.md)。

## 7. 已有验证证据与当前 CI

最近一次已登记的源码验收为：

| 验证项目 | 已登记结果 |
| --- | --- |
| Archon | 实际诊断、完整声明类型与证明状态核查 |
| 基础测试 | 84 项通过 |
| 台账测试 | 117 项通过 |
| 七项常规检查 | 全部通过，包含拒绝警告的全库构建 |
| 传递公理审计 | 3,151 个项目所属模块、106,247 条声明；只允许 `propext`、`Classical.choice`、`Quot.sound` |

本分支固定 Lean `v4.35.0` 和 Mathlib `v4.35.0`，实际依赖由 [lean-toolchain](lean-toolchain)、[lakefile.toml](lakefile.toml)及 [lake-manifest.json](lake-manifest.json)确定。开发、获取缓存与常规验证命令见[根目录 README](README.md)。
