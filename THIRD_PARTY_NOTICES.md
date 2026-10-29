# 来源与致谢

## Mathlib4

本项目以 [Mathlib4](https://github.com/leanprover-community/mathlib4) 为必需依赖。
准确版本与提交见 `lakefile.toml` 和 `lake-manifest.json`。Mathlib 按 Apache License 2.0 发布，
版权归相应贡献者所有；Lake 管理的外部依赖不被重新署名为本项目原创代码。
群、矩阵、四元数、分析、拓扑、度量和流形等基础广泛复用其公开 API，感谢相应上游贡献者。

## Archon

形式化工具使用 [frenzymath/Archon](https://github.com/frenzymath/Archon)，按 Apache License 2.0 发布。
开发中采用的版本为 `0.3.3`，固定提交为
[`3fe2618870808d8c20912ab8b5aff80af275a1de`](https://github.com/frenzymath/Archon/tree/3fe2618870808d8c20912ab8b5aff80af275a1de)；
完整工具源码保存在 `.internal/archon/upstream/`，保留
Copyright 2026 FrenzyMath、[完整许可证](https://github.com/frenzymath/Archon/blob/3fe2618870808d8c20912ab8b5aff80af275a1de/LICENSE)与
[上游第三方声明](https://github.com/frenzymath/Archon/blob/3fe2618870808d8c20912ab8b5aff80af275a1de/THIRD_PARTY_NOTICES.md)，不在本项目重新署名。
内置 lean4-skills（Copyright (c) 2025 Lean 4 Theorem Proving Skill Contributors）和
lean-lsp-mcp（Copyright (c) 2025 Oliver Dressler）为 MIT 许可的修改版；各自完整许可证随源码保留。
准确来源、逐文件原始及本地哈希、树内符号链接、三个构建缓存文件的排除及本地适配边界见
`.internal/archon/source-manifest.json` 和 `.internal/archon/NOTICE.md`。

## Tau Ceti

曲面的 Euler 特征及其同胚不变性复用
[TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti/tree/1f9b4414105d86e487a4ac4c3d3397076a44d0d2)，
固定提交 `1f9b4414105d86e487a4ac4c3d3397076a44d0d2`，Apache-2.0。
移入的 95 个模块保留原作者与版权头，调整本地 import 前缀，并将九个证明依赖的 import 改为 public import。
准确原始文件、本地文件、哈希和修改见[来源清单](LowDimensionalTopology/External/TauCeti/source-manifest.json)，
完整许可见 [LICENSE](LowDimensionalTopology/External/TauCeti/LICENSE)。感谢 The Tau Ceti contributors。
实际 handle 曲面的胞腔分解及亏格唯一性连接证明由本项目编写。
本轮从同一固定提交另选取 van Kampen 商呈示及圆周楔和基本群所需的 46 个模块；
作者、逐文件原始与本地哈希及 import 修改见
[扩展清单](LowDimensionalTopology/External/TauCeti/VK_EXTENSION_UPSTREAM.json) 与
[补充致谢](LowDimensionalTopology/External/TauCeti/NOTICE.VK.md)。它们尚待当前工具链编译与公理审计。

## LeanPool

本项目适配 [LeanPool/lean-pool](https://github.com/LeanPool/lean-pool) 的拓扑、复分析及曲面基础，
固定提交 `86da5902e640ceb44e53f88c4a04f870dc062126`，Apache-2.0。
Álvaro Begué 的 Schoenflies 与 Jordan 曲线发展、Rado Kirov 的路径和复曲面基础等代码保留原作者、版权头及许可证。
具体原始文件、Git 对象、本地兼容修改和声明对应见 [总来源记录](LowDimensionalTopology/External/LeanPool/UPSTREAM.json)
及各子目录的 NOTICE、UPSTREAM 清单，完整许可见 [LICENSE](LowDimensionalTopology/External/LeanPool/LICENSE)。

## Uniformization 依赖

一般一致化证明依赖适配
[LR-UK/Bounded-orbit-wandering-domains](https://github.com/LR-UK/Bounded-orbit-wandering-domains)，
固定提交 `6e306deb8169e834e9cc6662160c70231a7e2a83`，Apache-2.0。
保留 Will (Ziang) Li、Geoffrey Irving、Yury Kudryashov 等原作者的真实归属和版权声明，
其中次级来源、固定提交及完整许可证见 [NOTICE](LowDimensionalTopology/External/Uniformization/NOTICE.md)
与 [UPSTREAM](LowDimensionalTopology/External/Uniformization/UPSTREAM.json)。

## Quasiconformal analysis

拟共形分析与可测黎曼映射定理复用 Wu Xiaobin 的
[Li-Zhong-QC-formalization](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/tree/1c0d5473c020b66ed5106331a38a61536760b9b2)，
固定提交 `1c0d5473c020b66ed5106331a38a61536760b9b2`，Apache-2.0。
基础选取该定理实际依赖的 84 个模块，另选取 Teichmüller 与 Hurwitz 依赖的 67 个模块，
其中含 11 个 Jacobians、8 个 LiZhongExternal 与 2 个 DouadyEarle 模块；保留原数学命名空间，
不移入上游 `References` 目录。扩展的逐文件来源和验证状态见
[扩展来源记录](LowDimensionalTopology/External/LiZhongQC/PROVENANCE_EXTENSION.md)。
感谢 harfe、Kai Lam 及 Douady–Earle 源码贡献者；次级固定提交与完整许可证随目录保留。
同一固定来源另选取 Bers 复流形与全纯族所需的 6 个模块，精确来源及待验证状态见
[Bers 来源记录](LowDimensionalTopology/External/LiZhongQC/BERS_UPSTREAM.json)。
其中 Jordan 曲线代码的次级来源为
[epfl-lara/jordan-curve-theorem](https://github.com/epfl-lara/jordan-curve-theorem/tree/e442525a662e9e3beb8205b9fa1fc99509076ded/HOLLight-Lean)，
固定提交 `e442525a662e9e3beb8205b9fa1fc99509076ded`，Apache-2.0；
感谢其对 T. C. Hales 的 HOL Light 证明的 Lean 形式化贡献者。
原始文件、本地文件、哈希、兼容修改和次级来源见
[UPSTREAM](LowDimensionalTopology/External/LiZhongQC/UPSTREAM.json) 与
[PROVENANCE](LowDimensionalTopology/External/LiZhongQC/PROVENANCE.md)，完整许可随目录保留。

下列本地适配也基于 Wu Xiaobin（Copyright 2026）的
[Li-Zhong-QC-formalization](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/tree/1c0d5473c020b66ed5106331a38a61536760b9b2)，
固定提交 `1c0d5473c020b66ed5106331a38a61536760b9b2`，Apache-2.0：

- [OffSupportCauchyKernels.lean](LowDimensionalTopology/Geometry/Quasiconformal/OffSupportCauchyKernels.lean)
  适配上游 [LiZhongQC/Ch11/S36_Hamilton.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch11/S36_Hamilton.lean)
  的核估计与支配微分证明，并复用
  [LiZhongQC/Ch02/S13_Representation.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch02/S13_Representation.lean)
  的归一化第一变分核。将半平面几何改为实际距离分离条件，推广到任意可测支撑域的开外部；
  推导核的绝对可积性，并通过归一化核的抵消证明同一第一变分的三阶空间导数公式。
- [SchwarzianIdentityVariation.lean](LowDimensionalTopology/Geometry/Quasiconformal/SchwarzianIdentityVariation.lean)
  适配同一 `S36_Hamilton.lean` 的三阶导数与恒等映射处 Schwarzian 变分证明，并复用
  [LiZhongQC/Ch05/S21_UniversalTeichmuller.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch05/S21_UniversalTeichmuller.lean)
  的参数 Taylor、Cauchy 估计及导数全纯性结果。空间域推广为任意实际固定开域，
  从真实全纯族、局部一致界及第一变分导出导数交换与 Schwarzian 参数导数。

- [PoincareKernelSeries.lean](LowDimensionalTopology/Geometry/Teichmuller/PoincareKernelSeries.lean)
  适配同一 `S36_Hamilton.lean` 的 Poincaré 级数局部可求和界、核积分与展开证明。
  求和保留原矩阵群的完整 Möbius 像，并证明 ±I 的真实重复计数；
  原紧黎曼面的每个二次微分使用未缩放的基本域核种子，得到绝对与紧集一致收敛。

- [SourceFundamentalIntegrability.lean](LowDimensionalTopology/Geometry/Teichmuller/SourceFundamentalIntegrability.lean)
  适配同一 `S36_Hamilton.lean` 的紧轨道集展开与 Möbius 高度估计。
  对同一原紧黎曼面的任意给定基本域，证明原可测加权有界系数的非加权可积性；
  不要求系数全纯或自守，保留原矩阵群及 ±I 的真实计数。

- [MeasurablePoincareSeed.lean](LowDimensionalTopology/Geometry/Teichmuller/MeasurablePoincareSeed.lean)、
  [RawAutomorphicKernelInvariant.lean](LowDimensionalTopology/Geometry/Teichmuller/RawAutomorphicKernelInvariant.lean) 与
  [RawSeedBergmanSeries.lean](LowDimensionalTopology/Geometry/Teichmuller/RawSeedBergmanSeries.lean)
  适配同一 `S36_Hamilton.lean` 的支配微分、核面积、核变换与展开证明。
  将原连续全纯系数的分析步骤推广到真实可测可积输入；原函数及给定基本域不变，
  全矩阵群展开保留真实 ±I 重数，再对实际投影群级数严格消去该重数。

- [AhlforsWeillRealAnalytic.lean](LowDimensionalTopology/Geometry/Teichmuller/AhlforsWeillRealAnalytic.lean)
  适配上游 `LiZhongQC/Ch10/S33_BersEmbedding.lean` 的 `l333_core` 有界组装，
  并复用 `LiZhongQC/Ch05/S20_SchwarzDomains.lean` 的配对比值接口。
  本地保留真实规范化配对公式，新证实标量限制与有理组合下的实解析性，
  经既有原生自守参数接口给出同一非对称规范化解及准确 Bers 逆类；
  不复制原长 ODE、规范化或亚纯延拓证明。

- [DERealAnalyticRepresentatives.lean](LowDimensionalTopology/Geometry/Teichmuller/DERealAnalyticRepresentatives.lean)
  适配上游 `LiZhongQC/Ch06/S24_QuasiFuchsian.lean` 的 `s24q_genus_ge_two` 代表／同伦组装，
  复用同一固定归档所分发的 `LiZhongQC/Lemmas/DEDescent.lean` 与 `DouadyEarle/Extension.lean`。
  本地显式证明实际 Cayley 共轭的实解析性，通过既有全纯覆盖分支在全部原图册中下降，
  保留同一原目标及真实标记商类；解析前向下降证明为新作，未复制 Douady–Earle 的证明，
  也未补造该归档未记录的独立仓库、提交或作者。

- [CanonicalFrickeComparisonLift.lean](LowDimensionalTopology/Geometry/Teichmuller/CanonicalFrickeComparisonLift.lean)、
  [CanonicalFrickeMatrixConvergence.lean](LowDimensionalTopology/Geometry/Teichmuller/CanonicalFrickeMatrixConvergence.lean) 与
  [CanonicalFrickeBoundaryNormalization.lean](LowDimensionalTopology/Geometry/Teichmuller/CanonicalFrickeBoundaryNormalization.lean)、
  [NativeFrickeCoordinateContinuityProof.lean](LowDimensionalTopology/Geometry/Teichmuller/NativeFrickeCoordinateContinuityProof.lean)
  复用上游 `LiZhongQC/Ch06/S23_QCOnSurfaces.lean` 的实际 QC 提升与标记同伦判据，
  以及 `LiZhongQC/Ch07/S27_TeichmullerExistence.lean` 的共轭矩阵收敛证明。
  本地适配保留给定多边形端点标记，推导共同甲板修正及全部原矩阵交织关系，
  再由原正 c 规范消去代表元正负号，得到原有序坐标的收敛；边界适配复用
  `LiZhongQC/Ch02/S13_Representation.lean` 的边界对应，以原动态标记的轨道极限
  推导比较提升在 0、1、∞ 的规范化，保留同一个 K 及全部原矩阵交织关系。
  最终连续性证明还复用同一 S27 的实际一致化运输及 `normalizedLift_unique`，
  将原标记比较提升识别为已有规范解，再由原矩阵收敛取得同一 QC 度量商上的连续性。

- [AngularTwistCauchyPolar.lean](LowDimensionalTopology/Geometry/Teichmuller/AngularTwistCauchyPolar.lean)
  适配 Wu Xiaobin 的
  [LiZhongQC/Lemmas/GreenPolar.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Lemmas/GreenPolar.lean)，
  固定提交 `1c0d5473c020b66ed5106331a38a61536760b9b2`，Apache-2.0。
  本地改动将有限圆盘上的极坐标范数可积性运输用于全平面角锥系数的实际积分，
  从原三极点核的全局绝对可积性取得半无限半径与角区间乘积上的
  Jacobian 加权联合绝对可积性，随后应用 Fubini；保留原半径 Jacobian、
  角区间与评价点因子，不扩建一般极坐标或奇异核理论。

- [InjectiveHolomorphicJacobian.lean](LowDimensionalTopology/Geometry/SeveralComplexVariables/InjectiveHolomorphicJacobian.lean)
  的一维步骤复用同一固定归档 `LiZhongQC/Lemmas/Conformal.lean` 的
  `deriv_ne_zero_of_injOn`。高维归纳使用本项目已有的原坐标与解析纤维证明，
  保留独立的解析零集圆盘前提；没有复制外部 Weierstrass preparation 证明。

- [NativeLiftedHorizontalArcNoClosure.lean](LowDimensionalTopology/Geometry/Teichmuller/NativeLiftedHorizontalArcNoClosure.lean) 与
  [QuadraticSubintervalLiftLength.lean](LowDimensionalTopology/Geometry/Teichmuller/QuadraticSubintervalLiftLength.lean)
  分别适配上游 [LiZhongQC/Ch11/S35_DiscTeichmullerMaps.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch11/S35_DiscTeichmullerMaps.lean)
  的 `a35_rayLength_pos` 正积分论证与
  [LiZhongQC/Lemmas/UniformizedUniqueness.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Lemmas/UniformizedUniqueness.lean)
  的 `utm_length_lift` 分区积分论证。第一项用于原二次微分的实际上半平面提升及
  任意非退化有限参数区间，两端允许为零点，不增加有限长度或圆盘可积性前提。
  第二项将真实分区的端点从0、1推广为给定子区间，利用有限原生长度取得可容许分区，
  再由定义下确界的两向不等式识别提升积分；不增加 C1 或微分非零前提。

- [QuadraticProjectionDistance.lean](LowDimensionalTopology/Geometry/Teichmuller/QuadraticProjectionDistance.lean)
  适配 Wu Xiaobin 同一固定提交 `1c0d5473c020b66ed5106331a38a61536760b9b2`（Apache-2.0）的
  [LiZhongQC/Lemmas/UniformizedUniqueness.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Lemmas/UniformizedUniqueness.lean)
  中 `utm_length_lift` 的有限分区 Lipschitz 拼接步骤，用于同一原生上半平面路径。
  本地再以现有全纯投影与有限开覆盖细分构造实际投影分区，由原密度积分和路径下确界证明距离不增；不增加微分非零或有限长度前提。
- [ActualQuadraticGeodesicLift.lean](LowDimensionalTopology/Geometry/Teichmuller/ActualQuadraticGeodesicLift.lean)
  适配 Wu Xiaobin 同一固定提交 `1c0d5473c020b66ed5106331a38a61536760b9b2`（Apache-2.0）的
  [LiZhongQC/Lemmas/UniformizedUniqueness.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Lemmas/UniformizedUniqueness.lean)
  中 `utm_length_lift` 的有限分区提升 Lipschitz 论证，将端点从0、1改为实际子区间。
  本地由源测地性与已有局部有限距离自动导出该区间有限性，再接合原提升积分、投影距离界及实际仿射子路径，未增加公开有限长度或正则性前提。
- [NativeMaximalHorizontalTrajectory.lean](LowDimensionalTopology/Geometry/Teichmuller/NativeMaximalHorizontalTrajectory.lean)
  适配同一固定提交的 [LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean)
  中 `s26v_mem_critArc` 的实际自然坐标流盒、有限可继续区间重叠唯一性与曲线拼接构造；
  保留原紧黎曼面及同一二次微分，将区间并显式保存为含0的最大开区间，并复用有限端趋于原微分零点的定理。

- [NativeFiniteQuadraticMinimum.lean](LowDimensionalTopology/Geometry/Teichmuller/NativeFiniteQuadraticMinimum.lean)
  适配同一固定提交的 [LiZhongQC/Ch07/S25_QuadraticDifferentials.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch07/S25_QuadraticDifferentials.lean)
  中 `shortest_isPhiGeodesicRS` 的局部最短连接、图册内拼接及有限长度消去证明；
  保留实际原生上半平面的同一提升微分、原曲线与全部道路竞争者，抽去局部证明中未使用的紧致前提。

- [NativeRootHorizontalFlowAction.lean](LowDimensionalTopology/Geometry/Teichmuller/NativeRootHorizontalFlowAction.lean)
  适配同一固定提交的 [LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean)
  中 `s26v_trajAt_chart` 的实际坐标转移、邻域恒等式及链式求导，将全局 (1,0) 根与原轨线切向量的乘积运输到固定图；
  其余部分通过既有流盒、根比值常数与轨线唯一性接口，证明同一具体时间映射的全时定向及零元、加法规律。

- [NativeRootHorizontalFlowContinuity.lean](LowDimensionalTopology/Geometry/Teichmuller/NativeRootHorizontalFlowContinuity.lean)
  适配同一固定提交的 [LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean)
  中 `s26v_a_natAt_chart` 的实际坐标转移、邻域恒等式及链式求导，以及 `s26v_flowBox_line` 的局部逆函数计算；
  用于固定自然管上的全局 (1,0) 根收缩和同一具体时间映射的联合连续性，其余部分通过现成自然管及轨线唯一性接口组合。

- [NativeRootHorizontalFlowArea.lean](LowDimensionalTopology/Geometry/Teichmuller/NativeRootHorizontalFlowArea.lean)
  适配同一固定提交的 [LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean)
  中 `s26v_a_pair_core` 的自然坐标分片积分计算，以及 `s26v_pair_average` 的临界集零测拉回、a.e. 指标替换步骤；
  用实际根定向双射与固定管符号证明单次覆盖，再组合现成积分接口与 Borel 子空间迹，得到同一时间映射的单向面积不变性。

- [HorizontalZeroJoinProngSeparation.lean](LowDimensionalTopology/Geometry/Teichmuller/HorizontalZeroJoinProngSeparation.lean)
  适配 Wu Xiaobin（Copyright 2026）同一固定提交
  [LiZhongQC/Ch07/S25_QuadraticDifferentials.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch07/S25_QuadraticDifferentials.lean)
  中 `zero_critical_trajectories` 的正实系数分解及单位相位判别，并复用其公共相位接口；
  从标准线性射线改用于同一实际曲线的非恒定径向参数，随后组合现成连续单射单调性、
  单位根及余弦接口得到两条实际水平射线的分离。上游许可证 Apache-2.0 已完整保留。

感谢 Wu Xiaobin；完整许可继续保留于
[LiZhongQC/LICENSE](LowDimensionalTopology/External/LiZhongQC/LICENSE)。

## Riemann–Roch

紧黎曼曲面的 Riemann–Roch 分析基础复用 Rado Kirov 的
[jacobian-claude](https://github.com/rkirov/jacobian-claude/tree/73212f7ef2bb46a7884710b18fe1e18b8509e3e5)，
固定提交 `73212f7ef2bb46a7884710b18fe1e18b8509e3e5`，Apache-2.0。
基础移入源为上述固定 QC 仓库中的 183 模块集成版本，原始 Git、集成版本与本地哈希分别记录。
Teichmüller 扩展另含 11 个模块，其归属和独立来源核验范围见
[扩展记录](LowDimensionalTopology/External/Jacobians/PROVENANCE_EXTENSION.md)。
历史 Stokes 来源保留 Michal J Wallace 的 MIT 许可与固定参考版本。
感谢 Rado Kirov、Wu Xiaobin、Michal J Wallace；完整来源及局部图册适配见
[PROVENANCE](LowDimensionalTopology/External/Jacobians/PROVENANCE.md) 与
[UPSTREAM](LowDimensionalTopology/External/Jacobians/UPSTREAM.json)，完整许可随目录保留。

后续移入代码继续记录准确上游 URL、提交、文件、许可和本地改动，并保留原版权及作者信息。
本项目许可证不替代各第三方组件的权利与许可。

- [HorizontalZeroJoinModelCost.lean](LowDimensionalTopology/Geometry/Teichmuller/HorizontalZeroJoinModelCost.lean)
  适配 Wu Xiaobin（Copyright 2026）同一固定提交
  [LiZhongQC/Ch07/S25_QuadraticDifferentials.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch07/S25_QuadraticDifferentials.lean)
  中 `s25g_segLen_add` 的相邻区间积分分解，以及 `s25e_cone_case_apex` 的具体锥势与端点值计算；
  对同一实际 Lipschitz 参数保留两个径向积分，再用实际水平射线的扇形界及现成锥势下界、折径竞争曲线，
  证明其加权长度等于该模型距离。上游 Apache-2.0 许可证已完整保留。

- [NativeHorizontalSideSegment.lean](LowDimensionalTopology/Geometry/Teichmuller/NativeHorizontalSideSegment.lean)
  适配 Wu Xiaobin（Copyright 2026）同一固定提交
  [LiZhongQC/Ch07/S25_QuadraticDifferentials.lean](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/blob/1c0d5473c020b66ed5106331a38a61536760b9b2/LiZhongQC/Ch07/S25_QuadraticDifferentials.lean)
  中 `s25g_straight_seg` 的虚部均值定理论证；保留同一实际参数，配合连续单射的实部单调性证明局部线段像等式。
  自然坐标与逆映射直接复用现成公共接口，未重证其存在性。上游 Apache-2.0 许可证已完整保留。
