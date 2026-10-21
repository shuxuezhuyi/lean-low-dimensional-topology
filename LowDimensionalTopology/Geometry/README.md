# 几何接口导航

本目录按数学对象和依赖组织。公共总入口为 `LowDimensionalTopology`；
几何部分的入口为 [`LowDimensionalTopology.Geometry`](../Geometry.lean)。
局部开发可直接导入所需的主题模块。

| 目录 | 内容 |
| --- | --- |
| `Auxiliary` | 独立的代数、分析、拓扑与测度工具 |
| `Euclidean` | 欧氏内积、凸性、角度与反射 |
| `Inversive` | 反演、广义球面及保球变换 |
| `Mobius` | Möbius 变换、交比、分类与边界作用 |
| `Hyperbolic` | 双曲模型、模型间映射、度量、测地线与凸性 |
| `DiscreteGroups` | 群作用、轨道、离散性与基本域 |
| `Polygon` | 多边形、边配对、局部几何与拓扑 |
| `Surfaces` | 曲面拓扑、黎曼曲面、覆盖与一致化 |
| `Fuchsian` | Fuchsian 群、商空间、曲面端与面积 |

双曲模型各自保留相应的载体、度量及作用；模型间的坐标运输放在
`Hyperbolic/ModelMaps`。使用接口时应核对声明中的具体载体、正性条件、
群作用和拓扑假设。连接不同对象的模块保留在实际使用该连接的数学层。

可复用的低层结果通过独立模块导出，具体几何构造导入这些模块。
类型相关的方法随其类型所在命名空间组织；文件位置表示依赖层次，
同一类型的方法可以由多个主题模块共同扩充。

常用的主题入口如下。表中的链接指向相应文件；在 Lean 中以
`LowDimensionalTopology.Geometry` 为前缀，用点分隔模块路径，例如
`LowDimensionalTopology.Geometry.Auxiliary.Topology.Covering.PathLifting`。

| 所需接口 | 入口 |
| --- | --- |
| 一般覆盖映射与平面拓扑 | [PathLifting](Auxiliary/Topology/Covering/PathLifting.lean)、[PlaneAccessibility](Auxiliary/Topology/PlaneAccessibility.lean) |
| 相容局部测度 | [CompatibleMeasure](Auxiliary/Measure/CompatibleMeasure.lean) |
| 欧氏内积与有限凸包 | [ComplexAffine](Euclidean/InnerProduct/ComplexAffine.lean)、[FiniteHull](Euclidean/Convexity/FiniteHull.lean) |
| 保球反演群与广义圆盘 | [Subgroup](Inversive/UnitBall/Subgroup.lean)、[GeometricDisc](Mobius/Circle/GeometricDisc.lean) |
| 双曲模型与坐标 | [Hyperboloid.Basic](Hyperbolic/Models/Hyperboloid/Basic.lean)、[RadialCoordinates](Hyperbolic/Models/Klein/RadialCoordinates.lean)、[PoincareKlein.Ambient](Hyperbolic/ModelMaps/PoincareKlein/Ambient.lean) |
| 群作用与基本域 | [FiniteOrbit](DiscreteGroups/Action/FiniteOrbit.lean)、[CosetRegion](DiscreteGroups/Action/CosetRegion.lean)、[FundamentalDomainMeasure](DiscreteGroups/Action/FundamentalDomainMeasure.lean) |
| 黎曼曲面的覆盖结构 | [Covering](Surfaces/Riemann/Covering.lean) |
| 商曲面与几何签名 | [BoundaryPresentation](Fuchsian/Nielsen/BoundaryPresentation.lean)、[BoundaryCensusArea](Fuchsian/Nielsen/BoundaryCensusArea.lean)、[CappedSurface](Fuchsian/Nielsen/CappedSurface.lean)、[QuotientSurface](Fuchsian/Nielsen/QuotientSurface.lean)、[QuotientSignature](Fuchsian/Nielsen/QuotientSignature.lean) |

开发、严格构建、公理检查及依赖版本维护见根目录的
[README](../../README.md) 与 [项目约定](../../AGENTS.md)。
