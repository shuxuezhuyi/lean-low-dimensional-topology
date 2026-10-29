# Lean 4 低维拓扑与几何

以 **Mathlib4 为必需基础库**，维护离散群、双曲几何及低维拓扑的 Lean 4 形式化。
数学实现采用 Mathlib4 的公开接口，由 Mathlib4 衔接 Lean 底层。
库中的对象包括 Möbius 变换、双曲模型与测地线、Fuchsian 群、基本域和多边形、商曲面及面积。
代码和公共接口按数学对象及依赖关系组织；`LowDimensionalTopology.lean` 是公共总入口。
常用的主题导入入口见[几何接口导航](LowDimensionalTopology/Geometry/README.md)。

| 目录 | 内容 |
| --- | --- |
| [Auxiliary](LowDimensionalTopology/Geometry/Auxiliary) | 分析、拓扑、测度等可复用工具 |
| [Euclidean](LowDimensionalTopology/Geometry/Euclidean) | 欧氏空间与角度 |
| [Inversive](LowDimensionalTopology/Geometry/Inversive) | 反演、广义球面与保形性质 |
| [Mobius](LowDimensionalTopology/Geometry/Mobius) | Möbius 变换、交比与边界作用 |
| [Hyperbolic](LowDimensionalTopology/Geometry/Hyperbolic) | 双曲模型、测地线、距离与面积 |
| [DiscreteGroups](LowDimensionalTopology/Geometry/DiscreteGroups) | 离散作用、轨道与基本域 |
| [Fuchsian](LowDimensionalTopology/Geometry/Fuchsian) | Fuchsian 群、商空间与群的几何 |
| [Polygon](LowDimensionalTopology/Geometry/Polygon) | 多边形、边配对与拼合 |
| [Surfaces](LowDimensionalTopology/Geometry/Surfaces) | 曲面、覆盖、闭 Riemann 曲面与一致化 |
| [Teichmuller](LowDimensionalTopology/Geometry/Teichmuller) | 标记商、Teichmüller 空间、Fenchel–Nielsen 坐标与 Weil–Petersson 几何 |

项目约定见 [AGENTS.md](AGENTS.md)。开发中使用了
[Archon](https://github.com/frenzymath/Archon) 的 Lean 指引和诊断工具。
新写及移入的 Lean 文件统一采用 `module`、显式 `public import` 和 `public section`。
移入外部代码保留原作者、版权、许可及准确上游，见[第三方致谢](THIRD_PARTY_NOTICES.md)。

## 主要参考文献

<!-- reference-acknowledgment:start -->
Alan F. Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
Springer, 1983. DOI: 10.1007/978-1-4612-1146-4.

Y. Imayoshi and M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer, 1992.
<!-- reference-acknowledgment:end -->

## 许可证

[Apache License 2.0](LICENSE)。第三方组件按各自保留的许可证和来源说明使用。
