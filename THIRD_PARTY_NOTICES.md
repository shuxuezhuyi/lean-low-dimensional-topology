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
上游源码作为外部工具安装，不在本项目重新署名。

## Tau Ceti

曲面的 Euler 特征及其同胚不变性复用
[TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti/tree/1f9b4414105d86e487a4ac4c3d3397076a44d0d2)，
固定提交 `1f9b4414105d86e487a4ac4c3d3397076a44d0d2`，Apache-2.0。
移入的 95 个模块保留原作者与版权头，调整本地 import 前缀，并将九个证明依赖的 import 改为 public import。
准确原始文件、本地文件、哈希和修改见[来源清单](LowDimensionalTopology/External/TauCeti/source-manifest.json)，
完整许可见 [LICENSE](LowDimensionalTopology/External/TauCeti/LICENSE)。感谢 The Tau Ceti contributors。
实际 handle 曲面的胞腔分解及亏格唯一性连接证明由本项目编写。

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

后续移入代码继续记录准确上游 URL、提交、文件、许可和本地改动，并保留原版权及作者信息。
本项目许可证不替代各第三方组件的权利与许可。
