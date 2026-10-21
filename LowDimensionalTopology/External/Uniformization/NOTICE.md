# Uniformization proof dependencies

These Lean files are adapted from
[LR-UK/Bounded-orbit-wandering-domains](https://github.com/LR-UK/Bounded-orbit-wandering-domains)
at commit `6e306deb8169e834e9cc6662160c70231a7e2a83`, under Apache 2.0.
The RiemannDynamics sources retain their 2026 copyright and authorship notices
for **Will (Ziang) Li**. The complete license texts are retained in `LICENSE`,
`RIEMANN_DYNAMICS_LICENSE`, and `FUNCTION_THEORY_LICENSE`.

`FunctionTheory/RiemannSphere/Basic.lean` adapts the sphere atlas of
**Geoffrey Irving**, [girving/ray](https://github.com/girving/ray), commit
`753f7131cf96f4651294de4398368abf136c34de`,
`Ray/Manifold/RiemannSphere.lean`, under Apache 2.0 (`RAY_LICENSE`).
Its retained source notice records this secondary attribution.

`UPSTREAM.json` records the exact original and local SHA-256 of every included
Lean source, its original path, and the compatibility changes. All copied
files retain the original notices. The local module paths, public imports,
and public sections follow this project's module convention. These are
adaptations of the credited proofs.

The complete reduced33-module proof includes the sphere analytic manifold,
biholomorphic maps, potential theory, Green functions, path covering, Riemann
mapping, and the general uniformization trichotomy. The exact original
Riemann-surface and model adapters are maintained separately in
`Geometry.Surfaces.Uniformization`.
Every included proof was strictly compiled and audited before public copying.
No external Lake package or version pin is added.

The two `BoundedWanderingDomains` modules retain the copyright and author
notices of **Yury Kudryashov** (2026 Riemann mapping and 2025 unit-disc shifts),
Apache 2.0. They adapt Mathlib PR33505 from `urkud/mathlib4`, commit
`d43061d911b1aeae0788591da437a3b115098962`, through the credited upstream
repository. The Riemann-mapping proof has one local pinned-Mathlib simplification
change; its mathematical statement is unchanged. `GreenSymmetry/Transport`
uses that fully proved Riemann mapping theorem instead of the larger Tau Ceti
chain and omits two unused grid/primitives lemmas.
