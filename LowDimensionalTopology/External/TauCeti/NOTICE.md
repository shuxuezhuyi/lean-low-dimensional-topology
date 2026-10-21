# Tau Ceti Euler characteristic prerequisites

These 95 modules are copied from [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti)
at commit `1f9b4414105d86e487a4ac4c3d3397076a44d0d2`, under Apache-2.0.
Original copyright and author notices are retained in every source; see [LICENSE](LICENSE).

They provide the genuine homotopy invariance of the Euler characteristic of finite CW spaces.
The project uses it with an independently constructed CW decomposition of its actual handle surface
to prove uniqueness of topological genus and the signature area formula.

Local changes replace `TauCeti.*` import paths with
`LowDimensionalTopology.External.TauCeti.*`; declaration namespaces and proof bodies are retained. Nine upstream proof-only imports are made public
under the project module convention, with their historical comments clarified.
Every local source uses `module`, `public import` and `public section`.
[The source manifest](source-manifest.json) records original and local hashes.
No project Lean or Mathlib dependency pins are changed.
