# Quasiconformal and measurable Beltrami sources

The base selection documented in `UPSTREAM.json` is the 84-module recursive local import closure of
`LiZhongQC.Ch02.S13_Representation` from
[xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/tree/1c0d5473c020b66ed5106331a38a61536760b9b2),
fixed commit `1c0d5473c020b66ed5106331a38a61536760b9b2`.
The primary source is copyright 2026 Wu Xiaobin and Apache-2.0 licensed.
Its complete license is preserved in [LICENSE](LICENSE).

The selected sources comprise 53 LiZhongQC modules and 31 JordanCurveTheorem modules.
The latter preserve the Apache-2.0 source of the epfl-lara Lean reformalization of
T. C. Hales’s HOL Light Jordan curve proof; their exact secondary repository,
commit and existing integration changes are retained in
[JordanCurveTheorem/PROVENANCE.md](JordanCurveTheorem/PROVENANCE.md) and its
[LICENSE](JordanCurveTheorem/LICENSE).
Thank you to Wu Xiaobin, the Jordan curve theorem contributors, and the Mathlib contributors.

No References, Jacobians, RiemannDynamics, LiZhongExternal or DouadyEarle modules
are imported by this selected closure. In particular, the separate References
library with unfinished theorem statements is excluded.

## Local adaptation

The integration changes are local module paths, `module`, explicit `public import`,
`@[expose] public section`, the original elaboration options, the whitespace
normalization recorded below, and compatibility repairs for the project's fixed
Mathlib and Lean versions. Original declaration namespaces are preserved. Mathematical
statements retain their hypotheses and conclusions, allowing local binder renaming
and the recorded public definitional aliases and equivalent uniform-measure interface
change described below. Proof scripts use current
public Mathlib API names and remove redundant tactics and unused simp arguments.
These compatibility changes alter proof tokens and are recorded per file.
Original per-library
options are set explicitly in each file: LiZhongQC uses `autoImplicit = false`
and `relaxedAutoImplicit = false`; JordanCurveTheorem uses `autoImplicit = true`,
`relaxedAutoImplicit = false`, and `maxSynthPendingDepth = 3`.
Source-local options are retained. `SectionY_GridCells` additionally uses a finite
800000-heartbeat file limit, consistent with its existing 800000-heartbeat proofs.
Its coordinate helpers `e1` and `e2` are public because public theorem signatures
refer to them. The Koebe derivative proofs specify the intermediate square function
explicitly in applications of the public derivative composition API.
The removed finite-type uniform `PMF.toMeasure` interface in `S10_AnalyticDefinition`
is expressed through the current `Measure.uniformOfFinset` on all Boolean values.
The fair-coin measure's probability property is proved explicitly, and its singleton
mass follows from the current public API. The independent coin product and its
Cantor push-forward therefore keep the same mathematical definitions.
The `Lᵖ` indicator arguments explicitly derive null measurability from their existing
measurable-set proofs, as required by the current public Mathlib interface.
The `QuasiMeasurePreserving` type is referred to by its current public
`MeasureTheory` namespace, replacing its definitionally identical deprecated alias
under `MeasureTheory.Measure`.

[UPSTREAM.json](UPSTREAM.json) records every original/local file, SHA256,
module correspondence, wrapper options and the checksum of upstream source outside
import commands. Nonliteral CRLF endings, trailing whitespace and redundant EOF
blank lines were normalized where needed for the repository whitespace checks.
Every string and character literal was retained exactly; non-whitespace code was
checked unchanged by this normalization. Each file records its exact formatting
changes and any subsequent compatibility adaptations. Original source checksums
remain available alongside the adapted local checksums.
No project dependency pin or external package source was changed. The original
source targeted Lean 4.35.0-rc2 and Mathlib commit
`2f3d8f63005779e9d708eb9adf3feca54aa24ceb`; this project keeps its own pinned versions.

Source inspection found no custom compiler-internal API, custom metaprogramming
commands, code holes or new axioms in the selected closure. That source check is
not a current-toolchain compilation or transitive axiom certificate. The original
Jordan provenance includes its own historical verification results; those are
not claimed as new checks performed by this import.

Additional Teichmüller development modules are recorded separately in [PROVENANCE_EXTENSION.md](PROVENANCE_EXTENSION.md) and the QC extension manifest. Their integration is in progress; the base selection and its fixed-source checksums remain unchanged.
