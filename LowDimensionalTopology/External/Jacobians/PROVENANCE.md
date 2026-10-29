# Riemann–Roch on compact Riemann surfaces

The base selection documented in `UPSTREAM.json` is the 183-module local import closure, including
the entry point `Jacobians.RiemannRoch`, selected from Rado Kirov's
[jacobian-claude](https://github.com/rkirov/jacobian-claude/tree/73212f7ef2bb46a7884710b18fe1e18b8509e3e5)
at commit `73212f7ef2bb46a7884710b18fe1e18b8509e3e5`.
The complete Apache-2.0 license is preserved in [LICENSE](LICENSE); its CRLF line
endings were normalized to LF without changing the license wording.

The immediate source snapshot is the Jacobians integration in Wu Xiaobin's
[Li-Zhong-QC-formalization](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/tree/1c0d5473c020b66ed5106331a38a61536760b9b2)
at commit `1c0d5473c020b66ed5106331a38a61536760b9b2`.
No files from its References, LiZhongQC, RiemannDynamics, JordanCurveTheorem,
LiZhongExternal or DouadyEarle libraries are part of this selection.
Thank you to Rado Kirov, Wu Xiaobin, Michal J Wallace and the Mathlib contributors.

## Mathematical scope

The entry point proves Riemann–Roch for every divisor on an actual compact
connected Hausdorff complex analytic one-dimensional manifold. Meromorphic
functions and their orders are defined through the genuine manifold charts.
Linear-system dimensions use a quotient by germ-zero representatives; analytic
genus is the dimension of actual holomorphic cotangent-bundle sections.
Finiteness and the Laurent-tail Serre-duality route are proved in the selected
dependencies. The entry point also proves the standard canonical-degree and
canonical-dimension consequences and a simple-pole existence consequence.

Analytic genus is not definitionally the project's topological handle genus.
Their comparison remains a separate mathematical obligation. Importing these
sources does not establish the topological-genus version of Riemann–Roch or
the dimension of quadratic differentials on the project's surfaces by itself.

## Local adaptation

The local changes are project-relative module paths, `module`, explicit
`public import`, `@[expose] public section`, restoration of the source library's
`autoImplicit = false` and `relaxedAutoImplicit = true`, and normalization of
nonliteral line endings and trailing whitespace. Mathematical declaration
namespaces and the original copyright and author headers are retained.

The source sphere has its own genuine two-chart atlas on `OnePoint ℂ`. Its
charted-space and analytic-manifold instances are scoped to
`Jacobians.RiemannSphere`, with explicit scope activation in their 16 transitive
consumers. This retains that atlas for these proofs while avoiding a second
global atlas beside the project's already integrated Riemann-sphere atlas.
The two atlases have not been identified or silently substituted.

Compatibility repairs use current public Mathlib names and smoothness
equivalences on open sets, expose the existing chart-cover choice
and affine-map helpers needed in public types or definitions, and simplify
linter-reported proof steps. The original mathematical statements are retained;
proof tokens and helper visibility change as recorded per file in the manifest.

[UPSTREAM.json](UPSTREAM.json) records original upstream, immediate integrated
snapshot and adapted local SHA256 values separately. It preserves every selected
record from the immediate snapshot's vendor manifest, omitting only the historical
Windows staging path. The original manifest's checksum is recorded as well.
Actual raw Git SHA256 and Git blob hashes were independently recomputed for all
183 upstream files. The snapshot manifest's reported upstream hashes describe
its historical CRLF staging bytes and are retained separately; they are not
misidentified as hashes of the upstream Git blobs. Of the immediate snapshot's
selected files, 142 agree with the raw upstream after CRLF normalization and 41
include its recorded integration changes.
[UPSTREAM_PROVENANCE.md](UPSTREAM_PROVENANCE.md) preserves the immediate snapshot's
historical provenance verbatim; its compilation and audit reports describe that
earlier integration, not new validation of this directory.

The source integration targeted Lean 4.35.0-rc2 and Mathlib commit
`2f3d8f63005779e9d708eb9adf3feca54aa24ceb`. This project retains its own fixed
toolchain and dependency versions. No external dependency files are modified.

## Historical secondary Stokes source

The preserved `PlanarCompactSupportStokes` header credits the MIT-licensed
`tangentstorm/JacobianChallenge`, now named
[tangentproofs/JacobianChallenge](https://github.com/tangentproofs/JacobianChallenge).
Its referenced file is `Jacobian/Blueprint/Sec03/StokesOnRSWithBoundary.lean`.
The fixed reference revision
[`dd6c82de5bb0f35666e33f7643508865575f2905`](https://github.com/tangentproofs/JacobianChallenge/tree/dd6c82de5bb0f35666e33f7643508865575f2905)
is that file's last change before Kirov's port; the original port did not record
its precise source revision. Copyright is 2026 Michal J Wallace, and the complete
license from that fixed revision is preserved in
[LICENSE.JacobianChallenge.MIT](LICENSE.JacobianChallenge.MIT).

The six credited rectangle declarations were introduced in jacobian-claude
commit `ed445dad1a98c07fddded8485e816c1d1a3214b6`, then removed in its four pruning
commits `a59e72788c16c7ef5b4af0cfb89ad1a1858e9981`,
`fc038fd7fa0ec7f5558a358ab894d330accc5239`,
`e90f50b21ccaaae1ec5219f2934f19e0bf526c4d` and
`e2ed71447e523a96b7d57b9bd22702e43075930e`.
Their historical attribution remains in the selected header, alongside the four
remaining compact-support integration-by-parts theorems. The complete MIT
material is retained to make that history explicit.

Additional Teichmüller development modules are recorded separately in [PROVENANCE_EXTENSION.md](PROVENANCE_EXTENSION.md) and the QC extension manifest. Their integration is in progress; the base selection and its fixed-source checksums remain unchanged.
