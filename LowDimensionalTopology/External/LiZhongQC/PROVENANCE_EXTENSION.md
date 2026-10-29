# Teichmüller and Hurwitz source extension

This extension adds 67 modules from the main proved source in
[Li-Zhong-QC-formalization](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/tree/1c0d5473c020b66ed5106331a38a61536760b9b2), fixed commit `1c0d5473c020b66ed5106331a38a61536760b9b2`.
The original 84-module selection remains recorded in its own `UPSTREAM.json`,
including subsequent current-toolchain adaptations. The extension is recorded
separately in `EXTENSION_UPSTREAM.json`.
Its primary source is copyright 2026 Wu Xiaobin and is distributed under the
repository's complete root Apache-2.0 license, already preserved here as `LICENSE`.

The added selection contains 46 LiZhongQC modules, 11 Jacobians modules,
eight LiZhongExternal modules and two DouadyEarle modules. The Jacobians files
are placed in the existing sibling `External/Jacobians` library. This is the
minimum file-import closure of the actual `UniformizedTeichmuller` and
`HurwitzTheorem` endpoints, stopping at the existing fixed public dependencies.
References, RMT4 and a second RiemannDynamics/Uniformization copy are excluded.

## Actual mathematical scope

The source uses actual compact complex manifolds, variable target Riemann
surfaces, quasiconformal marking homeomorphisms, biholomorphisms and Mathlib
free homotopy. Its distance is the infimum of `1/2 * log K` over genuine
compatible quasiconformal maps. The selected companion modules prove
attainment, separation, completeness and discontinuity using these objects.
The Hurwitz endpoint proves both finiteness and the bound `84 * (g - 1)`
for the actual conformal automorphisms, with a constructed finite analytic
quotient and Riemann–Hurwitz argument.

These imports alone do not identify the source's quasiconformal marking
quotient with the native smooth marking quotient, or its fundamental-group
genus with native handle genus. Those are separate mathematical bridges.
No Mumford compactness or normal complex analytic moduli structure is asserted
by this source selection.

## Preserved sources and licenses

The 11 added Jacobians sources are the exact integration files in the same
fixed QC archive. Their vendor manifest records the upstream
`rkirov/jacobian-claude` commit
`73212f7ef2bb46a7884710b18fe1e18b8509e3e5`. Archive bytes, historical
vendor-reported upstream hashes and local adapted bytes are recorded separately.
The existing Jacobians Apache-2.0 license, authorship and secondary MIT notices
remain in force. All eleven primary-upstream Git raw hashes and blob identifiers were subsequently
independently checked at that fixed commit and are recorded separately from
archive bytes and historical vendor-reported hashes.

The eight LiZhongExternal files preserve their source's
[original provenance](LiZhongExternal/UPSTREAM_PROVENANCE.md):
harfe's MIT-licensed fixed-point proof at
`770940ddf9878cf61952ed53d910b92bca841838`, and Kai Lam's selected
Apache-2.0-licensed PR36770 source at
`230d75acb32d80e7d7c4f4cd028b139f3dc28be7`.
Their complete license texts are retained at `LiZhongExternal/Harfe/LICENSE.harfe`
and `LiZhongExternal/Topology/LICENSE.mathlib`. The source's old compilation
and axiom reports are historical claims, not new verification of this extension.

DouadyEarle is included **as distributed by the fixed QC archive under its root
Apache-2.0 license; an independent original repository and pin are not recorded**.
The archive records a Windows sister-project source and two historical file
hashes, preserved verbatim in
[UPSTREAM_PROVENANCE.md](DouadyEarle/UPSTREAM_PROVENANCE.md).
Its complete archive license is supplied as `DouadyEarle/LICENSE`.
No independently verified sister-project license or revision is claimed.

Thank you to Wu Xiaobin, Rado Kirov, the Douady–Earle source contributors,
harfe, Kai Lam and the Mathlib contributors.

## Local adaptation and validation status

All new modules receive `module`, explicit `public import`,
`@[expose] public section` and the original per-library elaboration options.
Original local options, copyright headers, mathematical namespaces and literal
contents are retained. Initial wrapper-only preparation preserved all proof tokens;
subsequent current-toolchain compatibility repairs are recorded per file and do
not retain that stronger token-identity claim. Nonliteral
CRLF endings and trailing whitespace are normalized and counted per file.

Original RiemannDynamics imports map to the already integrated public
`External/Uniformization` modules. Their actual path-cover interfaces and
trichotomy are preserved. The existing canonical sphere atlas remains in use;
the archived independent sphere atlas is not duplicated.
The added Jacobians files that depend on `ProjectiveLine` explicitly open the
original `Jacobians.RiemannSphere` scope, retaining that separate source atlas.

These modules are installed in the repository. Current-toolchain compatibility
adaptation is in progress; no Lean/LSP/build or compiled axiom audit has yet run
for the 67 extension modules. The 32 modified QC/secondary additions and eight modified Jacobians additions
are recorded with their initial and current hashes; the two DouadyEarle files
retain their original prepared bytes. Dependency locks and package sources are
unchanged; base selections keep their separate adaptation records.

## Douady–Earle mathematical source notes

The preserved `Basic.lean` preface and `IsProbabilityDensity` docstring overstate
the regularity of arbitrary circle-homeomorphism pushforwards of harmonic
measure. The actual extension proof explicitly corrects this in
`Extension.lean` at original lines 123–137: it integrates the general transformed
boundary family against the original Poisson kernel in the original angular
parameter. Only the Poisson kernel supplies a continuous density. No density,
absolute continuity or differentiability of the boundary homeomorphism or its
inverse is an additional premise of the final extension theorems.

The actual domain is Mathlib's `Circle`; the inputs are a continuous bijection
`phi : Circle → Circle`. `extension_analyticOn_disk` proves real analyticity
on the open disk. `extension_isHomeomorphOn` proves an actual homeomorphism
of the closed disk. `extension_jacobian_pos` additionally uses
`HasIncreasingLift phi`: a strictly increasing real lift with period increment
`2*pi`, the genuine degree `+1` orientation condition. No positive boundary
derivative is assumed. The sign-free theorem for both orientations proves
nonzero Jacobian only.

The total extension is not claimed smooth outside or through the disk boundary.
A uniform QC bound for every circle homeomorphism would also be false; the
source obtains that bound through actual compact surface quotient and
equivariance arguments. These restrictions and the source's original comments
are retained. The native smooth forward/inverse descent remains a separate
interface theorem; this import does not mark it completed.
