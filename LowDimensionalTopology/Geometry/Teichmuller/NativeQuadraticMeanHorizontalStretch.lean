/- Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import LowDimensionalTopology.Unproved.Teichmuller.QuadraticFlatProofGaps
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness

/-!
# The mean horizontal-stretch inequality on the original surface

The existing fully proved mean-stretch theorem has exactly the required
original-atlas integral contract. Only the already proved native genus
conversion is used here.

The reused analytic theorem is due to Wu Xiaobin's Apache-2.0
Li-Zhong-QC-formalization, pinned in the source manifest at
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see
`THIRD_PARTY_NOTICES.md`. No flow, branched-cover or separatrix proof
is reconstructed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u

/-- The existing original-atlas theorem proves the entire source-scoped
mean-stretch obligation, with the single quadratic area integral. -/
theorem quadraticMeanHorizontalStretch :
    LowDimensionalTopology.Unproved.Teichmuller.QuadraticMeanHorizontalStretch.{u} := by
  intro X inst R g hg hgenus q hq
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro h hqc hhom
  have hqne : (q : X → ℂ → ℂ) ≠ 0 := by
    intro hzero
    exact hq (Subtype.ext hzero)
  change LiZhongQC.quadDiffNorm (q : X → ℂ → ℂ) ≤ _
  exact LiZhongQC.lemma26_2 (by omega) (R.hasSourceGenus hgenus)
    h hqc hhom q.property hqne

end LowDimensionalTopology.Geometry.Teichmuller
