module

public import LowDimensionalTopology.Geometry.Surfaces.SingularMeasuredFoliation
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S26_TeichmullerUniqueness

/-!
# Actual local flat charts of a positive-order plane monomial

The existing regular natural parameter and inverse-function construction give
a genuine partial chart away from zero, retaining its exact derivative law
on the whole restricted source.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

/-- Every nonzero point has an actual local flat chart of the positive-order monomial. -/
theorem exists_quadraticProngNaturalChart (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    ∃ a : OpenPartialHomeomorph ℂ ℂ, z ∈ a.source ∧ IsProngNaturalChart m 1 a := by
  have hpow : z ^ m ≠ 0 := (pow_ne_zero_iff (Nat.ne_of_gt hm)).mpr hz
  obtain ⟨f, hf, _, hfd, hid⟩ :=
    LiZhongQC.eq25_2_natural_parameter (analyticAt_id.pow m) hpow
  let i : ℂ ≃L[ℂ] ℂ := .unitsEquivAut ℂ (.mk0 _ hfd)
  have hF : HasStrictFDerivAt f i.toContinuousLinearMap z := hf.hasStrictDerivAt
  have hsrc : z ∈ (hF.toOpenPartialHomeomorph f).source :=
    hF.mem_toOpenPartialHomeomorph_source
  have hG : {u : ℂ | u ≠ 0 ∧ AnalyticAt ℂ f u ∧ deriv f u ^ 2 = u ^ m} ∈ 𝓝 z := by
    filter_upwards [eventually_ne_nhds hz, hf.eventually_analyticAt, hid] with u hu ha hd
    exact ⟨hu, ha, hd⟩
  obtain ⟨V, hVG, hVo, hzV⟩ := mem_nhds_iff.mp hG
  let a := (hF.toOpenPartialHomeomorph f).restrOpen V hVo
  have hcoe : (a : ℂ → ℂ) = f := hF.toOpenPartialHomeomorph_coe
  refine ⟨a, ⟨hsrc, hzV⟩, ?_, ?_, ?_⟩
  · intro hzero
    exact (hVG hzero.2).1 rfl
  · intro u hu
    simpa only [hcoe] using (hVG hu.2).2.1
  · intro u hu
    simpa only [hcoe, one_mul] using (hVG hu.2).2.2

end LowDimensionalTopology.Geometry.Teichmuller
