module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceCompactFundamentalDomain
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral

/-!
# Unweighted integrability of the original measurable source coefficient

An actual compact fundamental domain has a uniform positive lower height and
finite planar area. Thus the original almost-everywhere height-weighted bound
bounds the same measurable coefficient on this domain. Only the height
function is used continuously; the coefficient retains only its stated a.e.
measurability and weighted-bound hypotheses.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

/-- The same original compact cover has a genuine compact integration domain
on which the literal measurable coefficient is integrable without its height
weight. No continuity or holomorphicity of the coefficient is assumed. -/
theorem exists_sourceCompactFundamentalDomainH_integrable_of_weighted_bound
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f ((volume : Measure ℂ).restrict LiZhongQC.upperHalf))
    (hb : ∃ M : ℝ, ∀ᵐ z ∂((volume : Measure ℂ).restrict LiZhongQC.upperHalf),
      ‖f z‖ * z.im ^ 2 ≤ M) :
    ∃ F : Set ℂ, LiZhongQC.IsFundamentalDomainH Γ F ∧ IsCompact F ∧ IntegrableOn f F := by
  obtain ⟨F, hF, hCF⟩ := exists_sourceCompactFundamentalDomainH R hΓ hp
  refine ⟨F, hF, hCF, ?_⟩
  obtain ⟨M, hM⟩ := hb
  obtain ⟨δ, hδ, hδF⟩ := hCF.exists_forall_le'
    Complex.continuous_im.continuousOn (fun z hz => hF.1 hz)
  let : IsFiniteMeasure ((volume : Measure ℂ).restrict F) :=
    isFiniteMeasure_restrict.mpr hCF.measure_ne_top
  refine ⟨AEStronglyMeasurable.mono_set hF.1 hf, ?_⟩
  apply HasFiniteIntegral.of_bounded (C := M / δ ^ 2)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hF.1 hM,
    ae_restrict_mem hF.2.1] with z hz hzF
  have hsquare : δ ^ 2 ≤ z.im ^ 2 :=
    (sq_le_sq₀ hδ.le (hF.1 hzF).le).mpr (hδF z hzF)
  exact (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
    ((mul_le_mul_of_nonneg_left hsquare (norm_nonneg (f z))).trans hz)

end LowDimensionalTopology.Geometry.Teichmuller
