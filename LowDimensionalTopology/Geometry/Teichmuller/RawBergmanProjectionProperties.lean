module

public import LowDimensionalTopology.Geometry.Teichmuller.RawSeedBergmanSeries
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBergmanProperties
public import LowDimensionalTopology.Geometry.Teichmuller.SourceCompactFundamentalDomain

/-!
# Projection properties of the literal raw Bergman integral

Every original measurable weighted-bounded automorphic coefficient has a
holomorphic automorphic Bergman image. The same essential norm controls the
actual output coefficient, and the literal integral is idempotent on H.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic

open Surfaces LiZhongQC AutomorphicPoincare

variable {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict upperHalf))
    (ha : ∀ A ∈ Γ, ∀ z ∈ upperHalf,
      f (h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = f z)
    (hb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict upperHalf), ‖f z‖ * z.im ^ 2 ≤ M)

include hΓ hp hf ha hb

/-- The unchanged raw coefficient has a holomorphic, pointwise automorphic
Bergman image for its original compact uniformization. -/
theorem bergman_differentiableOn_and_automorphic :
    DifferentiableOn ℂ (bergman f) upperHalf ∧
      ∀ A ∈ Γ, ∀ z ∈ upperHalf,
        bergman f (h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = bergman f z := by
  obtain ⟨F, hF, _⟩ := exists_sourceCompactFundamentalDomainH R hΓ hp
  have hs := source_seed_differentiableOn_and_phiArea_lt_top R hΓ hp hF hf hb
  have hθ := (h36p_poincare hΓ hF hs.1 hs.2).1
  let m : ℂ := Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1))
  have hm : m ≠ 0 := by
    change (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) ≠ 0
    exact_mod_cast (h36p_mult_pos (Γ := Γ)).ne'
  have he : EqOn (bergman f)
      (fun z => m⁻¹ * h36p_theta Γ (seed F f) z) upperHalf := by
    intro z hz
    dsimp only
    rw [raw_seed_matrix_sum hΓ hF hf ha hb hz]
    change bergman f z = m⁻¹ * (m * bergman f z)
    rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]
  refine ⟨(hθ.1.const_mul m⁻¹).congr (fun z hz => he hz), ?_⟩
  intro A hA z hz
  rw [he (h36p_m_mem A hz), he hz, mul_div_assoc]
  exact congrArg (fun v : ℂ => m⁻¹ * v) (hθ.2.2 A hA z hz)

/-- The literal raw integral produces a genuine measurable weighted-bounded
holomorphic automorphic coefficient and fixes its own output on all of H.
The bound uses exactly the original input's weighted essential norm. -/
theorem bergman_projection_properties :
    DifferentiableOn ℂ (bergman f) upperHalf ∧
      (∀ A ∈ Γ, ∀ z ∈ upperHalf,
        bergman f (h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = bergman f z) ∧
      AEStronglyMeasurable (bergman f) (volume.restrict upperHalf) ∧
      (∀ z ∈ upperHalf, ‖bergman f z‖ * z.im ^ 2 ≤
        (2 * BersWeighted.kernelConstant) * weightedEssNorm (fun z : ℍ => f z)) ∧
      (∀ᵐ z ∂(volume.restrict upperHalf), ‖bergman f z‖ * z.im ^ 2 ≤
        (2 * BersWeighted.kernelConstant) * weightedEssNorm (fun z : ℍ => f z)) ∧
      EqOn (bergman (bergman f)) (bergman f) upperHalf := by
  obtain ⟨hd, hauto⟩ := bergman_differentiableOn_and_automorphic R hΓ hp f hf ha hb
  have hbound : ∀ z ∈ upperHalf, ‖bergman f z‖ * z.im ^ 2 ≤
      (2 * BersWeighted.kernelConstant) * weightedEssNorm (fun z : ℍ => f z) :=
    fun z hz => bergman_weighted_bound f hf ha hb hz
  refine ⟨hd, hauto, hd.continuousOn.aestronglyMeasurable
    isOpen_upperHalf.measurableSet, hbound, ?_, ?_⟩
  · exact (ae_restrict_mem isOpen_upperHalf.measurableSet).mono fun z hz => hbound z hz
  · exact bergman_eq_self_of_differentiable R p hp (bergman f) hd hauto

end LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic
