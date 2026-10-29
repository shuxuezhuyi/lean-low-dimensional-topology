module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCanonicalCoefficientCurve
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchySeriesThirdDerivative

/-!
# The original canonical angular variation and its third-derivative series

One original period-circle geodesic and its actual covering choose one
full-period matrix and positive normalized coordinate. The literal
coefficient family, its selected canonical plane solutions and the spatial
third-derivative series use those same choices. Countability is derived
from the original covering, and the series formula holds for every actual
choice of right-coset representatives.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open LowDimensionalTopology.Geometry.Surfaces

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The same original data construct the canonical zero-extended plane
variation and its locally uniform third-derivative series. -/
theorem originalClosedGeodesic_exists_canonical_angular_thirdDerivative_series
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ∃ (A Q : Deck) (s : ℝ) (hs : 0 < s), A ∈ Γ ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
        Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s) ∧
      let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
      let θ := canonicalBandWidth s hs
      let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s))
      let ν : ℂ → ℂ := fun ζ =>
        ∑' u : C, rightCosetInfinitesimalZeroExtension θ ΓQ s u ζ
      let m : ΓQ → ℂ → ℂ := fun γ =>
        LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
      ∃ μ : ℝ → MeasurableBeltramiBall,
        (∀ t : ℝ, ((μ t).val : ℂ → ℂ) =ᵐ[volume]
          rightCosetCoefficientSum θ ΓQ s t) ∧
        (μ 0).val = 0 ∧
        TendstoLocallyUniformly
          (fun t w =>
            (MeasurableBeltramiBall.normalizedSolution (μ t) w - w) / (t : ℂ))
          (LiZhongQC.ahVar ν) (𝓝[≠] (0 : ℝ)) ∧
        (∀ w : ℂ,
          HasDerivAt (fun t : ℝ => MeasurableBeltramiBall.normalizedSolution (μ t) w)
            (LiZhongQC.ahVar ν w) 0) ∧
        ∀ ρ : C → ΓQ, (∀ u : C, Quotient.mk _ (ρ u) = u) →
          TendstoLocallyUniformlyOn
            (fun (F : Finset C) (z : ℂ) =>
              (Complex.I / (2 * (Real.pi : ℂ))) *
                ∑ u ∈ F, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
            (iteratedDeriv 3 (LiZhongQC.ahVar ν)) (atTop : Filter (Finset C))
            LiZhongQC.lowerHalf ∧
          ∀ z : ℂ, z ∈ LiZhongQC.lowerHalf →
            HasSum (fun u : C => (Complex.I / (2 * (Real.pi : ℂ))) *
              (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
              (iteratedDeriv 3 (LiZhongQC.ahVar ν) z) ∧
            iteratedDeriv 3 (LiZhongQC.ahVar ν) z =
              (Complex.I / (2 * (Real.pi : ℂ))) *
                ∑' u : C, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  obtain ⟨A, Q, s, hs, hA, hcov, hQA, hsep⟩ :=
    originalClosedGeodesic_exists_normalized_angular_one_support q hp hcircle
  refine ⟨A, Q, s, hs, hA, hcov, hQA, ?_⟩
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  have hcount : (ΓQ : Set Deck).Countable := by
    rw [Subgroup.coe_map]
    exact (LiZhongQC.h36p_countable (LiZhongQC.utm_x2_isFuchsian hp)).image _
  let : Countable ΓQ := hcount.to_subtype
  obtain ⟨_v, μ, _ε, _hv, _hvnorm, hμ, _hdecomp, _hε, hzero, hvar, hderiv⟩ :=
    exists_rightCosetCoefficientSum_canonical_variation (canonicalBandWidth s hs) ΓQ s hsep
  refine ⟨μ, hμ, hzero, hvar, hderiv, ?_⟩
  exact (rightCosetCauchySeries_thirdDerivative (canonicalBandWidth s hs) ΓQ s hsep).2

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
