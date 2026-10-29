module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistPeterssonSeriesReflection
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicDecomposition
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistActualBersSeries
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistGivenHarmonicSeries

/-!
# The actual angular harmonic representative and its Petersson series

One original simple closed geodesic chooses one normalized covering.
The same entire infinitesimal defines the genuine compatible direction.
Its reflected derivative identity identifies an original global quadratic
differential with every actual convergent Petersson series. The existing
harmonic projection then gives the exact infinitesimal quotient class.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open LowDimensionalTopology.Geometry.Surfaces

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- In one normalized covering of the original geodesic, the actual angular
direction has its precise harmonic representative modulo the genuine Bers kernel. -/
theorem originalClosedGeodesic_exists_normalized_angular_harmonic_series
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {M : HyperbolicSurfaceModel R.toRiemannSurface} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R.t2Space
    let := R.connectedSpace
    let := R.compactSpace
    ∃ (A Q : Deck) (s : ℝ) (hs : 0 < s), A ∈ Γ ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
        Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s) ∧
      let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
      let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
      let hpQ : LiZhongQC.IsUniformization ΓQ pQ :=
        LiZhongQC.adjustProjection_isUniformization hp Q
      let θ := canonicalBandWidth s hs
      let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s))
      let m : ΓQ → ℂ → ℂ := fun γ =>
        LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
      ∃ ν : GammaMeasurableBeltrami.Space ΓQ,
        (ν.val : ℍ → ℂ) =ᵐ[volume]
          (fun z : ℍ => rightCosetInfinitesimalSum θ ΓQ s (z : ℂ)) ∧
        ‖ν‖ ≤ 1 / (4 * (θ : ℝ)) ∧
        ∀ (P : Fuchsian.HalfPlaneFuchsianGroup (ΓQ.map Hyperbolic.realSLMobius))
          (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F),
          ∃ Θ : HolomorphicQuadraticDifferential R.toRiemannAtlas,
            (∀ ρ : C → ΓQ, (∀ u : C, Quotient.mk _ (ρ u) = u) →
              (∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
                HasSum (fun u : C => (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
                  (QuadraticBergman.uniformizedQuadratic R pQ Θ z) ∧
                Summable (fun u : C => ‖(deriv (m (ρ u)) z / m (ρ u) z) ^ 2‖)) ∧
              TendstoLocallyUniformlyOn
                (fun (E : Finset C) (z : ℂ) =>
                  ∑ u ∈ E, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
                (QuadraticBergman.uniformizedQuadratic R pQ Θ)
                (atTop : Filter (Finset C)) LiZhongQC.upperHalf) ∧
            NativePetersson.harmonicProjection R P pQ hpQ F hF ν =
              (-(Complex.I / (Real.pi : ℂ))) •
                NativeHarmonicBeltrami.ofQuadratic R pQ hpQ Θ ∧
            ν - (-(Complex.I / (Real.pi : ℂ))) •
                NativeHarmonicBeltrami.ofQuadratic R pQ hpQ Θ ∈
              NativePetersson.infinitesimalSubmodule ΓQ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  obtain ⟨A, Q, s, hs, hA, hcov, hQA, hsep⟩ :=
    originalClosedGeodesic_exists_normalized_angular_one_support q hp hcircle
  refine ⟨A, Q, s, hs, hA, hcov, hQA, ?_⟩
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
  have hpQ : LiZhongQC.IsUniformization ΓQ pQ :=
    LiZhongQC.adjustProjection_isUniformization hp Q
  let θ := canonicalBandWidth s hs
  have hcount : (ΓQ : Set Deck).Countable := by
    rw [Subgroup.coe_map]
    exact (LiZhongQC.h36p_countable (LiZhongQC.utm_x2_isFuchsian hp)).image _
  let : Countable ΓQ := hcount.to_subtype
  obtain ⟨ν, hν, hνnorm⟩ := exists_rightCosetInfinitesimalSum_native θ ΓQ s hsep
  refine ⟨ν, hν, hνnorm, ?_⟩
  intro P F hF
  exact givenAngularInfinitesimal_exists_harmonic_series R θ ΓQ s pQ hpQ hsep ν hν P F hF

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
