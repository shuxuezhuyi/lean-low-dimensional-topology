module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistNativeInfinitesimal
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchySeriesThirdDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicDerivative
public import LowDimensionalTopology.Geometry.Quasiconformal.OffSupportCauchyKernels

/-!
# The actual Bers derivative of the same angular infinitesimal

The proved fourth-kernel formula identifies the third Cauchy derivative
with the genuine automorphic Frechet derivative on the same compatible
coefficient class. One original geodesic then supplies one normalized
covering and the actual locally uniform series for every right-coset section.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open LowDimensionalTopology.Geometry.Surfaces

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The same entire angular coefficient gives the true Bers derivative and
the third spatial derivative of its normalized Cauchy variation. -/
theorem rightCosetInfinitesimalSum_fderiv_bers
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) [Countable Γ]
    (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v)
    (ν : GammaMeasurableBeltrami.Space Γ)
    (hν : (ν.val : ℍ → ℂ) =ᵐ[volume]
      (fun z : ℍ => rightCosetInfinitesimalSum θ Γ s (z : ℂ))) :
    EqOn
      (((fderiv ℂ (BersWeighted.automorphicProjection hΓ) 0 ν).toSource) : ℂ → ℂ)
      (iteratedDeriv 3 (LiZhongQC.ahVar (rightCosetInfinitesimalSum θ Γ s)))
      LiZhongQC.lowerHalf := by
  let η := rightCosetInfinitesimalSum θ Γ s
  let B := 1 / (4 * (θ : ℝ))
  obtain ⟨hm, hb, _⟩ := rightCosetCauchySeries_hasSum θ Γ s hsep
  have hB : 0 ≤ B := one_div_nonneg.mpr (mul_nonneg (by norm_num) θ.property.1.le)
  have hη : LiZhongQC.IsBeltramiCoeff η univ B :=
    ⟨hm.aestronglyMeasurable.restrict, Filter.Eventually.of_forall hb⟩
  have hzero (ζ : ℂ) (hζ : ζ ∉ LiZhongQC.upperHalf) : η ζ = 0 := by
    change (∑' u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
      rightCosetInfinitesimalZeroExtension θ Γ s u ζ) = 0
    change ¬ (0 : ℝ) < ζ.im at hζ
    have hu : ∀ u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ = 0 := by
      intro u
      refine Quotient.inductionOn u ?_
      intro γ
      change pullbackInfinitesimalZeroExtension θ γ.val ζ = 0
      exact pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos θ γ.val
        (le_of_not_gt hζ)
    simp only [hu, tsum_zero]
  have hae : GammaMeasurableBeltrami.planeRepresentative ν.val
      =ᵐ[volume.restrict LiZhongQC.upperHalf] η := by
    apply GammaMeasurableBeltrami.ae_plane_iff.mpr
    filter_upwards [hν] with z hzν
    exact (GammaMeasurableBeltrami.planeRepresentative_coe ν.val z).trans hzν
  intro z hz
  have hsub : LiZhongQC.lowerHalf ⊆ LiZhongQC.upperHalfᶜ := by
    intro w hw
    change w.im < (0 : ℝ) at hw
    change ¬ (0 : ℝ) < w.im
    exact not_lt_of_ge hw.le
  have hz' : z ∈ interior LiZhongQC.upperHalfᶜ :=
    interior_mono hsub (by simpa only [LiZhongQC.isOpen_lowerHalf.interior_eq] using hz)
  have hthird := Quasiconformal.OffSupportCauchy.thirdDerivative_firstVariation
    LiZhongQC.isOpen_upperHalf.measurableSet hB hη
    (Filter.Eventually.of_forall hzero) hz'
  rw [BersWeighted.fderiv_automorphicProjection hΓ]
  calc
    _ = LiZhongQC.bersDerivative (GammaMeasurableBeltrami.planeRepresentative ν.val) z :=
      BersWeighted.integralOperator_decode_eqOn ν hz
    _ = LiZhongQC.bersDerivative η z := BersWeighted.bersDerivative_congr_ae hae z
    _ = iteratedDeriv 3 (LiZhongQC.ahVar η) z := hthird.symm

/-- One normalization of the same original geodesic yields the actual Bers
derivative series, with genuine sums and local uniform convergence. -/
theorem originalClosedGeodesic_exists_normalized_angular_bers_series
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
      let hpQ := LiZhongQC.adjustProjection_isUniformization hp Q
      let hΓQ : LiZhongQC.IsFuchsian ΓQ := LiZhongQC.utm_x_isFuchsian hpQ
      let θ := canonicalBandWidth s hs
      let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s))
      let m : ΓQ → ℂ → ℂ := fun γ =>
        LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
      ∃ ν : GammaMeasurableBeltrami.Space ΓQ,
        (ν.val : ℍ → ℂ) =ᵐ[volume]
          (fun z : ℍ => rightCosetInfinitesimalSum θ ΓQ s (z : ℂ)) ∧
        ‖ν‖ ≤ 1 / (4 * (θ : ℝ)) ∧
        let D : ℂ → ℂ :=
          ((fderiv ℂ (BersWeighted.automorphicProjection hΓQ) 0 ν).toSource : ℂ → ℂ)
        EqOn D
          (iteratedDeriv 3 (LiZhongQC.ahVar (rightCosetInfinitesimalSum θ ΓQ s)))
          LiZhongQC.lowerHalf ∧
        ∀ ρ : C → ΓQ, (∀ u : C, Quotient.mk _ (ρ u) = u) →
          (∀ z : ℂ, z ∈ LiZhongQC.lowerHalf →
            HasSum (fun u : C => (Complex.I / (2 * (Real.pi : ℂ))) *
              (deriv (m (ρ u)) z / m (ρ u) z) ^ 2) (D z) ∧
            D z = (Complex.I / (2 * (Real.pi : ℂ))) *
              ∑' u : C, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2) ∧
          TendstoLocallyUniformlyOn
            (fun (E : Finset C) (z : ℂ) => (Complex.I / (2 * (Real.pi : ℂ))) *
              ∑ u ∈ E, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
            D (atTop : Filter (Finset C)) LiZhongQC.lowerHalf := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  obtain ⟨A, Q, s, hs, hA, hcov, hQA, hsep⟩ :=
    originalClosedGeodesic_exists_normalized_angular_one_support q hp hcircle
  refine ⟨A, Q, s, hs, hA, hcov, hQA, ?_⟩
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  have hpQ := LiZhongQC.adjustProjection_isUniformization hp Q
  let hΓQ : LiZhongQC.IsFuchsian ΓQ := LiZhongQC.utm_x_isFuchsian hpQ
  let θ := canonicalBandWidth s hs
  have hcount : (ΓQ : Set Deck).Countable := by
    rw [Subgroup.coe_map]
    exact (LiZhongQC.h36p_countable (LiZhongQC.utm_x2_isFuchsian hp)).image _
  let : Countable ΓQ := hcount.to_subtype
  obtain ⟨ν, hν, hνnorm⟩ := exists_rightCosetInfinitesimalSum_native θ ΓQ s hsep
  have he := rightCosetInfinitesimalSum_fderiv_bers θ ΓQ s hΓQ hsep ν hν
  refine ⟨ν, hν, hνnorm, he, ?_⟩
  intro ρ hρ
  obtain ⟨hlocal, hpoint⟩ :=
    (rightCosetCauchySeries_thirdDerivative θ ΓQ s hsep).2 ρ hρ
  refine ⟨?_, hlocal.congr_right (fun z hz => (he hz).symm)⟩
  intro z hz
  have hs' := hpoint z hz
  exact ⟨(he hz).symm ▸ hs'.1, (he hz).trans hs'.2⟩

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
