module

public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeDisplacementBounds
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientRealMobiusNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealMobiusCoefficientPairing
public import LowDimensionalTopology.Geometry.Teichmuller.RealMobiusFundamentalRegion
public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeriesRealMobius
public import LowDimensionalTopology.Geometry.Teichmuller.SymmetricNativeMarkedLengthPetersson

/-!
# The original marked-length variation and its general endpoint series

The same original loop and prescribed covering group retain their actual
coefficient curve. A real Möbius normalization transports the covering lift,
full projective cyclic series, fundamental region and literal coefficient
pairing. Equality of the native marked-point germs identifies the resulting
derivative with that of the original marked-length scalar curve.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces GammaMeasurableBeltrami

/-- Every actual hyperbolic covering of the original loop has its native
marked-length first variation equal to the same original endpoint-series pairing. -/
theorem marked_length_hasDerivAt_general_endpoint_petersson
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (α : LiZhongQC.Loop X) (A : Deck) (hAΓ : A ∈ Γ)
    (hcov : LiZhongQC.Covers p A α)
    (hA : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (μ : Space Γ) :
    letI := R.toRiemannAtlas.toChartedSpace
    let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
      (Subgroup.zpowers (Hyperbolic.realSLMobius A))
    let CA := Quotient (QuotientGroup.rightRel SA)
    ∀ (ρ : CA → Γ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
      ∀ (F : Set ℂ), LiZhongQC.IsFundamentalDomainH Γ F →
        let Θ : ℂ → ℂ := fun z => ∑' u : CA,
          GeodesicSeries.seed (Hyperbolic.hHyperbolicAxis A hA ht)
              (LiZhongQC.h36p_m (ρ u).val z) * (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2
        HasDerivAt
          (fun t : ℝ => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α
            (TeichmullerSpace.coefficientProjection R hg hgenus
              (canonicalHandleGroupPresentation g) hΓ (LiZhongQC.s27g_actsFreely hp) hp
              ((t : ℂ) • μ)))
          ((2 / Real.pi) * (LiZhongQC.beltramiPairing F
            (planeRepresentative μ.val) Θ).re) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  dsimp only
  intro ρ hρ F hF
  obtain ⟨Q, s, hs, hQA⟩ := Fuchsian.realSLMobius_hyperbolic_positive_log_normal_form A
    ((Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr ht)
  let ΓQ := LiZhongQC.conjGroup Γ Q
  let pQ := LiZhongQC.adjustProjection p Q
  have hpQ : LiZhongQC.IsUniformization ΓQ pQ := LiZhongQC.adjustProjection_isUniformization hp Q
  let hΓQ := BersWeighted.isFuchsian_realConjugate hΓ Q
  let μQ := (coefficientRealMobiusIsometry Γ Q).symm μ
  let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
    (Subgroup.zpowers (Hyperbolic.realSLMobius A))
  let CA := Quotient (QuotientGroup.rightRel SA)
  let CQ := Quotient (QuotientGroup.rightRel (AngularTwist.projectiveDilationSubgroup ΓQ s))
  obtain ⟨_e, ρQ, _hmk, _hρtransport, hρQ, hseries⟩ :=
    GeodesicSeries.geodesicSeries_realMobius_conjugate Γ A hA ht Q s hs hQA ρ hρ
  let Θ : ℂ → ℂ := fun z => ∑' u : CA,
    GeodesicSeries.seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
      (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2
  let ΘQ : ℂ → ℂ := fun w => ∑' v : CQ,
    (deriv (LiZhongQC.h36p_m (ρQ v).val) w / LiZhongQC.h36p_m (ρQ v).val w) ^ 2
  let FQ := LiZhongQC.h36p_m Q '' F
  have hFQ := fundamentalDomainH_realMobius_image Γ Q hF
  have hAQ : Q * A * Q⁻¹ ∈ ΓQ := Subgroup.mem_map.mpr ⟨A, hAΓ, rfl⟩
  have hcovQ : LiZhongQC.Covers pQ (Q * A * Q⁻¹) α := by
    obtain ⟨c, hcc, hcp, hc1⟩ := hcov
    refine ⟨fun t => Q • c t, (continuous_const_smul Q).comp_continuousOn hcc,
      fun t ht => ?_, ?_⟩
    · change p (Q⁻¹ • (Q • c t)) = α.2.extend t
      rw [inv_smul_smul]
      exact hcp t ht
    · change Q • c 1 = (Q * A * Q⁻¹) • (Q • c 0)
      rw [hc1, mul_smul, mul_smul, inv_smul_smul]
  have hpair : LiZhongQC.beltramiPairing F (planeRepresentative μ.val) Θ =
      LiZhongQC.beltramiPairing FQ (planeRepresentative μQ.val) ΘQ := by
    have hμ : coefficientRealMobiusIsometry Γ Q μQ = μ :=
      (coefficientRealMobiusIsometry Γ Q).apply_symm_apply μ
    have htransport := coefficientQuadraticPairing_realMobius Γ Q μQ hF.1 hF.2.1 ΘQ
    rw [hμ] at htransport
    calc
      _ = LiZhongQC.beltramiPairing F (planeRepresentative μ.val)
          (fun z => ΘQ (LiZhongQC.h36p_m Q z) / ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4) := by
        unfold LiZhongQC.beltramiPairing
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hF.2.1] with z hz
        rw [show Θ z = ΘQ (LiZhongQC.h36p_m Q z) /
          ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4 from hseries z (hF.1 hz)]
      _ = _ := htransport
  have hd : HasDerivAt
      (fun t : ℝ => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α
        (TeichmullerSpace.coefficientProjection R hg hgenus
          (canonicalHandleGroupPresentation g) hΓQ (LiZhongQC.s27g_actsFreely hpQ) hpQ
          ((t : ℂ) • μQ)))
      ((2 / Real.pi) * (LiZhongQC.beltramiPairing FQ (planeRepresentative μQ.val) ΘQ).re) 0 :=
    marked_length_hasDerivAt_relative_petersson R hg hgenus
      (canonicalHandleGroupPresentation g) hΓQ (LiZhongQC.s27g_actsFreely hpQ) hpQ α
      (Q * A * Q⁻¹) hAQ hcovQ s hs hQA μQ ρQ hρQ FQ hFQ
  rw [← hpair] at hd
  have hcurve := TeichmullerSpace.coefficientProjection_realScalar_realMobius_germ
    R hg hgenus hΓ hp Q μ
  apply hd.congr_of_eventuallyEq
  filter_upwards [hcurve] with t ht
  exact congrArg (markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α) ht

end LowDimensionalTopology.Geometry.Teichmuller
