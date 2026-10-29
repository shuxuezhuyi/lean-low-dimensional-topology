module

public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeDisplacementBounds
public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeriesRealMobius
public import LowDimensionalTopology.Geometry.Teichmuller.RealMobiusFundamentalRegion
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersRealMobiusCovariance

/-!
# The original endpoint series on the original fundamental region

The same real Möbius change transports the proved normalized holomorphic
quadratic differential. Its actual fourth denominator preserves the area
integral on the same image region and gives the original group law.

The quadratic and measurable-region APIs reuse Wu Xiaobin's Li-Zhong-QC
formalization, Apache-2.0, pinned commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries

open GammaMeasurableBeltrami

private def upperPullback (Q : Deck) (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  φ (LiZhongQC.h36p_m Q z) / ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4

private theorem upperPullback_comp (Q B : Deck) (φ : ℂ → ℂ)
    {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    upperPullback Q (upperPullback B φ) z = upperPullback (B * Q) φ z := by
  dsimp only [upperPullback]
  rw [LiZhongQC.h36p_b_m_mul B Q hz, LiZhongQC.h36p_b_j_mul B Q hz,
    mul_pow, div_div]

private theorem upperPullback_mem (Γ : Subgroup Deck) (Q : Deck) {F : Set ℂ}
    (hFH : F ⊆ LiZhongQC.upperHalf) (hFm : MeasurableSet F) {φ : ℂ → ℂ}
    (hφ : φ ∈ LiZhongQC.integrableAutomorphicQD (LiZhongQC.conjGroup Γ Q)
      (LiZhongQC.h36p_m Q '' F)) :
    upperPullback Q φ ∈ LiZhongQC.integrableAutomorphicQD Γ F := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hcomp := (hφ.1.differentiableAt
      (LiZhongQC.isOpen_upperHalf.mem_nhds (LiZhongQC.h36p_m_mem Q hz))).comp z
        (LiZhongQC.h36p_m_hasDerivAt Q hz).differentiableAt
    have hden : DifferentiableAt ℂ (fun w : ℂ =>
        ((Q 1 0 : ℂ) * w + Q 1 1) ^ 4) z :=
      (((differentiableAt_const _).mul differentiableAt_id).add_const _).pow 4
    exact (hcomp.div hden (pow_ne_zero _ (denominator_ne_zero Q ⟨z, hz⟩))).differentiableWithinAt
  · have harea : LiZhongQC.phiArea (upperPullback Q φ) F =
        LiZhongQC.phiArea φ (LiZhongQC.h36p_m Q '' F) := by
      unfold LiZhongQC.phiArea
      rw [LiZhongQC.h36p_b_lintegral_image Q hFm hFH]
      apply setLIntegral_congr_fun hFm
      intro z _hz
      dsimp only [upperPullback]
      rw [LiZhongQC.h36p_b_norm_term, ENNReal.ofReal_mul (norm_nonneg _)]
    rw [harea]
    exact hφ.2.1
  · intro γ hγ z hz
    change upperPullback γ (upperPullback Q φ) z = upperPullback Q φ z
    let δ : Deck := Q * γ * Q⁻¹
    have hδ : δ ∈ LiZhongQC.conjGroup Γ Q := Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩
    have hmatrix : Q * γ = δ * Q := by
      dsimp only [δ]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    have hfix (w : ℂ) (hw : w ∈ LiZhongQC.upperHalf) : upperPullback δ φ w = φ w :=
      hφ.2.2 δ hδ w hw
    calc
      _ = upperPullback (Q * γ) φ z := upperPullback_comp γ Q φ hz
      _ = upperPullback (δ * Q) φ z := by rw [hmatrix]
      _ = upperPullback Q (upperPullback δ φ) z := (upperPullback_comp Q δ φ hz).symm
      _ = _ := by
        change upperPullback δ φ (LiZhongQC.h36p_m Q z) /
          ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4 = _
        rw [hfix _ (LiZhongQC.h36p_m_mem Q hz)]
        rfl

/-- On every original fundamental region, the literal endpoint series is
holomorphic, integrable, and quadratic automorphic for the same original group. -/
theorem geodesicSeries_mem_integrableAutomorphicQD
    (Γ : Subgroup Deck) (hΓ : LiZhongQC.IsFuchsian Γ) (A : Deck) (hAΓ : A ∈ Γ)
    (hA : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2) :
    let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
      (Subgroup.zpowers (Hyperbolic.realSLMobius A))
    let CA := Quotient (QuotientGroup.rightRel SA)
    ∀ (ρ : CA → Γ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
      ∀ (F : Set ℂ), LiZhongQC.IsFundamentalDomainH Γ F →
        (fun z : ℂ => ∑' u : CA,
          seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
            (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2) ∈
          LiZhongQC.integrableAutomorphicQD Γ F := by
  dsimp only
  intro ρ hρ F hF
  obtain ⟨Q, s, hs, hQA⟩ := Fuchsian.realSLMobius_hyperbolic_positive_log_normal_form A
    ((Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr ht)
  let ΓQ := LiZhongQC.conjGroup Γ Q
  let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
    (Subgroup.zpowers (Hyperbolic.realSLMobius A))
  let CA := Quotient (QuotientGroup.rightRel SA)
  let CQ := Quotient (QuotientGroup.rightRel (AngularTwist.projectiveDilationSubgroup ΓQ s))
  obtain ⟨_e, ρQ, _hmk, _hρtransport, hρQ, hseries⟩ :=
    geodesicSeries_realMobius_conjugate Γ A hA ht Q s hs hQA ρ hρ
  let Θ : ℂ → ℂ := fun z => ∑' u : CA,
    seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
      (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2
  let ΘQ : ℂ → ℂ := fun w => ∑' v : CQ,
    (deriv (LiZhongQC.h36p_m (ρQ v).val) w / LiZhongQC.h36p_m (ρQ v).val w) ^ 2
  have hΓQ := BersWeighted.isFuchsian_realConjugate hΓ Q
  have hAQ : Q * A * Q⁻¹ ∈ ΓQ := Subgroup.mem_map.mpr ⟨A, hAΓ, rfl⟩
  have hFQ := fundamentalDomainH_realMobius_image Γ Q hF
  have hrelative := AngularTwist.lengthKernel_relative_poincare ΓQ hΓQ
    (Q * A * Q⁻¹) hAQ s hs hQA ρQ hρQ
  have hΘQ : ΘQ ∈ LiZhongQC.integrableAutomorphicQD ΓQ (LiZhongQC.h36p_m Q '' F) :=
    (hrelative.2 _ hFQ).1
  have hpull := upperPullback_mem Γ Q hF.1 hF.2.1 hΘQ
  have heq (z : ℂ) (hz : z ∈ LiZhongQC.upperHalf) : Θ z = upperPullback Q ΘQ z :=
    hseries z hz
  change Θ ∈ LiZhongQC.integrableAutomorphicQD Γ F
  refine ⟨hpull.1.congr heq, ?_, ?_⟩
  · have harea : LiZhongQC.phiArea Θ F = LiZhongQC.phiArea (upperPullback Q ΘQ) F := by
      unfold LiZhongQC.phiArea
      apply setLIntegral_congr_fun hF.2.1
      intro z hz
      exact congrArg (fun w : ℂ => ENNReal.ofReal ‖w‖) (heq z (hF.1 hz))
    rw [harea]
    exact hpull.2.1
  · intro γ hγ z hz
    change Θ (LiZhongQC.h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = Θ z
    rw [heq z hz, heq (LiZhongQC.h36p_m γ z) (LiZhongQC.h36p_m_mem γ hz)]
    exact hpull.2.2 γ hγ z hz

end LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries
