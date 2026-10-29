module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersRealMobiusCovariance
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistActualBersSeries
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistPeterssonSeriesReflection
public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicPeterssonSeries
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# The same angular direction in the original covering group

The true derivative of the native Bers projection commutes with the actual
coefficient and quadratic isometries. The full cyclic-coset transport and
reflection then give the same endpoint-seed series in the original group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter
open scoped UpperHalfPlane ComplexConjugate Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open GammaMeasurableBeltrami

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The same whole direction has the actual derivative and the literal
full-cyclic endpoint series in the original covering coordinates. -/
theorem givenAngularInfinitesimal_originalGamma_bers_series
    (Γ : Subgroup Deck) (hΓ : LiZhongQC.IsFuchsian Γ)
    (A : Deck) (_hAΓ : A ∈ Γ)
    (hA : Hyperbolic.realSLMobius A ≠ 1)
    (ht : 4 < (Matrix.trace A.val) ^ 2)
    (Q : Deck) (s : ℝ) (hs : 0 < s)
    (hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
    (ν : GammaMeasurableBeltrami.Space (LiZhongQC.conjGroup Γ Q))
    (hν : (ν.val : ℍ → ℂ) =ᵐ[MeasureTheory.volume]
      (fun z : ℍ => rightCosetInfinitesimalSum (canonicalBandWidth s hs)
        (LiZhongQC.conjGroup Γ Q) s (z : ℂ)))
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel
          (projectiveDilationSubgroup (LiZhongQC.conjGroup Γ Q) s)),
        rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs)
          (LiZhongQC.conjGroup Γ Q) s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs)
          (LiZhongQC.conjGroup Γ Q) s v ζ ≠ 0 → u = v) :
    let hΓQ := BersWeighted.isFuchsian_realConjugate hΓ Q
    let I := coefficientRealMobiusIsometry Γ Q
    let U := BersWeighted.automorphicRealMobiusIsometry Γ Q
    let DQ := fderiv ℂ (BersWeighted.automorphicProjection hΓQ) 0 ν
    let D := fderiv ℂ (BersWeighted.automorphicProjection hΓ) 0 (I ν)
    U DQ = D ∧
      ∀ (ρ : Quotient (QuotientGroup.rightRel
          (Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
            (Subgroup.zpowers (Hyperbolic.realSLMobius A)))) → Γ),
        (∀ u, Quotient.mk _ (ρ u) = u) →
        ∀ z : ℂ, z ∈ LiZhongQC.lowerHalf →
          (D.toSource : ℂ → ℂ) z =
            (Complex.I / (2 * (Real.pi : ℂ))) *
              conj (GeodesicSeries.peterssonSeries Γ A hA ht ρ (conj z)) := by
  let ΓQ := LiZhongQC.conjGroup Γ Q
  let hΓQ := BersWeighted.isFuchsian_realConjugate hΓ Q
  let I := coefficientRealMobiusIsometry Γ Q
  let U := BersWeighted.automorphicRealMobiusIsometry Γ Q
  let DQ := fderiv ℂ (BersWeighted.automorphicProjection hΓQ) 0 ν
  let D := fderiv ℂ (BersWeighted.automorphicProjection hΓ) 0 (I ν)
  have hnear :
      (fun μ : Space ΓQ => U (BersWeighted.automorphicProjection hΓQ μ)) =ᶠ[𝓝 0]
        (fun μ : Space ΓQ => BersWeighted.automorphicProjection hΓ (I μ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Space ΓQ) (show (0 : ℝ) < 1 by norm_num)]
      with μ hμ
    exact BersWeighted.automorphicRealMobiusIsometry_projection hΓ Q ⟨μ, hμ⟩
  have hleft := U.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp (0 : Space ΓQ)
    (BersWeighted.hasFDerivAt_automorphicProjection hΓQ)
  have hΓderiv : HasFDerivAt (BersWeighted.automorphicProjection hΓ)
      (BersWeighted.automorphicIntegralOperator hΓ) (I (0 : Space ΓQ)) := by
    simpa only [map_zero] using BersWeighted.hasFDerivAt_automorphicProjection hΓ
  have hright := hΓderiv.comp (0 : Space ΓQ) I.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  have hCov : U DQ = D := by
    dsimp only [DQ, D]
    rw [BersWeighted.fderiv_automorphicProjection hΓQ,
      BersWeighted.fderiv_automorphicProjection hΓ]
    exact congrArg (fun T : Space ΓQ →L[ℂ] BersWeighted.Automorphic Γ => T ν)
      (hleft.unique (hright.congr_of_eventuallyEq hnear))
  refine ⟨hCov, ?_⟩
  intro ρ hρ z hz
  let θ := canonicalBandWidth s hs
  let : Countable ΓQ := (LiZhongQC.h36p_countable hΓQ).to_subtype
  let CQ := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s))
  let m : ΓQ → ℂ → ℂ := fun δ => LiZhongQC.h36p_m δ.val
  let c : ℂ := Complex.I / (2 * (Real.pi : ℂ))
  obtain ⟨_e, ρQ, _hmk, _htransport, hρQ, hseries⟩ :=
    GeodesicSeries.geodesicSeries_realMobius_conjugate Γ A hA ht Q s hs hQA ρ hρ
  have hD := rightCosetInfinitesimalSum_fderiv_bers θ ΓQ s hΓQ hsep ν hν
  let w := LiZhongQC.utm_b_mob Q z
  have hw : w ∈ LiZhongQC.lowerHalf := LiZhongQC.bg2_a_mem Q hz
  have hwU : conj w ∈ LiZhongQC.upperHalf := by
    change 0 < (conj w).im
    rw [Complex.conj_im]
    exact neg_pos.mpr hw
  have hzU : conj z ∈ LiZhongQC.upperHalf := by
    change 0 < (conj z).im
    rw [Complex.conj_im]
    exact neg_pos.mpr hz
  have hQconj : LiZhongQC.h36p_m Q (conj z) = conj w := by
    change LiZhongQC.utm_b_mob Q (conj z) = conj (LiZhongQC.utm_b_mob Q z)
    exact (LiZhongQC.s33dim_conj_mob Q z).symm
  have hLower : (DQ.toSource : ℂ → ℂ) w =
      c * ∑' v : CQ, (deriv (m (ρQ v)) w / m (ρQ v) w) ^ 2 := by
    exact (hD hw).trans
      ((((rightCosetCauchySeries_thirdDerivative θ ΓQ s hsep).2 ρQ hρQ).2 w hw).2)
  have hReflect :
      (∑' v : CQ, (deriv (m (ρQ v)) w / m (ρQ v) w) ^ 2) =
        conj (∑' v : CQ,
          (deriv (m (ρQ v)) (LiZhongQC.h36p_m Q (conj z)) /
            m (ρQ v) (LiZhongQC.h36p_m Q (conj z))) ^ 2) := by
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro v
    rw [hQconj]
    simpa +unfoldPartialApp only [m, LiZhongQC.h36p_m, LiZhongQC.mobiusFn,
      Complex.conj_conj] using (squaredLogDeriv_mobius_conj (ρQ v).val hwU)
  have hOrig := hseries (conj z) hzU
  change GeodesicSeries.peterssonSeries Γ A hA ht ρ (conj z) = _ at hOrig
  have hConjOrig := congrArg conj hOrig
  simp only [map_div₀, map_pow, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_conj] at hConjOrig
  have hTransport : (D.toSource : ℂ → ℂ) z =
      (DQ.toSource : ℂ → ℂ) w / BersWeighted.realMobiusDenom Q z ^ 4 := by
    rw [← hCov, BersWeighted.automorphicRealMobiusIsometry_toSource]
    exact BersWeighted.realMobiusPullback_apply Q _ hz
  calc
    (D.toSource : ℂ → ℂ) z =
        (DQ.toSource : ℂ → ℂ) w / BersWeighted.realMobiusDenom Q z ^ 4 := hTransport
    _ = (c * ∑' v : CQ, (deriv (m (ρQ v)) w / m (ρQ v) w) ^ 2) /
        BersWeighted.realMobiusDenom Q z ^ 4 := by rw [hLower]
    _ = c * (conj (∑' v : CQ,
        (deriv (m (ρQ v)) (LiZhongQC.h36p_m Q (conj z)) /
          m (ρQ v) (LiZhongQC.h36p_m Q (conj z))) ^ 2) /
        BersWeighted.realMobiusDenom Q z ^ 4) := by rw [hReflect]; ring
    _ = c * conj (GeodesicSeries.peterssonSeries Γ A hA ht ρ (conj z)) := by
      exact congrArg (fun a => c * a) hConjOrig.symm

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
