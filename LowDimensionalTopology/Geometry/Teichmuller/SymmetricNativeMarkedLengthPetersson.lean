module

public import LowDimensionalTopology.Geometry.Teichmuller.SymmetricNativeMarkedLengthDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.AngularLengthKernelPoincare
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.Ring

/-!
# The same mirror integral and the actual marked-length first variation

Conjugation identifies the lower-half-plane integral with the conjugate of
the upper-half-plane integral for the same symmetric coefficient. The actual
length derivative and the full-period relative Poincare identity then give
the literal real coefficient pairing, with the same normalized covering data.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

private theorem lengthKernel_conj (s : ℝ) (z : ℂ) :
    conj (LiZhongQC.ahKer (Real.exp (2 * s) : ℂ) (conj z) / (Real.exp (2 * s) : ℂ)) =
      LiZhongQC.ahKer (Real.exp (2 * s) : ℂ) z / (Real.exp (2 * s) : ℂ) := by
  simp only [LiZhongQC.ahKer, map_div₀, map_mul, map_sub, map_one,
    Complex.conj_ofReal, Complex.conj_conj]

/-- The actual given mirror representative has its genuine integrable
two-half-plane comparison and the exact normalized real first variation. -/
theorem same_symmetric_direction_integral_comparison
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (μ : GammaMeasurableBeltrami.Space Γ) (η : MeasurableBeltramiSpace)
    (hη : (η : ℂ → ℂ) =ᵐ[volume]
      LiZhongQC.s27u_symExt (GammaMeasurableBeltrami.planeRepresentative μ.val))
    (s : ℝ) (hs : 0 < s) :
    let lam := Real.exp (2 * s)
    let κ := GammaMeasurableBeltrami.planeRepresentative μ.val
    let f : ℂ → ℂ := fun ζ => LiZhongQC.ahKer (lam : ℂ) ζ / (lam : ℂ)
    Integrable (fun ζ : ℂ => LiZhongQC.s27u_symExt κ ζ * f ζ) volume ∧
      (∫ ζ : ℂ, LiZhongQC.s27u_symExt κ ζ * f ζ) =
        (∫ ζ in LiZhongQC.upperHalf, κ ζ * f ζ) +
          conj (∫ ζ in LiZhongQC.upperHalf, κ ζ * f ζ) ∧
      (Quasiconformal.firstVariation η (lam : ℂ)).re / lam =
        -(2 / Real.pi) * (∫ ζ in LiZhongQC.upperHalf, κ ζ * f ζ).re := by
  classical
  let lam := Real.exp (2 * s)
  let κ := GammaMeasurableBeltrami.planeRepresentative μ.val
  let f : ℂ → ℂ := fun ζ => LiZhongQC.ahKer (lam : ℂ) ζ / (lam : ℂ)
  let σ := LiZhongQC.s27u_symExt κ
  have hlam : 1 < lam := Real.one_lt_exp_iff.mpr (mul_pos zero_lt_two hs)
  have hlam0 : (lam : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans hlam))
  have hκ := GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val
  have hσ := LiZhongQC.s27u_b_s_beltrami hκ
  have hint : Integrable (fun ζ : ℂ => σ ζ * f ζ) volume := by
    apply ((LiZhongQC.ah_ker_integrable (lam : ℂ)).div_const (lam : ℂ)).bdd_mul
    · simpa only [Measure.restrict_univ] using hσ.1
    · simpa only [Measure.restrict_univ] using hσ.2
  have hmp : MeasurePreserving (fun z : ℂ => conj z)
      (volume.restrict LiZhongQC.lowerHalf) (volume.restrict LiZhongQC.upperHalf) := by
    have h := LiZhongQC.gzE_conj_measurePreserving.restrict_preimage
      LiZhongQC.isOpen_upperHalf.measurableSet
    rwa [LiZhongQC.s27u_b_s_conj_preimage_upperHalf] at h
  have hfc (z : ℂ) : conj (f (conj z)) = f z := lengthKernel_conj s z
  have hU : (∫ ζ in LiZhongQC.upperHalf, σ ζ * f ζ) =
      ∫ ζ in LiZhongQC.upperHalf, κ ζ * f ζ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with ζ hζ
    have hζ' : 0 < ζ.im := hζ
    change LiZhongQC.s27u_symExt κ ζ * f ζ = κ ζ * f ζ
    rw [LiZhongQC.s27u_symExt, ite_eq_right (not_lt.mpr hζ'.le)]
  have hL : (∫ ζ in LiZhongQC.lowerHalf, σ ζ * f ζ) =
      conj (∫ ζ in LiZhongQC.upperHalf, κ ζ * f ζ) := by
    have hc := hmp.integral_comp Complex.conjLIE.toHomeomorph.measurableEmbedding
      (fun ζ : ℂ => conj (κ ζ * f ζ))
    calc
      _ = ∫ ζ in LiZhongQC.lowerHalf, conj (κ (conj ζ) * f (conj ζ)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem LiZhongQC.isOpen_lowerHalf.measurableSet] with ζ hζ
        have hζ' : ζ.im < 0 := hζ
        change LiZhongQC.s27u_symExt κ ζ * f ζ = conj (κ (conj ζ) * f (conj ζ))
        rw [LiZhongQC.s27u_symExt, ite_eq_left hζ', map_mul, hfc]
      _ = ∫ ζ in LiZhongQC.upperHalf, conj (κ ζ * f ζ) := hc
      _ = _ := integral_conj
  have hsets : LiZhongQC.upperHalfᶜ =ᵐ[volume] LiZhongQC.lowerHalf := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 LiZhongQC.gzE_volume_im_eq_zero] with ζ hζ
    have hne : ζ.im ≠ 0 := hζ
    rcases lt_or_gt_of_ne hne with h | h
    · simp [LiZhongQC.upperHalf, LiZhongQC.lowerHalf, h, not_lt.mpr h.le]
    · simp [LiZhongQC.upperHalf, LiZhongQC.lowerHalf, h, not_lt.mpr h.le]
  have hfold : (∫ ζ : ℂ, σ ζ * f ζ) =
      (∫ ζ in LiZhongQC.upperHalf, κ ζ * f ζ) +
        conj (∫ ζ in LiZhongQC.upperHalf, κ ζ * f ζ) := by
    have h := integral_add_compl LiZhongQC.isOpen_upperHalf.measurableSet hint
    rw [setIntegral_congr_set hsets, hU, hL] at h
    exact h.symm
  have hFV := Quasiconformal.firstVariation_eq_of_ae η hη (lam : ℂ)
  change Quasiconformal.firstVariation η (lam : ℂ) =
    -(1 / (Real.pi : ℂ)) * (∫ ζ : ℂ, σ ζ * LiZhongQC.ahKer (lam : ℂ) ζ) at hFV
  have hdiv : Quasiconformal.firstVariation η (lam : ℂ) / (lam : ℂ) =
      -(1 / (Real.pi : ℂ)) * (∫ ζ : ℂ, σ ζ * f ζ) := by
    calc
      _ = -(1 / (Real.pi : ℂ)) *
          ((∫ ζ : ℂ, σ ζ * LiZhongQC.ahKer (lam : ℂ) ζ) / (lam : ℂ)) := by
        apply (div_eq_iff hlam0).2
        rw [mul_assoc, div_mul_cancel₀ _ hlam0, hFV]
      _ = _ := by
        rw [← integral_div]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ (fun ζ => by dsimp only [f]; ring)
  refine ⟨hint, hfold, ?_⟩
  have hπcast : -(1 / (Real.pi : ℂ)) = ((-(1 / Real.pi) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one]
  calc
    _ = (Quasiconformal.firstVariation η (lam : ℂ) / (lam : ℂ)).re :=
      (Complex.div_ofReal_re _ lam).symm
    _ = (-(1 / (Real.pi : ℂ)) *
        ((∫ ζ in LiZhongQC.upperHalf, κ ζ * f ζ) +
          conj (∫ ζ in LiZhongQC.upperHalf, κ ζ * f ζ))).re := by rw [hdiv, hfold]
    _ = _ := by
      rw [hπcast, Complex.re_ofReal_mul]
      simp only [Complex.add_re, Complex.conj_re]
      ring

/-- The original normalized marked-length scalar curve has its actual
first variation equal to the full-period relative Petersson coefficient pairing. -/
theorem marked_length_hasDerivAt_relative_petersson
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (α : LiZhongQC.Loop X) (A0 : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA0 : A0 ∈ Γ) (hcov : LiZhongQC.Covers p A0 α) (s : ℝ) (hs : 0 < s)
    (hproj : Hyperbolic.realSLMobius A0 =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
    (μ : GammaMeasurableBeltrami.Space Γ) :
    let C := Quotient (QuotientGroup.rightRel (AngularTwist.projectiveDilationSubgroup Γ s))
    let m : Γ → ℂ → ℂ := fun γ =>
      LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
    ∀ (ρ : C → Γ), (∀ u : C, Quotient.mk _ (ρ u) = u) →
      ∀ (F : Set ℂ), LiZhongQC.IsFundamentalDomainH Γ F →
        let Θ : ℂ → ℂ := fun z => ∑' u : C, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2
        HasDerivAt
          (fun t : ℝ => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α
            (TeichmullerSpace.coefficientProjection R hg hgenus hPresentation hΓ hfree hp
              ((t : ℂ) • μ)))
          ((2 / Real.pi) * (LiZhongQC.beltramiPairing F
            (GammaMeasurableBeltrami.planeRepresentative μ.val) Θ).re) 0 := by
  let C := Quotient (QuotientGroup.rightRel (AngularTwist.projectiveDilationSubgroup Γ s))
  let m : Γ → ℂ → ℂ := fun γ =>
    LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
  dsimp only
  intro ρ hρ F hF
  let Θ : ℂ → ℂ := fun z => ∑' u : C, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2
  obtain ⟨η, hη, _, hd⟩ := exists_marked_length_derivative_same_symmetric_direction
    (R := R) (hg := hg) (hgenus := hgenus) (hPresentation := hPresentation)
    (hΓ := hΓ) (hfree := hfree) (hp := hp) (α := α)
    (A0 := A0) (hA0 := hA0) (hcov := hcov) (s := s) (hs := hs) (hproj := hproj) μ
  have hmirror := (same_symmetric_direction_integral_comparison μ η hη s hs).2.2
  have hP := AngularTwist.lengthKernel_relative_poincare Γ hΓ A0 hA0 s hs hproj ρ hρ
  have hpair := (((hP.2 F hF).2) μ).2
  rw [hpair, Complex.neg_re] at hmirror
  have hvalue : (Quasiconformal.firstVariation η (Real.exp (2 * s) : ℂ)).re /
      Real.exp (2 * s) = (2 / Real.pi) *
        (LiZhongQC.beltramiPairing F (GammaMeasurableBeltrami.planeRepresentative μ.val)
          Θ).re := by
    exact hmirror.trans (by ring)
  rw [hvalue] at hd
  exact hd

end LowDimensionalTopology.Geometry.Teichmuller
