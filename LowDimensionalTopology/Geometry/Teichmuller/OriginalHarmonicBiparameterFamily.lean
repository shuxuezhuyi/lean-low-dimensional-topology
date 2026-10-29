module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalHarmonicFirstJets
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The actual two-parameter normalized harmonic plane family -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

/-- The literal independent coefficients on the two half-planes. -/
def harmonicBiparameterCoefficient
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (s t z : ℂ) : ℂ :=
  if z.im < 0 then t * conj (harmonicPlane R p q (conj z))
  else s * harmonicPlane R p q z

/-- The actual normalized whole-plane solution for the two coefficients. -/
def canonicalBiparameterFamily
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (s t : ℂ) : ℂ → ℂ :=
  normalizedSolution (harmonicBiparameterCoefficient R p q s t)

/-- The conjugate diagonal is exactly the original symmetric family. -/
theorem canonicalBiparameterFamily_diagonal
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (s : ℂ) :
    canonicalBiparameterFamily R p q s (conj s) = canonicalFamily R p q s := by
  unfold canonicalBiparameterFamily canonicalFamily fMuSym
  congr 1
  funext z
  simp only [harmonicBiparameterCoefficient, symmetricExtension, map_mul]

/-- On one genuine parameter bidisc both actual normalized solutions and
separate pointwise parameter holomorphy follow from the original harmonic
bound. No spatial or integral derivative is assumed. -/
theorem canonicalBiparameterFamily_separately_holomorphic
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε →
        IsBeltramiCoeff (harmonicBiparameterCoefficient R p q s t) univ (1 / 2) ∧
        IsNormalizedSolution (canonicalBiparameterFamily R p q s t)
          (harmonicBiparameterCoefficient R p q s t)) ∧
      (∀ t : ℂ, ‖t‖ < ε → ∀ z : ℂ,
        DifferentiableOn ℂ (fun s => canonicalBiparameterFamily R p q s t z)
          (Metric.ball 0 ε)) ∧
      (∀ s : ℂ, ‖s‖ < ε → ∀ z : ℂ,
        DifferentiableOn ℂ (fun t => canonicalBiparameterFamily R p q s t z)
          (Metric.ball 0 ε)) := by
  classical
  let ν := harmonicPlane R p q
  let M : ℝ := ‖(NativeHarmonicBeltrami.ofQuadratic R p hp q).val‖
  have hM : 0 ≤ M := norm_nonneg _
  have hν : IsBeltramiCoeff ν upperHalf M := by
    have h := planeRepresentative_isBeltramiCoeff
      (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
    have he : planeRepresentative (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
        =ᵐ[volume.restrict upperHalf] ν :=
      NativeHarmonicBeltrami.planeRepresentative_ofQuadratic_ae R p hp q
    refine ⟨h.1.congr he, ?_⟩
    filter_upwards [he, h.2] with z hz hb
    rwa [← hz]
  have hiν : IsBeltramiCoeff (fun z => Complex.I * ν z) upperHalf M := by
    refine ⟨hν.1.const_mul Complex.I, ?_⟩
    filter_upwards [hν.2] with z hz
    simpa only [norm_mul, Complex.norm_I, one_mul] using hz
  have hσ := bg_s_beltrami hν
  have hτ := bg_s_beltrami hiν
  have hform (s t : ℂ) : harmonicBiparameterCoefficient R p q s t =
      fun z => ((s + t) / 2) * symmetricExtension ν z +
        ((s - t) / (2 * Complex.I)) *
          symmetricExtension (fun w => Complex.I * ν w) z := by
    funext z
    by_cases hz : z.im < 0
    · simp only [harmonicBiparameterCoefficient, symmetricExtension, ν, hz, ↓reduceIte,
        map_mul, Complex.conj_I]
      field_simp [Complex.I_ne_zero]
      ring
    · simp only [harmonicBiparameterCoefficient, symmetricExtension, ν, hz, ↓reduceIte]
      field_simp [Complex.I_ne_zero]
      ring
  let ε : ℝ := 1 / (4 * (M + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hM1 : M + 1 ≠ 0 := by positivity
  have hεM : 2 * ε * M < 1 / 2 := by
    calc
      _ < 2 * ε * (M + 1) := mul_lt_mul_of_pos_left (by linarith) (by positivity)
      _ = 1 / 2 := by dsimp only [ε]; field_simp [hM1]; ring
  have hcoeff (s t : ℂ) (hs : ‖s‖ < ε) (ht : ‖t‖ < ε) :
      IsBeltramiCoeff (harmonicBiparameterCoefficient R p q s t) univ (1 / 2) := by
    rw [hform]
    refine ⟨(hσ.1.const_mul _).add (hτ.1.const_mul _), ?_⟩
    have ha : ‖(s + t) / 2‖ ≤ (‖s‖ + ‖t‖) / 2 := by
      rw [norm_div, Complex.norm_ofNat]
      exact div_le_div_of_nonneg_right (norm_add_le s t) (by norm_num)
    have hb : ‖(s - t) / (2 * Complex.I)‖ ≤ (‖s‖ + ‖t‖) / 2 := by
      rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
      exact div_le_div_of_nonneg_right (norm_sub_le s t) (by norm_num)
    filter_upwards [hσ.2, hτ.2] with z hzσ hzτ
    calc
      _ ≤ ‖(s + t) / 2 * symmetricExtension ν z‖ +
          ‖(s - t) / (2 * Complex.I) *
            symmetricExtension (fun w => Complex.I * ν w) z‖ := norm_add_le _ _
      _ ≤ ((‖s‖ + ‖t‖) / 2) * M + ((‖s‖ + ‖t‖) / 2) * M := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul ha hzσ (norm_nonneg _) (by positivity))
          (mul_le_mul hb hzτ (norm_nonneg _) (by positivity))
      _ = (‖s‖ + ‖t‖) * M := by ring
      _ ≤ 2 * ε * M := mul_le_mul_of_nonneg_right (by linarith) hM
      _ ≤ 1 / 2 := hεM.le
  have hspec (s t : ℂ) (hs : ‖s‖ < ε) (ht : ‖t‖ < ε) :
      IsNormalizedSolution (canonicalBiparameterFamily R p q s t)
        (harmonicBiparameterCoefficient R p q s t) := by
    have hex : ∃ f : ℂ → ℂ,
        IsNormalizedSolution f (harmonicBiparameterCoefficient R p q s t) :=
      (thm13_7_normalized_existence (by norm_num) (by norm_num) (hcoeff s t hs ht)).imp
        fun _ hf => hf.1
    rw [canonicalBiparameterFamily, normalizedSolution, dite_eq_left hex]
    exact hex.choose_spec
  refine ⟨ε, hε, fun s t hs ht => ⟨hcoeff s t hs ht, hspec s t hs ht⟩, ?_, ?_⟩
  · intro t ht z
    have hhol (w : ℂ) : DifferentiableOn ℂ
        (fun s => harmonicBiparameterCoefficient R p q s t w) (Metric.ball 0 ε) := by
      let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
      by_cases hw : w.im < 0
      · simp only [harmonicBiparameterCoefficient, ite_eq_left hw]
        exact differentiableOn_const _
      · simp only [harmonicBiparameterCoefficient, ite_eq_right hw]
        intro a _
        exact (hasDerivAt_mul_const (x := a) _).differentiableAt.differentiableWithinAt
    exact thm13_8_ahlfors_bers_holomorphic Metric.isOpen_ball
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      (fun s hs => hcoeff s t (mem_ball_zero_iff.mp hs) ht) hhol
      (fun s hs => hspec s t (mem_ball_zero_iff.mp hs) ht) z
  · intro s hs z
    have hhol (w : ℂ) : DifferentiableOn ℂ
        (fun t => harmonicBiparameterCoefficient R p q s t w) (Metric.ball 0 ε) := by
      let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
      by_cases hw : w.im < 0
      · simp only [harmonicBiparameterCoefficient, ite_eq_left hw]
        intro a _
        exact (hasDerivAt_mul_const (x := a) _).differentiableAt.differentiableWithinAt
      · simp only [harmonicBiparameterCoefficient, ite_eq_right hw]
        exact differentiableOn_const _
    exact thm13_8_ahlfors_bers_holomorphic Metric.isOpen_ball
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      (fun t ht => hcoeff s t hs (mem_ball_zero_iff.mp ht)) hhol
      (fun t ht => hspec s t hs (mem_ball_zero_iff.mp ht)) z

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
