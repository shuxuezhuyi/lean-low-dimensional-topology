module
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicDecomposition

/-!
# The original Hermitian integral and the actual harmonic projection

The coefficient directions range over the entire compatible L-infinity space.
The literal inverse-square-height integral and original quadratic pairing are
retained. Actual harmonic representatives identify the second slot with the
full Petersson functional; its proved projection invariance and conjugate
symmetry give both slots, with the reflected Bers normalization unchanged.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

open Surfaces WeilPetersson

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

local notation "B" => GammaMeasurableBeltrami.Space Γ
local notation "Q" => Space R P p hp F hF

private theorem harmonic_right_integrand_ae (μ : B) (q : Q) :
    (fun z : ℍ => (((z.im ^ 2)⁻¹ : ℝ) : ℂ) * μ.val z *
      conj ((NativeHarmonicBeltrami.ofQuadratic R p hp
        (toQuadratic R P p hp F hF q)).val z)) =ᵐ[flatArea.restrict F]
      fun z => μ.val z * lift R P p hp F hF q z := by
  have hq := GammaMeasurableBeltrami.ae_hyperbolic_iff.mp
    (NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp
      (toQuadratic R P p hp F hF q))
  filter_upwards [ae_restrict_of_ae hq] with z hz
  rw [hz]
  simp only [NativeHarmonicBeltrami.coefficient, map_mul, map_pow,
    Complex.conj_ofReal, Complex.conj_conj, Complex.ofReal_inv, Complex.ofReal_pow]
  change ((z.im : ℂ) ^ 2)⁻¹ * μ.val z *
      ((z.im : ℂ) ^ 2 * lift R P p hp F hF q z) =
    μ.val z * lift R P p hp F hF q z
  have hy : (z.im : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr z.im_ne_zero)
  calc
    ((z.im : ℂ) ^ 2)⁻¹ * μ.val z *
        ((z.im : ℂ) ^ 2 * lift R P p hp F hF q z) =
      (((z.im : ℂ) ^ 2)⁻¹ * (z.im : ℂ) ^ 2) *
        (μ.val z * lift R P p hp F hF q z) := by ring
    _ = μ.val z * lift R P p hp F hF q z := by
      rw [inv_mul_cancel₀ hy, one_mul]

private theorem harmonic_right_integrable (μ : B) (q : Q) :
    IntegrableOn (fun z : ℍ => (((z.im ^ 2)⁻¹ : ℝ) : ℂ) * μ.val z *
      conj ((NativeHarmonicBeltrami.ofQuadratic R p hp
        (toQuadratic R P p hp F hF q)).val z)) F flatArea := by
  exact (pairing_integrable R P p hp F hF μ q).congr_fun_ae
    (Filter.EventuallyEq.symm (harmonic_right_integrand_ae R P p hp F hF μ q))

private theorem beltramiPairing_ofQuadratic_right (μ : B) (q : Q) :
    WeilPetersson.beltramiPairing F μ.val
        (NativeHarmonicBeltrami.ofQuadratic R p hp
          (toQuadratic R P p hp F hF q)).val =
      pairing R P p hp F hF μ q := by
  unfold WeilPetersson.beltramiPairing WeilPetersson.weightedPairing pairing
  exact integral_congr_ae (harmonic_right_integrand_ae R P p hp F hF μ q)

local notation "H" => harmonicProjection R P p hp F hF

/-- Every mixed integral with an actual harmonic second slot converges
absolutely, for every original bounded compatible coefficient. -/
theorem harmonicProjection_hermitian_integrable_right (μ ν : B) :
    IntegrableOn (fun z : ℍ => (((z.im ^ 2)⁻¹ : ℝ) : ℂ) * μ.val z *
      conj ((H ν).val z)) F flatArea := by
  rw [harmonicProjection_apply]
  exact harmonic_right_integrable R P p hp F hF μ
    (rieszQuadratic R P p hp F hF ν)

/-- The corresponding mixed integral with a harmonic first slot also
converges absolutely in the same original area measure. -/
theorem harmonicProjection_hermitian_integrable_left (μ ν : B) :
    IntegrableOn (fun z : ℍ => (((z.im ^ 2)⁻¹ : ℝ) : ℂ) * (H μ).val z *
      conj (ν.val z)) F flatArea := by
  have hi : IntegrableOn
      (fun z : ℍ => conj ((((z.im ^ 2)⁻¹ : ℝ) : ℂ) * ν.val z *
        conj ((H μ).val z))) F flatArea :=
    (Complex.conjCLE.integrable_comp_iff).mpr
      (harmonicProjection_hermitian_integrable_right R P p hp F hF ν μ)
  apply hi.congr_fun_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring

/-- The actual mixed Hermitian integral is the original quadratic pairing. -/
theorem beltramiPairing_harmonicProjection_right (μ ν : B) :
    beltramiPairing F μ.val (H ν).val =
      pairing R P p hp F hF μ (rieszQuadratic R P p hp F hF ν) := by
  rw [harmonicProjection_apply]
  exact beltramiPairing_ofQuadratic_right R P p hp F hF μ
    (rieszQuadratic R P p hp F hF ν)

private theorem beltramiPairing_harmonicProjection_both_eq_right (μ ν : B) :
    beltramiPairing F (H μ).val (H ν).val =
      beltramiPairing F μ.val (H ν).val := by
  have h := congrArg
    (fun f : StrongDual ℂ (Space R P p hp F hF) =>
      f (rieszQuadratic R P p hp F hF ν))
    (pairingMap_harmonicProjection R P p hp F hF μ)
  change pairing R P p hp F hF (H μ) (rieszQuadratic R P p hp F hF ν) =
    pairing R P p hp F hF μ (rieszQuadratic R P p hp F hF ν) at h
  exact (beltramiPairing_harmonicProjection_right R P p hp F hF (H μ) ν).trans
    (h.trans (beltramiPairing_harmonicProjection_right R P p hp F hF μ ν).symm)

/-- Both slots of the literal Hermitian integral are compatible with the
actual harmonic projection, including both original mixed quadratic pairings.
The coefficient directions range over the full compatible L-infinity space. -/
theorem harmonicProjection_hermitian_compatibility (μ ν : B) :
    beltramiPairing F (H μ).val (H ν).val =
        beltramiPairing F (H μ).val ν.val ∧
      beltramiPairing F (H μ).val (H ν).val =
        beltramiPairing F μ.val (H ν).val ∧
      beltramiPairing F (H μ).val (H ν).val =
        pairing R P p hp F hF (H μ) (rieszQuadratic R P p hp F hF ν) ∧
      beltramiPairing F (H μ).val (H ν).val =
        pairing R P p hp F hF μ (rieszQuadratic R P p hp F hF ν) := by
  have hr := beltramiPairing_harmonicProjection_both_eq_right R P p hp F hF μ ν
  have hl := congrArg conj
    (beltramiPairing_harmonicProjection_both_eq_right R P p hp F hF ν μ)
  simp only [beltramiPairing_conj] at hl
  exact ⟨hl, hr,
    beltramiPairing_harmonicProjection_right R P p hp F hF (H μ) ν,
    hr.trans (beltramiPairing_harmonicProjection_right R P p hp F hF μ ν)⟩

/-- The quadratic coefficient in the pairing is the literal reflected Bers
derivative with the original factor minus two. -/
theorem pairing_rieszQuadratic_eq_reflected_integral (μ ν : B) :
    pairing R P p hp F hF μ (rieszQuadratic R P p hp F hF ν) =
      ∫ z in UpperHalfPlane.coe '' F,
        GammaMeasurableBeltrami.planeRepresentative μ.val z *
          (-2 * conj (LiZhongQC.bersDerivative
            (GammaMeasurableBeltrami.planeRepresentative ν.val) (conj z))) := by
  rw [pairing_eq_planar]
  apply setIntegral_congr_fun
    ((UpperHalfPlane.isOpenEmbedding_coe.isOpenMap F hF.1).measurableSet)
  rintro z ⟨w, hw, rfl⟩
  dsimp only
  rw [uniformized_rieszQuadratic_eq_bersDerivative R P p hp F hF ν w.im_pos]

/-- The full two-slot compatibility formula in the original planar
normalization, with the actual projected coefficients and reflected quadratic
coefficient. Neither direction is restricted to a subunit ball. -/
theorem harmonicProjection_hermitian_compatibility_planar (μ ν : B) :
    beltramiPairing F (H μ).val (H ν).val =
        beltramiPairing F (H μ).val ν.val ∧
      beltramiPairing F (H μ).val (H ν).val =
        beltramiPairing F μ.val (H ν).val ∧
      beltramiPairing F (H μ).val (H ν).val =
        (∫ z in UpperHalfPlane.coe '' F,
          GammaMeasurableBeltrami.planeRepresentative (H μ).val z *
            (-2 * conj (LiZhongQC.bersDerivative
              (GammaMeasurableBeltrami.planeRepresentative ν.val) (conj z)))) ∧
      beltramiPairing F (H μ).val (H ν).val =
        (∫ z in UpperHalfPlane.coe '' F,
          GammaMeasurableBeltrami.planeRepresentative μ.val z *
            (-2 * conj (LiZhongQC.bersDerivative
              (GammaMeasurableBeltrami.planeRepresentative ν.val) (conj z)))) := by
  obtain ⟨hl, hr, hq, hraw⟩ :=
    harmonicProjection_hermitian_compatibility R P p hp F hF μ ν
  exact ⟨hl, hr,
    hq.trans (pairing_rieszQuadratic_eq_reflected_integral R P p hp F hF (H μ) ν),
    hraw.trans (pairing_rieszQuadratic_eq_reflected_integral R P p hp F hF μ ν)⟩

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
