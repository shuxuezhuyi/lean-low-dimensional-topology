module

public import LowDimensionalTopology.Geometry.Teichmuller.NativePeterssonSpace
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicBeltrami
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The literal Beltrami pairing into the actual Petersson continuous dual

The source uses its genuine compatible L-infinity class norm. The target uses
the operator norm for the full Petersson Hilbert norm. A finite-dimensional
continuous map into the actual L1 space supplies the bound for the bilinear
integral, without substituting a different norm on quadratic differentials.
Surjectivity is proved by the literal harmonic coefficient y² conjugate φ.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

open Surfaces WeilPetersson

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

local notation "Q" => Space R P p hp F hF
local notation "B" => GammaMeasurableBeltrami.Space Γ
local notation "mF" => flatArea.restrict F

/-- Each original coefficient has its actual L1 class on the full region. -/
def liftL1Linear : Q →ₗ[ℂ] Lp ℂ (1 : ℝ≥0∞) mF where
  toFun q := (liftQuadratic_integrableOn_fundamental R P p hp hF
    (toQuadratic R P p hp F hF q)).toL1 (lift R P p hp F hF q)
  map_add' q r := by
    simpa only [map_add] using Integrable.toL1_add
      (lift R P p hp F hF q) (lift R P p hp F hF r)
      (liftQuadratic_integrableOn_fundamental R P p hp hF q)
      (liftQuadratic_integrableOn_fundamental R P p hp hF r)
  map_smul' a q := by
    simpa only [map_smul, RingHom.id_apply] using Integrable.toL1_smul'
      (lift R P p hp F hF q)
      (liftQuadratic_integrableOn_fundamental R P p hp hF q) a

/-- Continuity refers to the precise full Petersson norm in the domain. -/
def liftL1 : Q →L[ℂ] Lp ℂ (1 : ℝ≥0∞) mF :=
  (liftL1Linear R P p hp F hF).toContinuousLinearMap

/-- The L1 target has its actual integral norm. -/
theorem norm_liftL1 (q : Q) :
    ‖liftL1 R P p hp F hF q‖ = ∫ z in F, ‖lift R P p hp F hF q z‖ ∂flatArea := by
  have hq : Integrable (lift R P p hp F hF q) mF :=
    liftQuadratic_integrableOn_fundamental R P p hp hF
      (toQuadratic R P p hp F hF q)
  rw [integral_norm_eq_lintegral_enorm hq.aestronglyMeasurable]
  exact Integrable.norm_toL1_eq_lintegral_enorm (lift R P p hp F hF q) hq

/-- The class's own norm bounds its representative for the actual flat area. -/
theorem coefficient_norm_ae (μ : B) : ∀ᵐ z : ℍ ∂flatArea, ‖μ.val z‖ ≤ ‖μ‖ := by
  filter_upwards [GammaMeasurableBeltrami.ae_hyperbolic_iff.mp
    (lpInfinity_norm_ae_le μ.val)] with z hz
  simpa only [ClosedSubmodule.norm_coe μ] using hz

/-- Absolute integrability of the full literal coefficient pairing. -/
theorem pairing_integrable (μ : B) (q : Q) :
    IntegrableOn (fun z : ℍ => μ.val z * lift R P p hp F hF q z) F flatArea := by
  have hμ : AEStronglyMeasurable (μ.val : ℍ → ℂ) mF :=
    ((Lp.aestronglyMeasurable μ.val).mono_ac
      GammaMeasurableBeltrami.flat_absolutelyContinuous_hyperbolic).restrict
  exact (liftQuadratic_integrableOn_fundamental R P p hp hF q).bdd_mul hμ
    (ae_restrict_of_ae (coefficient_norm_ae μ))

/-- The exact pairing of a genuine Beltrami class with an original differential. -/
def pairing (μ : B) (q : Q) : ℂ :=
  ∫ z in F, μ.val z * lift R P p hp F hF q z ∂flatArea

/-- The integral is bounded by the actual class norm times the literal L1 integral. -/
theorem norm_pairing_le (μ : B) (q : Q) :
    ‖pairing R P p hp F hF μ q‖ ≤
      ‖μ‖ * ∫ z in F, ‖lift R P p hp F hF q z‖ ∂flatArea := by
  unfold pairing
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le
    ((liftQuadratic_integrableOn_fundamental R P p hp hF q).norm.const_mul ‖μ‖) ?_
  filter_upwards [ae_restrict_of_ae (coefficient_norm_ae μ)] with z hz
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

/-- Linearity in the quadratic argument is proved from actual integrability. -/
def pairingLinear (μ : B) : Q →ₗ[ℂ] ℂ where
  toFun := pairing R P p hp F hF μ
  map_add' q r := by
    unfold pairing
    simp only [map_add, Pi.add_apply, mul_add]
    exact integral_add (pairing_integrable R P p hp F hF μ q)
      (pairing_integrable R P p hp F hF μ r)
  map_smul' a q := by
    unfold pairing
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      (∫ z in F, μ.val z * (a * lift R P p hp F hF q z) ∂flatArea) =
          ∫ z in F, a * (μ.val z * lift R P p hp F hF q z) ∂flatArea := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by ring
      _ = _ := integral_const_mul a _

/-- A genuine bounded linear functional on the full Petersson Hilbert space. -/
def functional (μ : B) : StrongDual ℂ Q :=
  (pairingLinear R P p hp F hF μ).toContinuousLinearMap

@[simp] theorem functional_apply (μ : B) (q : Q) :
    functional R P p hp F hF μ q = pairing R P p hp F hF μ q := rfl

/-- Linearity in the Beltrami argument respects almost-everywhere representatives. -/
def pairingMapLinear : B →ₗ[ℂ] StrongDual ℂ Q where
  toFun := functional R P p hp F hF
  map_add' μ ν := by
    apply ContinuousLinearMap.ext
    intro q
    simp only [add_apply, functional_apply]
    change pairing R P p hp F hF (μ + ν) q =
      pairing R P p hp F hF μ q + pairing R P p hp F hF ν q
    unfold pairing
    rw [AddMemClass.coe_add (GammaMeasurableBeltrami.compatibleClosedSubmodule Γ)]
    rw [← integral_add (pairing_integrable R P p hp F hF μ q)
      (pairing_integrable R P p hp F hF ν q)]
    apply integral_congr_ae
    have ha := GammaMeasurableBeltrami.ae_hyperbolic_iff.mp (Lp.coeFn_add μ.val ν.val)
    filter_upwards [ae_restrict_of_ae ha] with z hz
    simp only [Pi.add_apply] at hz
    change (μ.val + ν.val) z * _ = _
    rw [hz, add_mul]
  map_smul' a μ := by
    apply ContinuousLinearMap.ext
    intro q
    simp only [smul_apply, functional_apply, RingHom.id_apply, smul_eq_mul]
    change pairing R P p hp F hF (a • μ) q = a * pairing R P p hp F hF μ q
    unfold pairing
    rw [SetLike.val_smul (GammaMeasurableBeltrami.compatibleClosedSubmodule Γ)]
    rw [← integral_const_mul]
    apply integral_congr_ae
    have ha := GammaMeasurableBeltrami.ae_hyperbolic_iff.mp (Lp.coeFn_smul a μ.val)
    filter_upwards [ae_restrict_of_ae ha] with z hz
    simp only [Pi.smul_apply, smul_eq_mul] at hz
    change (a • μ.val) z * _ = _
    rw [hz, mul_assoc]

/-- The continuous-dual operator norm is controlled in the actual Petersson norm. -/
theorem norm_functional_le (μ : B) :
    ‖functional R P p hp F hF μ‖ ≤ ‖liftL1 R P p hp F hF‖ * ‖μ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro q
  change ‖pairing R P p hp F hF μ q‖ ≤ _
  calc
    ‖pairing R P p hp F hF μ q‖ ≤
        ‖μ‖ * ∫ z in F, ‖lift R P p hp F hF q z‖ ∂flatArea :=
      norm_pairing_le R P p hp F hF μ q
    _ = ‖μ‖ * ‖liftL1 R P p hp F hF q‖ := by rw [norm_liftL1]
    _ ≤ ‖μ‖ * (‖liftL1 R P p hp F hF‖ * ‖q‖) :=
      mul_le_mul_of_nonneg_left ((liftL1 R P p hp F hF).le_opNorm q) (norm_nonneg _)
    _ = (‖liftL1 R P p hp F hF‖ * ‖μ‖) * ‖q‖ := by ring

/-- The book's actual pairing map between the genuine normed spaces. -/
def pairingMap : B →L[ℂ] StrongDual ℂ Q :=
  (pairingMapLinear R P p hp F hF).mkContinuous ‖liftL1 R P p hp F hF‖
    (norm_functional_le R P p hp F hF)

@[simp] theorem pairingMap_apply (μ : B) (q : Q) :
    pairingMap R P p hp F hF μ q = pairing R P p hp F hF μ q := rfl

/-- The literal harmonic Beltrami class realizes precisely the Riesz functional. -/
theorem pairing_harmonic (q r : Q) :
    pairing R P p hp F hF
      (NativeHarmonicBeltrami.ofQuadratic R p hp (toQuadratic R P p hp F hF q)) r =
      inner ℂ q r := by
  rw [inner_eq_integral]
  unfold pairing
  apply integral_congr_ae
  have hae := GammaMeasurableBeltrami.ae_hyperbolic_iff.mp
    (NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp
      (toQuadratic R P p hp F hF q))
  filter_upwards [ae_restrict_of_ae hae] with z hz
  rw [hz]
  change (z.im : ℂ) ^ 2 * conj (lift R P p hp F hF q z) *
      lift R P p hp F hF r z =
    ((z.im ^ 2 : ℝ) : ℂ) * lift R P p hp F hF r z *
      conj (lift R P p hp F hF q z)
  rw [Complex.ofReal_pow]
  ring

/-- Surjectivity uses all original differentials and their actual harmonic classes. -/
theorem pairingMap_surjective : Function.Surjective (pairingMap R P p hp F hF) := by
  intro f
  let q : Q := (InnerProductSpace.toDual ℂ Q).symm f
  refine ⟨NativeHarmonicBeltrami.ofQuadratic R p hp (toQuadratic R P p hp F hF q), ?_⟩
  apply ContinuousLinearMap.ext
  intro r
  rw [pairingMap_apply, pairing_harmonic]
  exact InnerProductSpace.toDual_symm_apply

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
