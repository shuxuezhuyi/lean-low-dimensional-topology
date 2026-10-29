module

public import LowDimensionalTopology.Geometry.Teichmuller.BersPeterssonDuality
public import LowDimensionalTopology.Geometry.Teichmuller.BersIntegralSurjectivity
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The literal bounded harmonic projection in the original Beltrami norm

Riesz representation uses the full Petersson norm on all original quadratic
vectors. The harmonic coefficient map is conjugate linear, as is the inverse
Riesz map; their composition is complex linear. Its boundedness uses the real
finite dimensional continuity of the literal harmonic map, without changing
the Petersson norm or the original compatible L-infinity norm. The resulting
projection preserves the actual Bers integral and has its exact kernel.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

open Surfaces QuadraticBergman

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

local notation "Q" => Space R P p hp F hF
local notation "B" => GammaMeasurableBeltrami.Space Γ

/-- The unique full Petersson vector representing the literal pairing. -/
def rieszQuadratic (μ : B) : Q :=
  (InnerProductSpace.toDual ℂ Q).symm (pairingMap R P p hp F hF μ)

theorem rieszQuadratic_add (μ ν : B) :
    rieszQuadratic R P p hp F hF (μ + ν) =
      rieszQuadratic R P p hp F hF μ + rieszQuadratic R P p hp F hF ν := by
  simp only [rieszQuadratic, map_add]

theorem rieszQuadratic_smul (a : ℂ) (μ : B) :
    rieszQuadratic R P p hp F hF (a • μ) =
      conj a • rieszQuadratic R P p hp F hF μ := by
  simp only [rieszQuadratic, map_smul, LinearIsometryEquiv.map_smulₛₗ]

/-- Riesz representation preserves the actual full Petersson and dual norms. -/
theorem norm_rieszQuadratic (μ : B) :
    ‖rieszQuadratic R P p hp F hF μ‖ = ‖pairingMap R P p hp F hF μ‖ :=
  (InnerProductSpace.toDual ℂ Q).symm.norm_map _

section RealHarmonicMap

local instance : NormedSpace ℝ Q := NormedSpace.restrictScalars ℝ ℂ Q
local instance : NormedSpace ℝ B := NormedSpace.restrictScalars ℝ ℂ B
local instance : IsScalarTower ℝ ℂ Q := IsScalarTower.restrictScalars ℝ ℂ Q
local instance : FiniteDimensional ℝ Q := FiniteDimensional.trans ℝ ℂ Q

/-- The literal harmonic map, viewed over the real scalars only for continuity. -/
def harmonicLiftRealLinear : Q →ₗ[ℝ] B where
  toFun q := NativeHarmonicBeltrami.ofQuadratic R p hp (toQuadratic R P p hp F hF q)
  map_add' q r := by
    rw [map_add, NativeHarmonicBeltrami.ofQuadratic_add]
  map_smul' a q := by
    simp only [RingHom.id_apply]
    change NativeHarmonicBeltrami.ofQuadratic R p hp
        (toQuadratic R P p hp F hF ((a : ℂ) • q)) =
      (a : ℂ) • NativeHarmonicBeltrami.ofQuadratic R p hp (toQuadratic R P p hp F hF q)
    rw [map_smul, NativeHarmonicBeltrami.ofQuadratic_smul, Complex.conj_ofReal]

/-- The real continuous map has the unchanged original source and target norms. -/
def harmonicLift : Q →L[ℝ] B :=
  (harmonicLiftRealLinear R P p hp F hF).toContinuousLinearMap

@[simp] theorem harmonicLift_apply (q : Q) :
    harmonicLift R P p hp F hF q =
      NativeHarmonicBeltrami.ofQuadratic R p hp (toQuadratic R P p hp F hF q) := by
  simp only [harmonicLift, LinearMap.coe_toContinuousLinearMap', harmonicLiftRealLinear,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- The genuine harmonic map is conjugate linear over the complex scalars. -/
theorem harmonicLift_complex_smul (a : ℂ) (q : Q) :
    harmonicLift R P p hp F hF (a • q) = conj a • harmonicLift R P p hp F hF q := by
  rw [harmonicLift_apply, map_smul, NativeHarmonicBeltrami.ofQuadratic_smul,
    harmonicLift_apply]

/-- The two conjugate-linear operations produce the actual complex-linear projection. -/
def harmonicProjectionLinear : B →ₗ[ℂ] B where
  toFun μ := harmonicLift R P p hp F hF (rieszQuadratic R P p hp F hF μ)
  map_add' μ ν := by rw [rieszQuadratic_add, map_add]
  map_smul' a μ := by
    simp only [RingHom.id_apply]
    rw [rieszQuadratic_smul, harmonicLift_complex_smul, Complex.conj_conj]

/-- A bound in the actual Petersson and compatible L-infinity norms. -/
theorem norm_harmonicProjectionLinear_le (μ : B) :
    ‖harmonicProjectionLinear R P p hp F hF μ‖ ≤
      (‖harmonicLift R P p hp F hF‖ * ‖pairingMap R P p hp F hF‖) * ‖μ‖ := by
  change ‖harmonicLift R P p hp F hF (rieszQuadratic R P p hp F hF μ)‖ ≤ _
  calc
    _ ≤ ‖harmonicLift R P p hp F hF‖ * ‖rieszQuadratic R P p hp F hF μ‖ :=
      (harmonicLift R P p hp F hF).le_opNorm _
    _ = ‖harmonicLift R P p hp F hF‖ * ‖pairingMap R P p hp F hF μ‖ := by
      rw [norm_rieszQuadratic]
    _ ≤ ‖harmonicLift R P p hp F hF‖ * (‖pairingMap R P p hp F hF‖ * ‖μ‖) :=
      mul_le_mul_of_nonneg_left ((pairingMap R P p hp F hF).le_opNorm μ)
        (ContinuousLinearMap.opNorm_nonneg (harmonicLift R P p hp F hF))
    _ = _ := by ring

/-- The literal harmonic projection, bounded in the original compatible L-infinity norm. -/
def harmonicProjection : B →L[ℂ] B :=
  (harmonicProjectionLinear R P p hp F hF).mkContinuous
    (‖harmonicLift R P p hp F hF‖ * ‖pairingMap R P p hp F hF‖)
    (norm_harmonicProjectionLinear_le R P p hp F hF)

@[simp] theorem harmonicProjection_apply (μ : B) :
    harmonicProjection R P p hp F hF μ =
      NativeHarmonicBeltrami.ofQuadratic R p hp
        (toQuadratic R P p hp F hF (rieszQuadratic R P p hp F hF μ)) := by
  simp only [harmonicProjection, LinearMap.mkContinuous_apply,
    harmonicProjectionLinear, LinearMap.coe_mk, AddHom.coe_mk, harmonicLift_apply]

end RealHarmonicMap

/-- The projection retains the complete literal pairing functional. -/
theorem pairingMap_harmonicProjection (μ : B) :
    pairingMap R P p hp F hF (harmonicProjection R P p hp F hF μ) =
      pairingMap R P p hp F hF μ := by
  apply ContinuousLinearMap.ext
  intro q
  rw [pairingMap_apply, harmonicProjection_apply, pairing_harmonic]
  exact InnerProductSpace.toDual_symm_apply

/-- Every literal harmonic coefficient corresponds to its original full Petersson vector. -/
theorem rieszQuadratic_ofQuadratic (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    rieszQuadratic R P p hp F hF (NativeHarmonicBeltrami.ofQuadratic R p hp q) =
      (toQuadratic R P p hp F hF).symm q := by
  apply ext_inner_right ℂ
  intro r
  rw [rieszQuadratic, InnerProductSpace.toDual_symm_apply, pairingMap_apply]
  have he := pairing_harmonic R P p hp F hF ((toQuadratic R P p hp F hF).symm q) r
  rw [LinearEquiv.apply_symm_apply] at he
  exact he

/-- The projection fixes every original harmonic Beltrami class. -/
theorem harmonicProjection_fixes_ofQuadratic
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    harmonicProjection R P p hp F hF (NativeHarmonicBeltrami.ofQuadratic R p hp q) =
      NativeHarmonicBeltrami.ofQuadratic R p hp q := by
  rw [harmonicProjection_apply, rieszQuadratic_ofQuadratic, LinearEquiv.apply_symm_apply]

/-- The literal harmonic projection is idempotent. -/
theorem harmonicProjection_idempotent (μ : B) :
    harmonicProjection R P p hp F hF (harmonicProjection R P p hp F hF μ) =
      harmonicProjection R P p hp F hF μ := by
  conv_lhs => rw [harmonicProjection_apply R P p hp F hF μ]
  rw [harmonicProjection_fixes_ofQuadratic, ← harmonicProjection_apply]

/-- The full quadratic vector is unchanged by harmonic projection. -/
theorem rieszQuadratic_harmonicProjection (μ : B) :
    rieszQuadratic R P p hp F hF (harmonicProjection R P p hp F hF μ) =
      rieszQuadratic R P p hp F hF μ := by
  unfold rieszQuadratic
  rw [pairingMap_harmonicProjection]

/-- The projection kernel is exactly the actual Bers infinitesimal kernel. -/
theorem harmonicProjection_ker :
    (harmonicProjection R P p hp F hF).ker = infinitesimalSubmodule Γ := by
  rw [← pairingMap_ker R P p hp F hF]
  apply Submodule.ext
  intro μ
  change harmonicProjection R P p hp F hF μ = 0 ↔ pairingMap R P p hp F hF μ = 0
  constructor
  · intro hμ
    have he := pairingMap_harmonicProjection R P p hp F hF μ
    rw [hμ, map_zero] at he
    exact he.symm
  · intro hμ
    rw [harmonicProjection_apply]
    have hq : rieszQuadratic R P p hp F hF μ = 0 := by
      simp only [rieszQuadratic, hμ, map_zero]
    rw [hq, map_zero]
    have hz := NativeHarmonicBeltrami.ofQuadratic_smul R p hp (0 : ℂ)
      (0 : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    simpa only [zero_smul, map_zero] using hz

/-- Harmonic projection preserves the literal bounded Bers integral. -/
theorem harmonicProjection_bers (μ : B) :
    BersWeighted.integralOperator Γ (harmonicProjection R P p hp F hF μ) =
      BersWeighted.integralOperator Γ μ := by
  have hn : μ - harmonicProjection R P p hp F hF μ ∈ infinitesimalSubmodule Γ := by
    rw [← pairingMap_ker R P p hp F hF]
    change pairingMap R P p hp F hF (μ - harmonicProjection R P p hp F hF μ) = 0
    rw [map_sub, pairingMap_harmonicProjection, sub_self]
  change BersWeighted.integralOperator Γ (μ - harmonicProjection R P p hp F hF μ) = 0 at hn
  rw [map_sub, sub_eq_zero] at hn
  exact hn.symm

/-- The full Riesz vector has precisely the book's reflected Bers coefficient. -/
theorem uniformized_rieszQuadratic_eq_bersDerivative (μ : B) {z : ℂ}
    (hz : z ∈ LiZhongQC.upperHalf) :
    uniformizedQuadratic R p (toQuadratic R P p hp F hF
      (rieszQuadratic R P p hp F hF μ)) z =
      -2 * conj (LiZhongQC.bersDerivative
        (GammaMeasurableBeltrami.planeRepresentative μ.val) (conj z)) := by
  have hw : conj z ∈ LiZhongQC.lowerHalf := by
    change (conj z).im < 0
    rw [Complex.conj_im]
    exact neg_lt_zero.mpr hz
  have he := congrArg (fun f : BersWeighted.Target => f ⟨conj z, hw⟩)
    (harmonicProjection_bers R P p hp F hF μ)
  simp only [BersWeighted.integralOperator_apply] at he
  have hd := mul_right_cancel₀ (BersWeighted.weight_ne_zero ⟨conj z, hw⟩) he
  have hh := BersWeighted.bersDerivative_harmonic R p hp
    (toQuadratic R P p hp F hF (rieszQuadratic R P p hp F hF μ)) hw
  rw [← harmonicProjection_apply R P p hp F hF μ, hd, Complex.conj_conj] at hh
  have hc := congrArg conj hh
  simp only [map_mul, map_neg, map_div₀, map_one, map_ofNat, Complex.conj_conj] at hc
  calc
    _ = (-2 : ℂ) * (-(1 / 2 : ℂ) * uniformizedQuadratic R p
        (toQuadratic R P p hp F hF (rieszQuadratic R P p hp F hF μ)) z) := by ring
    _ = _ := by rw [← hc]

/-- The actual planar representative satisfies the literal harmonic Bers formula almost everywhere. -/
theorem planeRepresentative_harmonicProjection_ae (μ : B) :
    GammaMeasurableBeltrami.planeRepresentative
        (harmonicProjection R P p hp F hF μ).val =ᵐ[volume.restrict LiZhongQC.upperHalf]
      fun z => -2 * (z.im : ℂ) ^ 2 * LiZhongQC.bersDerivative
        (GammaMeasurableBeltrami.planeRepresentative μ.val) (conj z) := by
  rw [harmonicProjection_apply]
  filter_upwards [NativeHarmonicBeltrami.planeRepresentative_ofQuadratic_ae R p hp
    (toQuadratic R P p hp F hF (rieszQuadratic R P p hp F hF μ)),
    ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with z he hz
  rw [he, uniformized_rieszQuadratic_eq_bersDerivative R P p hp F hF μ hz]
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_conj]
  ring

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
