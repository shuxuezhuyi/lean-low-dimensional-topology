module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergmanKernel
public import Mathlib.Tactic.FieldSimp

/-!
# Harmonic coefficients as genuine compatible L-infinity classes

The coefficient attached to an original-atlas global quadratic differential is
the literal function `y² * conj φ` on the uniformizing upper half-plane. Its
boundedness follows from compactness of the original surface; its deck law is
proved from the weight-four automorphic equation and the actual imaginary-part
transformation formula. No bound or compatibility is added as an assumption.

The class and planar representative interfaces are used by the integral map
from Beltrami coefficients to the Petersson continuous dual.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped ENNReal UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicBeltrami

open Surfaces QuadraticBergman
open GammaMeasurableBeltrami

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} (p : ℍ → X)

/-- The actual harmonic representative associated to the original quadratic differential. -/
def coefficient (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) : ℂ :=
  (z.im : ℂ) ^ 2 * conj (WeilPetersson.liftQuadratic R.toRiemannAtlas p q z)

theorem coefficient_eq_uniformized
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    coefficient R p q z =
      (z.im : ℂ) ^ 2 * conj (uniformizedQuadratic R p q (z : ℂ)) := rfl

theorem norm_coefficient (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ‖coefficient R p q z‖ = ‖uniformizedQuadratic R p q (z : ℂ)‖ * z.im ^ 2 := by
  rw [coefficient_eq_uniformized, norm_mul, norm_pow, Complex.norm_conj,
    Complex.norm_of_nonneg z.im_pos.le]
  ring

theorem coefficient_continuous
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    Continuous (coefficient R p q) :=
  ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow 2).mul
    (Complex.continuous_conj.comp (WeilPetersson.liftQuadratic_continuous R p hp q))

/-- The full harmonic coefficient, without a quasiconformal subunit restriction,
belongs to the actual hyperbolic L-infinity space. -/
theorem coefficient_memLp
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    MemLp (coefficient R p q) (⊤ : ℝ≥0∞) (volume : Measure ℍ) := by
  obtain ⟨M, _, hb⟩ := uniformizedQuadratic_weightedBound R p hp q
  apply memLp_top_of_bound (coefficient_continuous R p hp q).aestronglyMeasurable M
  exact Eventually.of_forall fun z => by
    rw [norm_coefficient]
    exact hb (z : ℂ) z.im_pos

/-- The harmonic coefficient satisfies the actual Beltrami tensor equation pointwise. -/
theorem coefficient_compatible
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (γ : Deck) (hγ : γ ∈ Γ) (z : ℍ) :
    coefficient R p q z = phase γ z * coefficient R p q (γ • z) := by
  have hd := denominator_ne_zero γ z
  have hcd : conj (denominator γ z) ≠ 0 := by
    intro h
    apply hd
    simpa only [Complex.conj_conj, map_zero] using congrArg conj h
  have hmob : ((γ • z : ℍ) : ℂ) =
      ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have ha := uniformizedQuadratic_automorphic R p hp q γ hγ (z : ℂ) z.im_pos
  rw [← hmob] at ha
  change uniformizedQuadratic R p q ((γ • z : ℍ) : ℂ) /
    denominator γ z ^ 4 = uniformizedQuadratic R p q (z : ℂ) at ha
  have hval := (div_eq_iff (pow_ne_zero 4 hd)).mp ha
  have him : (γ • z : ℍ).im = z.im / Complex.normSq (denominator γ z) := by
    simp [MulAction.compHom_smul_def, UpperHalfPlane.im_smul_eq_div_normSq,
      Matrix.SpecialLinearGroup.det_mapGL, UpperHalfPlane.denom, denominator]
  have himc : ((γ • z : ℍ).im : ℂ) =
      (z.im : ℂ) / (denominator γ z * conj (denominator γ z)) := by
    rw [Complex.mul_conj]
    exact_mod_cast him
  rw [coefficient_eq_uniformized, coefficient_eq_uniformized, phase, himc, hval]
  simp only [map_mul, map_pow]
  field_simp [hd, hcd]

/-- The genuine almost-everywhere class of the literal harmonic function. -/
def ambient
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) : Ambient :=
  (coefficient_memLp R p hp q).toLp (coefficient R p q)

theorem ambient_coe_ae
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ambient R p hp q =ᵐ[volume] coefficient R p q :=
  (coefficient_memLp R p hp q).coeFn_toLp

/-- The actual compatible Banach-space element used in Petersson-dual surjectivity. -/
def ofQuadratic
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) : Space Γ := by
  refine ⟨ambient R p hp q, ?_⟩
  change ambient R p hp q ∈ compatibleSubmodule Γ
  apply (mem_compatibleSubmodule_iff _).2
  intro γ hγ
  have hae := ambient_coe_ae R p hp q
  have hcomp := (measurePreserving_deck γ).quasiMeasurePreserving.ae_eq_comp hae
  filter_upwards [hae, hcomp] with z hz hγz
  change ambient R p hp q (γ • z) = coefficient R p q (γ • z) at hγz
  rw [hz, hγz]
  exact coefficient_compatible R p hp q γ hγ z

theorem ofQuadratic_coe_ae
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    (ofQuadratic R p hp q).val =ᵐ[volume] coefficient R p q :=
  ambient_coe_ae R p hp q

/-- The chosen planar representative is the same literal harmonic coefficient
almost everywhere for Euclidean area on the upper half-plane. -/
theorem planeRepresentative_ofQuadratic_ae
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    planeRepresentative (ofQuadratic R p hp q).val =ᵐ[volume.restrict LiZhongQC.upperHalf]
      fun z => (z.im : ℂ) ^ 2 * conj (uniformizedQuadratic R p q z) := by
  apply ae_plane_iff.mpr
  filter_upwards [ofQuadratic_coe_ae R p hp q] with z hz
  rw [planeRepresentative_coe, hz, coefficient_eq_uniformized, UpperHalfPlane.coe_im]

theorem coefficient_add (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    coefficient R p (q + r) = coefficient R p q + coefficient R p r := by
  funext z
  simp only [coefficient, map_add, Pi.add_apply, mul_add]

theorem coefficient_smul (a : ℂ) (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    coefficient R p (a • q) = conj a • coefficient R p q := by
  funext z
  simp only [coefficient, map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem ofQuadratic_add
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ofQuadratic R p hp (q + r) = ofQuadratic R p hp q + ofQuadratic R p hp r := by
  apply Subtype.ext
  rw [AddMemClass.coe_add (compatibleClosedSubmodule Γ)]
  apply Lp.ext
  filter_upwards [ofQuadratic_coe_ae R p hp (q + r), ofQuadratic_coe_ae R p hp q,
    ofQuadratic_coe_ae R p hp r,
    Lp.coeFn_add (ofQuadratic R p hp q).val (ofQuadratic R p hp r).val]
    with z hqr hq hr hadd
  simp only [Pi.add_apply] at hadd
  change (ofQuadratic R p hp (q + r)).val z =
    ((ofQuadratic R p hp q).val + (ofQuadratic R p hp r).val) z
  rw [hqr, hadd, hq, hr, coefficient_add, Pi.add_apply]

theorem ofQuadratic_smul
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (a : ℂ) (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ofQuadratic R p hp (a • q) = conj a • ofQuadratic R p hp q := by
  apply Subtype.ext
  rw [SetLike.val_smul (compatibleClosedSubmodule Γ)]
  apply Lp.ext
  filter_upwards [ofQuadratic_coe_ae R p hp (a • q), ofQuadratic_coe_ae R p hp q,
    Lp.coeFn_smul (conj a) (ofQuadratic R p hp q).val] with z haq hq hsmul
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  change (ofQuadratic R p hp (a • q)).val z = (conj a • (ofQuadratic R p hp q).val) z
  rw [haq, hsmul, hq, coefficient_smul, Pi.smul_apply, smul_eq_mul]

end LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicBeltrami
