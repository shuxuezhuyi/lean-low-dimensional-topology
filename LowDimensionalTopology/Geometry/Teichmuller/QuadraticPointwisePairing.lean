module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicBeltrami
public import LowDimensionalTopology.Geometry.Teichmuller.NativePeterssonSpace
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# Pointwise Petersson pairing on the original surface

The height-weighted pairing of two original holomorphic quadratic differentials
is invariant under the actual uniformizing group. It therefore descends through
the given covering to a continuous scalar function on the original surface.
Its hyperbolic integral is the existing Petersson pairing. The first slot is
complex linear; the native Hilbert inner product consequently exchanges slots.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck} (p : ℍ → X)

/-- The literal inverse-fourth-density pointwise pairing on the upper half-plane. -/
def quadraticPointwiseLift
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) : ℂ :=
  ((z.im ^ 4 : ℝ) : ℂ) * liftQuadratic R.toRiemannAtlas p q z *
    conj (liftQuadratic R.toRiemannAtlas p r z)

/-- The pairing is the product of the two actual harmonic coefficients,
with conjugation in the first coefficient. -/
theorem quadraticPointwiseLift_eq_coefficients
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    quadraticPointwiseLift R p q r z =
      conj (NativeHarmonicBeltrami.coefficient R p q z) *
        NativeHarmonicBeltrami.coefficient R p r z := by
  simp only [quadraticPointwiseLift, NativeHarmonicBeltrami.coefficient, map_mul,
    map_pow, Complex.conj_ofReal, Complex.conj_conj, Complex.ofReal_pow]
  ring

variable
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

include hp in
/-- The unit-modulus deck phases cancel in the full pointwise pairing. -/
theorem quadraticPointwiseLift_invariant
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (γ : GammaMeasurableBeltrami.Deck) (hγ : γ ∈ Γ) (z : ℍ) :
    quadraticPointwiseLift R p q r (γ • z) = quadraticPointwiseLift R p q r z := by
  have hunit :
      conj (GammaMeasurableBeltrami.phase γ z) *
        GammaMeasurableBeltrami.phase γ z = 1 := by
    simp [Complex.conj_mul', GammaMeasurableBeltrami.norm_phase]
  rw [quadraticPointwiseLift_eq_coefficients, quadraticPointwiseLift_eq_coefficients,
    NativeHarmonicBeltrami.coefficient_compatible R p hp q γ hγ z,
    NativeHarmonicBeltrami.coefficient_compatible R p hp r γ hγ z]
  simp only [map_mul]
  calc
    _ = (conj (GammaMeasurableBeltrami.phase γ z) *
        GammaMeasurableBeltrami.phase γ z) *
        (conj (NativeHarmonicBeltrami.coefficient R p q (γ • z)) *
          NativeHarmonicBeltrami.coefficient R p r (γ • z)) := by rw [hunit, one_mul]
    _ = _ := by ring

include hp in
/-- Equality of original covering images gives equality of pointwise pairings. -/
theorem quadraticPointwiseLift_eq_of_fiber
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {z w : ℍ} (hzw : p z = p w) :
    quadraticPointwiseLift R p q r z = quadraticPointwiseLift R p q r w := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨γ, hγ, hγz⟩ := (hp.2.2.2 z w).mp hzw
  calc
    quadraticPointwiseLift R p q r z =
        quadraticPointwiseLift R p q r (γ • z) :=
      (quadraticPointwiseLift_invariant R p hp q r γ hγ z).symm
    _ = quadraticPointwiseLift R p q r w :=
      congrArg (quadraticPointwiseLift R p q r) hγz

/-- The actual scalar pairing on the original surface, using a covering preimage.
The evaluation theorem proves independence of that choice. -/
def quadraticPointwisePairing
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) : ℂ := by
  let := R.toRiemannAtlas.toChartedSpace
  exact quadraticPointwiseLift R p q r (Classical.choose (hp.2.2.1 x))

/-- Every covering preimage computes the same original-surface value. -/
theorem quadraticPointwisePairing_apply_cover
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    quadraticPointwisePairing R p hp q r (p z) = quadraticPointwiseLift R p q r z := by
  let := R.toRiemannAtlas.toChartedSpace
  change quadraticPointwiseLift R p q r (Classical.choose (hp.2.2.1 (p z))) = _
  exact quadraticPointwiseLift_eq_of_fiber R p hp q r
    (Classical.choose_spec (hp.2.2.1 (p z)))

/-- The descended pairing is continuous for the original surface topology. -/
theorem quadraticPointwisePairing_continuous
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    Continuous (quadraticPointwisePairing R p hp q r) := by
  let := R.toRiemannAtlas.toChartedSpace
  apply (hp.1.isQuotientMap hp.2.2.1).continuous_iff.mpr
  have hcomp : quadraticPointwisePairing R p hp q r ∘ p =
      quadraticPointwiseLift R p q r :=
    funext (quadraticPointwisePairing_apply_cover R p hp q r)
  rw [hcomp]
  exact (((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.pow 4)).mul
    (liftQuadratic_continuous R p hp q)).mul
      (Complex.continuous_conj.comp (liftQuadratic_continuous R p hp r)))

/-- The original-surface pairing is conjugate symmetric. -/
theorem quadraticPointwisePairing_conj
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) :
    conj (quadraticPointwisePairing R p hp q r x) =
      quadraticPointwisePairing R p hp r q x := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨z, rfl⟩ := hp.2.2.1 x
  rw [quadraticPointwisePairing_apply_cover, quadraticPointwisePairing_apply_cover]
  simp only [quadraticPointwiseLift, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- Additivity in the complex-linear first slot on the original surface. -/
theorem quadraticPointwisePairing_add_left
    (q r s : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) :
    quadraticPointwisePairing R p hp (q + r) s x =
      quadraticPointwisePairing R p hp q s x +
        quadraticPointwisePairing R p hp r s x := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨z, rfl⟩ := hp.2.2.1 x
  rw [quadraticPointwisePairing_apply_cover, quadraticPointwisePairing_apply_cover,
    quadraticPointwisePairing_apply_cover]
  simp only [quadraticPointwiseLift, map_add, Pi.add_apply, mul_add, add_mul]

/-- Additivity in the conjugate-linear second slot on the original surface. -/
theorem quadraticPointwisePairing_add_right
    (q r s : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) :
    quadraticPointwisePairing R p hp q (r + s) x =
      quadraticPointwisePairing R p hp q r x +
        quadraticPointwisePairing R p hp q s x := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨z, rfl⟩ := hp.2.2.1 x
  rw [quadraticPointwisePairing_apply_cover, quadraticPointwisePairing_apply_cover,
    quadraticPointwisePairing_apply_cover]
  simp only [quadraticPointwiseLift, map_add, Pi.add_apply, mul_add]

/-- Complex homogeneity in the first slot keeps the original scalar. -/
theorem quadraticPointwisePairing_smul_left (a : ℂ)
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) :
    quadraticPointwisePairing R p hp (a • q) r x =
      a * quadraticPointwisePairing R p hp q r x := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨z, rfl⟩ := hp.2.2.1 x
  rw [quadraticPointwisePairing_apply_cover, quadraticPointwisePairing_apply_cover]
  simp only [quadraticPointwiseLift, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Complex homogeneity in the second slot conjugates the original scalar. -/
theorem quadraticPointwisePairing_smul_right (a : ℂ)
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) :
    quadraticPointwisePairing R p hp q (a • r) x =
      conj a * quadraticPointwisePairing R p hp q r x := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨z, rfl⟩ := hp.2.2.1 x
  rw [quadraticPointwisePairing_apply_cover, quadraticPointwisePairing_apply_cover]
  simp only [quadraticPointwiseLift, map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/-- The diagonal is the literal nonnegative weighted square norm. -/
theorem quadraticPointwisePairing_self_apply_cover
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    quadraticPointwisePairing R p hp q q (p z) =
      ((z.im ^ 4 * ‖liftQuadratic R.toRiemannAtlas p q z‖ ^ 2 : ℝ) : ℂ) := by
  rw [quadraticPointwisePairing_apply_cover]
  simp only [quadraticPointwiseLift, mul_assoc, Complex.mul_conj',
    Complex.ofReal_mul, Complex.ofReal_pow]

/-- The diagonal has zero imaginary part at every original surface point. -/
theorem quadraticPointwisePairing_self_im
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) :
    (quadraticPointwisePairing R p hp q q x).im = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨z, rfl⟩ := hp.2.2.1 x
  rw [quadraticPointwisePairing_self_apply_cover]
  exact Complex.ofReal_im _

/-- The real diagonal is nonnegative on the entire original surface. -/
theorem quadraticPointwisePairing_self_nonneg
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) :
    0 ≤ (quadraticPointwisePairing R p hp q q x).re := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨z, rfl⟩ := hp.2.2.1 x
  rw [quadraticPointwisePairing_self_apply_cover, Complex.ofReal_re]
  exact mul_nonneg (pow_nonneg z.im_pos.le 4) (sq_nonneg _)

/-- The same native Petersson pairing integrates the descended original-surface
function against the actual hyperbolic area on every measurable region. -/
theorem nativeQuadraticPairing_eq_pointwiseIntegral
    (F : Set ℍ) (hF : MeasurableSet F)
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    nativeQuadraticPairing R.toRiemannAtlas p F q r =
      ∫ z in F, quadraticPointwisePairing R p hp q r (p z) ∂(volume : Measure ℍ) := by
  unfold nativeQuadraticPairing
  rw [quadraticPairing_eq_hyperbolicIntegral F hF]
  exact setIntegral_congr_fun hF fun z _ =>
    (quadraticPointwisePairing_apply_cover R p hp q r z).symm

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

open Surfaces WeilPetersson

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

/-- The genuine native Hilbert inner product integrates the same descended
pairing, exchanging the slots for Mathlib's conjugate-first convention. -/
theorem inner_eq_pointwiseIntegral (q r : Space R P p hp F hF) :
    inner ℂ q r =
      ∫ z in F, quadraticPointwisePairing R p hp
        (toQuadratic R P p hp F hF r) (toQuadratic R P p hp F hF q) (p z)
        ∂(volume : Measure ℍ) := by
  change nativeQuadraticPairing R.toRiemannAtlas p F
    (toQuadratic R P p hp F hF r) (toQuadratic R P p hp F hF q) = _
  exact nativeQuadraticPairing_eq_pointwiseIntegral R p hp F hF.1.measurableSet _ _

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
