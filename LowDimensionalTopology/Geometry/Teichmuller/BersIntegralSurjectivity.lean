module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicBeltrami
public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicDerivative

/-!
# Surjectivity of the literal Bers derivative onto the exact automorphic target

Reflection of a lower-half-plane form gives a holomorphic upper-half-plane
automorphic coefficient, hence an original-atlas quadratic differential.
The actual upper-half-plane reproducing integral sends its harmonic Beltrami
coefficient to minus one half the original lower form. Multiplication by minus
two therefore provides a genuine compatible L-infinity preimage. Every function
and the weighted target norm remain the ones already defined.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open Surfaces QuadraticBergman LiZhongQC

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)

/-- The literal Bers integral of a full harmonic class is minus one half the
reflected original quadratic coefficient. The exact factor comes from the
upper-half-plane reproducing coefficient, with no rank argument. -/
theorem bersDerivative_harmonic
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    bersDerivative (GammaMeasurableBeltrami.planeRepresentative
      (NativeHarmonicBeltrami.ofQuadratic R p hp q).val) z =
      -(1 / 2 : ℂ) * conj (uniformizedQuadratic R p q (conj z)) := by
  have hw : conj z ∈ upperHalf := by
    change 0 < (conj z).im
    rw [conj_im]
    exact neg_pos.mpr hz
  obtain ⟨_, hr⟩ := uniformizedQuadratic_reproducing R p hp q (conj z) hw
  have hk (ζ : ℂ) :
      conj ((ζ.im : ℂ) ^ 2 * uniformizedQuadratic R p q ζ /
        (conj ζ - conj z) ^ 4) =
        (ζ.im : ℂ) ^ 2 * conj (uniformizedQuadratic R p q ζ) / (ζ - z) ^ 4 := by
    simp only [map_div₀, map_mul, map_pow, Complex.conj_ofReal, map_sub, Complex.conj_conj]
  have he := congrArg conj hr
  have hc : conj (12 / Real.pi : ℂ) = (12 / Real.pi : ℂ) := by
    simp only [map_div₀, Complex.conj_ofReal, map_ofNat]
  rw [map_mul, ← integral_conj, hc] at he
  simp_rw [hk] at he
  rw [bersDerivative_congr_ae
    (NativeHarmonicBeltrami.planeRepresentative_ofQuadratic_ae R p hp q)]
  unfold bersDerivative
  rw [he]
  ring

/-- Reflection of the unchanged actual source function. -/
def reflectedUpper {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (φ : Automorphic Γ) (z : ℂ) : ℂ := conj ((φ.toSource : ℂ → ℂ) (conj z))

/-- Double conjugation preserves complex differentiability on the reflected domain. -/
theorem reflectedUpper_differentiableOn {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (φ : Automorphic Γ) : DifferentiableOn ℂ (reflectedUpper φ) upperHalf := by
  intro z hz
  have hz' : conj z ∈ lowerHalf := by
    change (conj z).im < 0
    rw [conj_im]
    exact neg_lt_zero.mpr hz
  have hd := (φ.toSource.property.1.differentiableAt
    (isOpen_lowerHalf.mem_nhds hz')).conj_conj
  rw [Complex.conj_conj] at hd
  exact hd.differentiableWithinAt

/-- The real matrix entries make reflection preserve every actual group equation. -/
theorem reflectedUpper_automorphic {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (φ : Automorphic Γ) :
    ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      reflectedUpper φ
          (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) /
        ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = reflectedUpper φ z := by
  intro γ hγ z hz
  have hz' : conj z ∈ lowerHalf := by
    change (conj z).im < 0
    rw [conj_im]
    exact neg_lt_zero.mpr hz
  have ha := φ.toSource.property.2.2 γ hγ (conj z) hz'
  simpa only [reflectedUpper, map_div₀, map_pow, map_add, map_mul,
    Complex.conj_ofReal, Complex.conj_conj] using congrArg conj ha

include hp in
/-- Every target form reflects to a genuine original-atlas differential on the
same given surface and the same uniformizing covering. -/
theorem exists_reflected_originalQuadratic (φ : Automorphic Γ) :
    ∃ q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
      ∀ z ∈ lowerHalf,
        conj (uniformizedQuadratic R p q (conj z)) = (φ.toSource : ℂ → ℂ) z := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨q, hq, he⟩ := utm_x_descent hp
    (reflectedUpper_differentiableOn φ) (reflectedUpper_automorphic φ)
  refine ⟨⟨q, hq⟩, fun z hz => ?_⟩
  have hw : conj z ∈ upperHalf := by
    change 0 < (conj z).im
    rw [conj_im]
    exact neg_pos.mpr hz
  have hv := congrArg conj (he (conj z) hw)
  simpa only [reflectedUpper, Complex.conj_conj, uniformizedQuadratic] using hv

include R p hp in
/-- The actual bounded Bers integral maps the entire compatible L-infinity
space onto the exact original lower-half-plane automorphic normed space. -/
theorem automorphicIntegralOperator_surjective (hΓ : IsFuchsian Γ) :
    Function.Surjective (automorphicIntegralOperator hΓ) := by
  intro φ
  obtain ⟨q, hq⟩ := exists_reflected_originalQuadratic R p hp φ
  let μ := NativeHarmonicBeltrami.ofQuadratic R p hp q
  refine ⟨(-2 : ℂ) • μ, ?_⟩
  apply Subtype.ext
  apply lp.ext
  funext z
  change integralOperator Γ ((-2 : ℂ) • μ) z = φ.val z
  rw [map_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  change (-2 : ℂ) * integralOperator Γ μ z = φ.val z
  rw [integralOperator_apply, bersDerivative_harmonic R p hp q z.property, hq z z.property]
  calc
    (-2 : ℂ) * (-(1 / 2 : ℂ) * (φ.toSource : ℂ → ℂ) z * weight z) =
        (φ.toSource : ℂ → ℂ) z * weight z := by ring
    _ = φ.val z := by
      rw [Automorphic.toSource_apply, decode_coe]
      exact div_mul_cancel₀ _ (weight_ne_zero z)

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
