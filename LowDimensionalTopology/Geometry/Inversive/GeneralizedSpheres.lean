/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.ReflectionConjugacy

/-!
# Generalized spheres and inversive products

The spheres are actual subsets of the existing one-point compactification.
Nonzero quadratic representatives are proved unique up to a nonzero scalar,
and the inversive product descends to these geometric subsets. Reflection
conjugacy transports generalized spheres and inverse pairs, including infinity.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint RealInnerProductSpace
open Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

/-- A Euclidean sphere as a subset of the fixed extended-space carrier. -/
def extendedSphere (c : Euclidean n) (r : ℝ) : Set (ExtendedEuclidean n) :=
  ((↑) : Euclidean n → ExtendedEuclidean n) '' sphere c r

/-- generalized spheres include positive-radius Euclidean spheres and genuine extended planes. -/
def IsGeneralizedSphere (S : Set (ExtendedEuclidean n)) : Prop :=
  (∃ c : Euclidean n, ∃ r : ℝ, 0 < r ∧ S = extendedSphere c r) ∨
    (∃ a : Euclidean n, ∃ t : ℝ, a ≠ 0 ∧ S = plane a t)

/-- The reflecting sphere is exactly the complete fixed-point set of its reflection. -/
theorem fixedPoints_sphereInversion (c : Euclidean n) (r : ℝ) (hr : 0 < r) :
    Function.fixedPoints (sphereInversionHomeomorph c r hr.ne') = extendedSphere c r := by
  ext z
  exact (sphereInversion_fixed_iff c hr z)

/-- The reflecting plane, including infinity, is exactly the complete fixed-point set. -/
theorem fixedPoints_planeReflection (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    Function.fixedPoints (planeReflectionHomeomorph a t ha) = plane a t := by
  ext z
  change planeReflectionHomeomorph a t ha z = z ↔ _
  rw [planeReflectionHomeomorph_apply]
  exact planeReflection_fixed_iff a t ha z

/-- Geometric generalized spheres agree with the fixed sets of the actual generating reflections. -/
theorem isGeneralizedSphere_iff_fixedPoints_reflection (S : Set (ExtendedEuclidean n)) :
    IsGeneralizedSphere S ↔ ∃ f : ExtendedHomeomorph n, IsReflection f ∧ Function.fixedPoints f = S := by
  constructor
  · rintro (⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩)
    · exact ⟨sphereInversionHomeomorph c r hr.ne', sphereInversion_isReflection c r hr,
        fixedPoints_sphereInversion c r hr⟩
    · exact ⟨planeReflectionHomeomorph a t ha, planeReflection_isReflection a t ha,
        fixedPoints_planeReflection a t ha⟩
  · rintro ⟨f, (⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩), rfl⟩
    · exact Or.inl ⟨c, r, hr, fixedPoints_sphereInversion c r hr⟩
    · exact Or.inr ⟨a, t, ha, fixedPoints_planeReflection a t ha⟩

/-- Conjugation transports the complete fixed-point set by the underlying bijection. -/
theorem fixedPoints_homeomorph_conjugation (g f : ExtendedHomeomorph n) :
    Function.fixedPoints (g * f * g⁻¹) = g '' Function.fixedPoints f := by
  ext z
  constructor
  · intro hz
    refine ⟨g⁻¹ z, ?_, by simp⟩
    have h := congrArg (fun w => g⁻¹ w) hz
    change g⁻¹ (g (f (g⁻¹ z))) = g⁻¹ z at h
    change f (g⁻¹ z) = g⁻¹ z
    simpa using h
  · rintro ⟨x, hx, rfl⟩
    change g (f (g⁻¹ (g x))) = g x
    simpa using congrArg g hx

/-- The coefficient space, in leading, vector, and constant coordinates. -/
abbrev SphereCoefficients (n : ℕ) := ℝ × Euclidean n × ℝ

/-- The positive quadratic quantity associated with a genuine sphere coefficient vector. -/
def sphereDiscriminant (a : SphereCoefficients n) : ℝ := ‖a.2.1‖ ^ 2 - a.1 * a.2.2

/-- The extended quadratic locus, with infinity included exactly when the leading coefficient is zero. -/
def sphereCoefficientCarrier (a : SphereCoefficients n) : Set (ExtendedEuclidean n) :=
  {z | z.elim (a.1 = 0)
    (fun x => a.1 * ‖x‖ ^ 2 - 2 * inner ℝ x a.2.1 + a.2.2 = 0)}

/-- A normalized coefficient vector for a Euclidean sphere. -/
def euclideanSphereCoefficients (c : Euclidean n) (r : ℝ) : SphereCoefficients n :=
  (1, c, ‖c‖ ^ 2 - r ^ 2)

/-- A coefficient vector for an extended affine plane. -/
def planeCoefficients (a : Euclidean n) (t : ℝ) : SphereCoefficients n := (0, a, 2 * t)

theorem sphereCoefficientCarrier_euclidean (c : Euclidean n) (r : ℝ) (hr : 0 < r) :
    sphereCoefficientCarrier (euclideanSphereCoefficients c r) = extendedSphere c r := by
  ext z
  cases z using OnePoint.rec with
  | infty => simp [sphereCoefficientCarrier, euclideanSphereCoefficients, extendedSphere]
  | coe x =>
    simp only [extendedSphere, Set.mem_image, OnePoint.coe_eq_coe, exists_eq_right]
    change 1 * ‖x‖ ^ 2 - 2 * inner ℝ x c + (‖c‖ ^ 2 - r ^ 2) = 0 ↔ dist x c = r
    rw [one_mul, dist_eq_norm]
    have hnorm := norm_sub_sq_real x c
    constructor <;> intro h <;> nlinarith [norm_nonneg (x - c)]

theorem sphereCoefficientCarrier_plane (a : Euclidean n) (t : ℝ) :
    sphereCoefficientCarrier (planeCoefficients a t) = plane a t := by
  ext z
  cases z using OnePoint.rec with
  | infty => simp [sphereCoefficientCarrier, planeCoefficients, plane]
  | coe x =>
    simp only [plane, Set.mem_ofPred_eq, OnePoint.coe_ne_infty, false_or,
      OnePoint.coe_eq_coe, exists_eq_right]
    change 0 * ‖x‖ ^ 2 - 2 * inner ℝ x a + 2 * t = 0 ↔ inner ℝ x a = t
    constructor <;> intro h <;> linarith

theorem sphereDiscriminant_euclidean (c : Euclidean n) (r : ℝ) :
    sphereDiscriminant (euclideanSphereCoefficients c r) = r ^ 2 := by
  simp [sphereDiscriminant, euclideanSphereCoefficients]

theorem sphereDiscriminant_plane (a : Euclidean n) (t : ℝ) :
    sphereDiscriminant (planeCoefficients a t) = ‖a‖ ^ 2 := by
  simp [sphereDiscriminant, planeCoefficients]

/-- Genuine sphere and plane coefficient vectors satisfy the required strict positivity. -/
theorem sphereDiscriminant_pos_euclidean (c : Euclidean n) (r : ℝ) (hr : 0 < r) :
    0 < sphereDiscriminant (euclideanSphereCoefficients c r) := by
  rw [sphereDiscriminant_euclidean]
  exact sq_pos_of_pos hr

theorem sphereDiscriminant_pos_plane (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    0 < sphereDiscriminant (planeCoefficients a t) := by
  rw [sphereDiscriminant_plane]
  exact sq_pos_of_pos (norm_pos_iff.mpr ha)

/-- The symmetric bilinear form on coefficient space. -/
def inversivePairing (a b : SphereCoefficients n) : ℝ :=
  2 * inner ℝ a.2.1 b.2.1 - a.1 * b.2.2 - a.2.2 * b.1

theorem inversivePairing_self (a : SphereCoefficients n) :
    inversivePairing a a = 2 * sphereDiscriminant a := by
  simp only [inversivePairing, sphereDiscriminant, real_inner_self_eq_norm_sq]
  ring

theorem inversivePairing_comm (a b : SphereCoefficients n) :
    inversivePairing a b = inversivePairing b a := by
  simp only [inversivePairing, real_inner_comm]
  ring

theorem inversivePairing_add_left (a b c : SphereCoefficients n) :
    inversivePairing (a + b) c = inversivePairing a c + inversivePairing b c := by
  simp only [inversivePairing, Prod.fst_add, Prod.snd_add, inner_add_left]
  ring

theorem inversivePairing_smul_left (k : ℝ) (a b : SphereCoefficients n) :
    inversivePairing (k • a) b = k * inversivePairing a b := by
  simp only [inversivePairing, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_left]
  ring

/-- The inversive product of coefficient representatives. -/
def coefficientInversiveProduct (a b : SphereCoefficients n) : ℝ :=
  |inversivePairing a b| / (2 * Real.sqrt (sphereDiscriminant a) * Real.sqrt (sphereDiscriminant b))

theorem sphereDiscriminant_smul (k : ℝ) (a : SphereCoefficients n) :
    sphereDiscriminant (k • a) = k ^ 2 * sphereDiscriminant a := by
  simp only [sphereDiscriminant, Prod.smul_fst, Prod.smul_snd, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, smul_eq_mul]
  ring

theorem inversivePairing_add_right (a b c : SphereCoefficients n) :
    inversivePairing a (b + c) = inversivePairing a b + inversivePairing a c := by
  rw [inversivePairing_comm a, inversivePairing_add_left]
  rw [inversivePairing_comm b, inversivePairing_comm c]

theorem inversivePairing_smul_right (k : ℝ) (a b : SphereCoefficients n) :
    inversivePairing a (k • b) = k * inversivePairing a b := by
  rw [inversivePairing_comm a, inversivePairing_smul_left, inversivePairing_comm b]

/-- The coefficient formula is independent of multiplication of either representative by a nonzero scalar. -/
theorem coefficientInversiveProduct_smul_left (k : ℝ) (hk : k ≠ 0)
    (a b : SphereCoefficients n) : coefficientInversiveProduct (k • a) b = coefficientInversiveProduct a b := by
  unfold coefficientInversiveProduct
  rw [inversivePairing_smul_left, sphereDiscriminant_smul, abs_mul,
    Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq_eq_abs]
  rw [show 2 * (|k| * Real.sqrt (sphereDiscriminant a)) * Real.sqrt (sphereDiscriminant b) =
    |k| * (2 * Real.sqrt (sphereDiscriminant a) * Real.sqrt (sphereDiscriminant b)) by ring]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr hk)

theorem coefficientInversiveProduct_comm (a b : SphereCoefficients n) :
    coefficientInversiveProduct a b = coefficientInversiveProduct b a := by
  rw [coefficientInversiveProduct, coefficientInversiveProduct, inversivePairing_comm]
  congr 1
  ring

theorem coefficientInversiveProduct_smul_right (k : ℝ) (hk : k ≠ 0)
    (a b : SphereCoefficients n) : coefficientInversiveProduct a (k • b) = coefficientInversiveProduct a b := by
  rw [coefficientInversiveProduct_comm a, coefficientInversiveProduct_smul_left k hk,
    coefficientInversiveProduct_comm b]

/-- equation, for two ordinary positive-radius spheres. -/
theorem coefficientInversiveProduct_sphere_sphere (c d : Euclidean n) (r t : ℝ)
    (hr : 0 < r) (ht : 0 < t) :
    coefficientInversiveProduct (euclideanSphereCoefficients c r) (euclideanSphereCoefficients d t) =
      |(r ^ 2 + t ^ 2 - ‖c - d‖ ^ 2) / (2 * r * t)| := by
  have hp : inversivePairing (euclideanSphereCoefficients c r) (euclideanSphereCoefficients d t) =
      r ^ 2 + t ^ 2 - ‖c - d‖ ^ 2 := by
    rw [norm_sub_sq_real]
    simp only [inversivePairing, euclideanSphereCoefficients, one_mul]
    ring
  rw [coefficientInversiveProduct, hp, sphereDiscriminant_euclidean,
    sphereDiscriminant_euclidean, Real.sqrt_sq hr.le, Real.sqrt_sq ht.le,
    abs_div, abs_of_pos (by positivity : 0 < 2 * r * t)]

/-- equation, for a sphere and an extended plane. -/
theorem coefficientInversiveProduct_sphere_plane (c a : Euclidean n) (r t : ℝ)
    (hr : 0 < r) (ha : a ≠ 0) :
    coefficientInversiveProduct (euclideanSphereCoefficients c r) (planeCoefficients a t) =
      |inner ℝ c a - t| / (r * ‖a‖) := by
  have hp : inversivePairing (euclideanSphereCoefficients c r) (planeCoefficients a t) =
      2 * (inner ℝ c a - t) := by
    simp only [inversivePairing, euclideanSphereCoefficients, planeCoefficients, one_mul, mul_zero,
      sub_zero]
    ring
  rw [coefficientInversiveProduct, hp, sphereDiscriminant_euclidean, sphereDiscriminant_plane,
    Real.sqrt_sq hr.le, Real.sqrt_sq (norm_nonneg a), abs_mul, abs_of_pos two_pos]
  field_simp [hr.ne', norm_ne_zero_iff.mpr ha]

/-- equation, for two extended planes. -/
theorem coefficientInversiveProduct_plane_plane (a b : Euclidean n) (r t : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    coefficientInversiveProduct (planeCoefficients a r) (planeCoefficients b t) =
      |inner ℝ a b| / (‖a‖ * ‖b‖) := by
  rw [coefficientInversiveProduct, sphereDiscriminant_plane, sphereDiscriminant_plane,
    Real.sqrt_sq (norm_nonneg a), Real.sqrt_sq (norm_nonneg b)]
  simp only [inversivePairing, planeCoefficients, zero_mul, mul_zero, sub_zero]
  rw [abs_mul, abs_of_pos two_pos]
  field_simp [norm_ne_zero_iff.mpr ha, norm_ne_zero_iff.mpr hb]

/-- Nonzero scalar multiples give exactly the same extended quadratic locus. -/
theorem sphereCoefficientCarrier_smul (k : ℝ) (hk : k ≠ 0) (a : SphereCoefficients n) :
    sphereCoefficientCarrier (k • a) = sphereCoefficientCarrier a := by
  ext z
  cases z using OnePoint.rec with
  | infty => simp [sphereCoefficientCarrier, Prod.smul_fst, smul_eq_mul, hk]
  | coe x =>
    change (k * a.1) * ‖x‖ ^ 2 - 2 * inner ℝ x (k • a.2.1) + k * a.2.2 = 0 ↔ _
    rw [real_inner_smul_right,
      show (k * a.1) * ‖x‖ ^ 2 - 2 * (k * inner ℝ x a.2.1) + k * a.2.2 =
        k * (a.1 * ‖x‖ ^ 2 - 2 * inner ℝ x a.2.1 + a.2.2) by ring]
    simp only [mul_eq_zero, hk, false_or]
    rfl

/-- Every actual generalized sphere has a genuine positive coefficient representative. -/
theorem exists_positive_sphereCoefficients (S : Set (ExtendedEuclidean n)) (hS : IsGeneralizedSphere S) :
    ∃ a : SphereCoefficients n, 0 < sphereDiscriminant a ∧ sphereCoefficientCarrier a = S := by
  rcases hS with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · exact ⟨euclideanSphereCoefficients c r, sphereDiscriminant_pos_euclidean c r hr,
      sphereCoefficientCarrier_euclidean c r hr⟩
  · exact ⟨planeCoefficients a t, sphereDiscriminant_pos_plane a t ha,
      sphereCoefficientCarrier_plane a t⟩

/-- The bilinear form in its standard Mathlib linear-map type. -/
def inversiveBilinearForm : SphereCoefficients n →ₗ[ℝ] SphereCoefficients n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ inversivePairing inversivePairing_add_left
    (fun k a b => by simpa only [smul_eq_mul] using inversivePairing_smul_left k a b)
    inversivePairing_add_right
    (fun k a b => by simpa only [smul_eq_mul] using inversivePairing_smul_right k a b)

/-- The alternative normalized bilinear-pairing expression. -/
theorem coefficientInversiveProduct_eq_bilinear (a b : SphereCoefficients n)
    (ha : 0 < sphereDiscriminant a) (hb : 0 < sphereDiscriminant b) :
    coefficientInversiveProduct a b = |inversivePairing a b| /
      (Real.sqrt |inversivePairing a a| * Real.sqrt |inversivePairing b b|) := by
  rw [coefficientInversiveProduct, inversivePairing_self, inversivePairing_self,
    abs_of_pos (mul_pos two_pos ha), abs_of_pos (mul_pos two_pos hb),
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2), Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
  congr 1
  symm
  calc
    _ = Real.sqrt 2 ^ 2 * Real.sqrt (sphereDiscriminant a) * Real.sqrt (sphereDiscriminant b) := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]

/-- proved for the full reflection-generated group. -/
theorem IsGeneralizedSphere.image [NeZero n] {S : Set (ExtendedEuclidean n)}
    (hS : IsGeneralizedSphere S) {g : ExtendedHomeomorph n} (hg : g ∈ generalMobiusGroup n) :
    IsGeneralizedSphere (g '' S) := by
  obtain ⟨f, hf, he⟩ := (isGeneralizedSphere_iff_fixedPoints_reflection S).mp hS
  rw [← he, ← fixedPoints_homeomorph_conjugation]
  exact (isGeneralizedSphere_iff_fixedPoints_reflection _).mpr
    ⟨g * f * g⁻¹, generalMobius_conjugate_isReflection hg hf, rfl⟩

theorem mobius_image_isGeneralizedSphere [NeZero n] (g : ExtendedHomeomorph n) (hg : g ∈ generalMobiusGroup n)
    (S : Set (ExtendedEuclidean n)) (hS : IsGeneralizedSphere S) :
    IsGeneralizedSphere (g '' S) := hS.image hg


/-- A quadratic coefficient representative of a positive sphere is unique up to its leading scalar. -/
theorem sphereCoefficients_eq_smul_euclidean [NeZero n] (a : SphereCoefficients n)
    (c : Euclidean n) (r : ℝ) (hr : 0 < r)
    (h : sphereCoefficientCarrier a = extendedSphere c r) :
    a = a.1 • euclideanSphereCoefficients c r := by
  rcases a with ⟨α, u, δ⟩
  have hvanish (v : Euclidean n) (hv : ‖v‖ = r) :
      α * ‖c + v‖ ^ 2 - 2 * inner ℝ (c + v) u + δ = 0 := by
    have hm : ((c + v : Euclidean n) : ExtendedEuclidean n) ∈
        sphereCoefficientCarrier (α, u, δ) := by
      rw [h]
      exact ⟨c + v, by simpa [Metric.mem_sphere, dist_eq_norm] using hv, rfl⟩
    exact hm
  let w := u - α • c
  have horth (v : Euclidean n) (hv : ‖v‖ = r) : inner ℝ v w = 0 := by
    have hp := hvanish v hv
    have hm := hvanish (-v) (by simpa using hv)
    simp only [norm_add_sq_real, norm_neg, inner_add_left, inner_neg_left, inner_neg_right] at hp hm
    dsimp [w]
    rw [inner_sub_right, real_inner_smul_right]
    have hic : inner ℝ c v = inner ℝ v c := real_inner_comm _ _
    rw [hic] at hp hm
    nlinarith
  have hw : w = 0 := by
    by_contra hn
    have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hn
    have hv : ‖(r / ‖w‖) • w‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hnorm)]
      exact div_mul_cancel₀ r hnorm.ne'
    have he := horth ((r / ‖w‖) • w) hv
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at he
    have : 0 < (r / ‖w‖) * ‖w‖ ^ 2 := mul_pos (div_pos hr hnorm) (sq_pos_of_pos hnorm)
    linarith
  have hu : u = α • c := sub_eq_zero.mp hw
  obtain ⟨v, hv⟩ := exists_norm_eq (E := Euclidean n) hr.le
  have hp := hvanish v hv
  have hm := hvanish (-v) (by simpa using hv)
  simp only [norm_add_sq_real, norm_neg, inner_add_left, inner_neg_left, inner_neg_right] at hp hm
  rw [hu, real_inner_smul_right, real_inner_self_eq_norm_sq] at hp hm
  have hδ : δ = α * (‖c‖ ^ 2 - r ^ 2) := by rw [hv] at hp hm; nlinarith
  simp only [euclideanSphereCoefficients, Prod.smul_mk, smul_eq_mul, mul_one]
  exact Prod.ext rfl (Prod.ext hu hδ)


/-- An extended-plane coefficient representative is a scalar multiple of its normal equation. -/
theorem sphereCoefficients_eq_smul_plane (a : SphereCoefficients n)
    (b : Euclidean n) (t : ℝ) (hb : b ≠ 0)
    (h : sphereCoefficientCarrier a = plane b t) :
    ∃ k : ℝ, a = k • planeCoefficients b t := by
  rcases a with ⟨α, u, δ⟩
  have hα : α = 0 := by
    have hm : (∞ : ExtendedEuclidean n) ∈ sphereCoefficientCarrier (α, u, δ) := by
      rw [h]
      exact Or.inl rfl
    exact hm
  subst α
  have hvanish (x : Euclidean n) (hx : inner ℝ x b = t) :
      2 * inner ℝ x u = δ := by
    have hm : (x : ExtendedEuclidean n) ∈ sphereCoefficientCarrier (0, u, δ) := by
      rw [h]
      exact Or.inr ⟨x, hx, rfl⟩
    change 0 * ‖x‖ ^ 2 - 2 * inner ℝ x u + δ = 0 at hm
    linarith
  have hnorm : ‖b‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hb)
  let k := inner ℝ u b / ‖b‖ ^ 2
  let p := (t / ‖b‖ ^ 2) • b
  let w := u - k • b
  have hp : inner ℝ p b = t := by
    dsimp [p]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact div_mul_cancel₀ t hnorm
  have hw : inner ℝ w b = 0 := by
    dsimp [w, k]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      div_mul_cancel₀ _ hnorm, sub_self]
  have hpw : inner ℝ (p + w) b = t := by rw [inner_add_left, hp, hw, add_zero]
  have hpv := hvanish p hp
  have hpwv := hvanish (p + w) hpw
  rw [inner_add_left] at hpwv
  have hwu : inner ℝ w u = 0 := by linarith
  have hww : inner ℝ w w = 0 := by
    change inner ℝ w (u - k • b) = 0
    rw [inner_sub_right, real_inner_smul_right, hwu, hw, mul_zero, sub_self]
  have hw0 : w = 0 := inner_self_eq_zero.mp hww
  have hu : u = k • b := sub_eq_zero.mp hw0
  have hδ : δ = k * (2 * t) := by
    rw [hu, real_inner_smul_right, hp] at hpv
    linarith
  refine ⟨k, ?_⟩
  simp only [planeCoefficients, Prod.smul_mk, smul_eq_mul, mul_zero]
  exact Prod.ext rfl (Prod.ext hu hδ)


/-- two nonzero representatives of the same generalized sphere differ by a nonzero scalar. -/
theorem sphereCoefficients_proportional [NeZero n] (a b : SphereCoefficients n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hS : IsGeneralizedSphere (sphereCoefficientCarrier a))
    (hab : sphereCoefficientCarrier a = sphereCoefficientCarrier b) :
    ∃ k : ℝ, k ≠ 0 ∧ a = k • b := by
  rcases hS with ⟨c, r, hr, h⟩ | ⟨c, t, hc, h⟩
  · have he := sphereCoefficients_eq_smul_euclidean a c r hr h
    have hf := sphereCoefficients_eq_smul_euclidean b c r hr (hab.symm.trans h)
    have hα : a.1 ≠ 0 := by intro hz; rw [hz, zero_smul] at he; exact ha he
    have hβ : b.1 ≠ 0 := by intro hz; rw [hz, zero_smul] at hf; exact hb hf
    refine ⟨a.1 / b.1, div_ne_zero hα hβ, ?_⟩
    calc
      a = a.1 • euclideanSphereCoefficients c r := he
      _ = (a.1 / b.1) • (b.1 • euclideanSphereCoefficients c r) := by
        rw [smul_smul, div_mul_cancel₀ _ hβ]
      _ = _ := by rw [← hf]
  · obtain ⟨α, he⟩ := sphereCoefficients_eq_smul_plane a c t hc h
    obtain ⟨β, hf⟩ := sphereCoefficients_eq_smul_plane b c t hc (hab.symm.trans h)
    have hα : α ≠ 0 := by intro hz; rw [hz, zero_smul] at he; exact ha he
    have hβ : β ≠ 0 := by intro hz; rw [hz, zero_smul] at hf; exact hb hf
    refine ⟨α / β, div_ne_zero hα hβ, ?_⟩
    calc
      a = α • planeCoefficients c t := he
      _ = (α / β) • (β • planeCoefficients c t) := by rw [smul_smul, div_mul_cancel₀ _ hβ]
      _ = _ := by rw [← hf]

@[simp] theorem sphereDiscriminant_zero : sphereDiscriminant (0 : SphereCoefficients n) = 0 := by
  simp [sphereDiscriminant]

/-- Every nonzero coefficient vector defining a genuine generalized sphere satisfies strict positivity. -/
theorem sphereDiscriminant_pos_of_carrier [NeZero n] (a : SphereCoefficients n)
    (ha : a ≠ 0) (hS : IsGeneralizedSphere (sphereCoefficientCarrier a)) :
    0 < sphereDiscriminant a := by
  obtain ⟨b, hb, hba⟩ := exists_positive_sphereCoefficients _ hS
  have hb0 : b ≠ 0 := by intro hz; rw [hz, sphereDiscriminant_zero] at hb; exact lt_irrefl _ hb
  obtain ⟨k, hk, h⟩ := sphereCoefficients_proportional a b ha hb0 hS hba.symm
  rw [h, sphereDiscriminant_smul]
  exact mul_pos (sq_pos_of_ne_zero hk) hb

/-- The inversive product is independent of the nonzero coefficient representatives of the two geometric loci. -/
theorem coefficientInversiveProduct_eq_of_carriers [NeZero n]
    (a a' b b' : SphereCoefficients n) (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hA : IsGeneralizedSphere (sphereCoefficientCarrier a))
    (hB : IsGeneralizedSphere (sphereCoefficientCarrier b))
    (hAA : sphereCoefficientCarrier a = sphereCoefficientCarrier a')
    (hBB : sphereCoefficientCarrier b = sphereCoefficientCarrier b') :
    coefficientInversiveProduct a b = coefficientInversiveProduct a' b' := by
  obtain ⟨k, hk, rfl⟩ := sphereCoefficients_proportional a a' ha ha' hA hAA
  obtain ⟨l, hl, rfl⟩ := sphereCoefficients_proportional b b' hb hb' hB hBB
  rw [coefficientInversiveProduct_smul_left _ hk, coefficientInversiveProduct_smul_right _ hl]

/-- Geometric generalized spheres with their actual extended-space subsets. -/
abbrev GeneralizedSphere (n : ℕ) := {S : Set (ExtendedEuclidean n) // IsGeneralizedSphere S}

/-- A positive coefficient representative chosen for an actual geometric generalized sphere. -/
def generalizedSphereCoefficients (S : GeneralizedSphere n) : SphereCoefficients n :=
  Classical.choose (exists_positive_sphereCoefficients S.val S.property)

theorem generalizedSphereCoefficients_pos (S : GeneralizedSphere n) :
    0 < sphereDiscriminant (generalizedSphereCoefficients S) :=
  (Classical.choose_spec (exists_positive_sphereCoefficients S.val S.property)).1

theorem generalizedSphereCoefficients_carrier (S : GeneralizedSphere n) :
    sphereCoefficientCarrier (generalizedSphereCoefficients S) = S.val :=
  (Classical.choose_spec (exists_positive_sphereCoefficients S.val S.property)).2

/-- The inversive product on actual generalized spheres. -/
def inversiveProduct (S T : GeneralizedSphere n) : ℝ :=
  coefficientInversiveProduct (generalizedSphereCoefficients S) (generalizedSphereCoefficients T)

/-- Any nonzero quadratic representatives compute the same geometric inversive product. -/
theorem inversiveProduct_eq_coefficients [NeZero n] (S T : GeneralizedSphere n)
    (a b : SphereCoefficients n) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : sphereCoefficientCarrier a = S.val) (hB : sphereCoefficientCarrier b = T.val) :
    inversiveProduct S T = coefficientInversiveProduct a b := by
  have hn (U : GeneralizedSphere n) : generalizedSphereCoefficients U ≠ 0 := by
    intro hz
    have hp := generalizedSphereCoefficients_pos U
    rw [hz, sphereDiscriminant_zero] at hp
    exact lt_irrefl _ hp
  apply coefficientInversiveProduct_eq_of_carriers _ _ _ _ (hn S) ha (hn T) hb
  · rw [generalizedSphereCoefficients_carrier]; exact S.property
  · rw [generalizedSphereCoefficients_carrier]; exact T.property
  · rw [generalizedSphereCoefficients_carrier, hA]
  · rw [generalizedSphereCoefficients_carrier, hB]


/-- An ordinary positive-radius sphere as a generalized sphere. -/
def euclideanGeneralizedSphere (c : Euclidean n) (r : ℝ) (hr : 0 < r) : GeneralizedSphere n :=
  ⟨extendedSphere c r, Or.inl ⟨c, r, hr, rfl⟩⟩

/-- An extended affine plane as a generalized sphere. -/
def planeGeneralizedSphere (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) : GeneralizedSphere n :=
  ⟨plane a t, Or.inr ⟨a, t, ha, rfl⟩⟩

theorem sphereCoefficients_ne_zero_of_pos (a : SphereCoefficients n)
    (ha : 0 < sphereDiscriminant a) : a ≠ 0 := by
  intro h
  rw [h, sphereDiscriminant_zero] at ha
  exact lt_irrefl _ ha

/-- The symmetric geometric inversive product. -/
theorem inversiveProduct_comm (S T : GeneralizedSphere n) : inversiveProduct S T = inversiveProduct T S :=
  coefficientInversiveProduct_comm _ _

/-- equation, as an equality for actual geometric spheres. -/
theorem inversiveProduct_sphere_sphere [NeZero n] (c d : Euclidean n) (r t : ℝ)
    (hr : 0 < r) (ht : 0 < t) :
    inversiveProduct (euclideanGeneralizedSphere c r hr) (euclideanGeneralizedSphere d t ht) =
      |(r ^ 2 + t ^ 2 - ‖c - d‖ ^ 2) / (2 * r * t)| := by
  rw [inversiveProduct_eq_coefficients _ _ (euclideanSphereCoefficients c r) (euclideanSphereCoefficients d t)
    (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_euclidean c r hr))
    (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_euclidean d t ht))
    (sphereCoefficientCarrier_euclidean c r hr) (sphereCoefficientCarrier_euclidean d t ht)]
  exact coefficientInversiveProduct_sphere_sphere c d r t hr ht

/-- equation, as an equality for an actual sphere and plane. -/
theorem inversiveProduct_sphere_plane [NeZero n] (c a : Euclidean n) (r t : ℝ)
    (hr : 0 < r) (ha : a ≠ 0) :
    inversiveProduct (euclideanGeneralizedSphere c r hr) (planeGeneralizedSphere a t ha) =
      |inner ℝ c a - t| / (r * ‖a‖) := by
  rw [inversiveProduct_eq_coefficients _ _ (euclideanSphereCoefficients c r) (planeCoefficients a t)
    (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_euclidean c r hr))
    (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_plane a t ha))
    (sphereCoefficientCarrier_euclidean c r hr) (sphereCoefficientCarrier_plane a t)]
  exact coefficientInversiveProduct_sphere_plane c a r t hr ha

/-- equation, as an equality for actual extended planes. -/
theorem inversiveProduct_plane_plane [NeZero n] (a b : Euclidean n) (r t : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    inversiveProduct (planeGeneralizedSphere a r ha) (planeGeneralizedSphere b t hb) =
      |inner ℝ a b| / (‖a‖ * ‖b‖) := by
  rw [inversiveProduct_eq_coefficients _ _ (planeCoefficients a r) (planeCoefficients b t)
    (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_plane a r ha))
    (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_plane b t hb))
    (sphereCoefficientCarrier_plane a r) (sphereCoefficientCarrier_plane b t)]
  exact coefficientInversiveProduct_plane_plane a b r t ha hb

/-- The normalized symmetric bilinear-form description of the geometric inversive product. -/
theorem inversiveProduct_eq_bilinear (S T : GeneralizedSphere n) :
    inversiveProduct S T = |inversiveBilinearForm (generalizedSphereCoefficients S) (generalizedSphereCoefficients T)| /
      (Real.sqrt |inversiveBilinearForm (generalizedSphereCoefficients S) (generalizedSphereCoefficients S)| *
        Real.sqrt |inversiveBilinearForm (generalizedSphereCoefficients T) (generalizedSphereCoefficients T)|) :=
  coefficientInversiveProduct_eq_bilinear _ _ (generalizedSphereCoefficients_pos S)
    (generalizedSphereCoefficients_pos T)

/-- The points are related by reflection in the indicated generalized sphere. -/
def IsInversePair (S : Set (ExtendedEuclidean n)) (x y : ExtendedEuclidean n) : Prop :=
  ∃ f : ExtendedHomeomorph n, IsReflection f ∧ Function.fixedPoints f = S ∧ f x = y

theorem IsInversePair.symm {S : Set (ExtendedEuclidean n)} {x y : ExtendedEuclidean n}
    (h : IsInversePair S x y) : IsInversePair S y x := by
  obtain ⟨f, hf, hS, rfl⟩ := h
  refine ⟨f, hf, hS, ?_⟩
  have hi := congrArg (fun g : ExtendedHomeomorph n => g (f x)) hf.inv_eq
  simpa using hi.symm

/-- actual Möbius transformations transport inverse pairs. -/
theorem IsInversePair.image [NeZero n] {S : Set (ExtendedEuclidean n)} {x y : ExtendedEuclidean n}
    (h : IsInversePair S x y) {g : ExtendedHomeomorph n} (hg : g ∈ generalMobiusGroup n) :
    IsInversePair (g '' S) (g x) (g y) := by
  obtain ⟨f, hf, hS, hxy⟩ := h
  refine ⟨g * f * g⁻¹, generalMobius_conjugate_isReflection hg hf, ?_, ?_⟩
  · rw [fixedPoints_homeomorph_conjugation, hS]
  · change g (f (g⁻¹ (g x))) = g y
    simpa using congrArg g hxy

theorem mobius_preserves_inversePair [NeZero n] (g : ExtendedHomeomorph n) (hg : g ∈ generalMobiusGroup n)
    (S : Set (ExtendedEuclidean n)) (x y : ExtendedEuclidean n) (h : IsInversePair S x y) :
    IsInversePair (g '' S) (g x) (g y) := h.image hg


/-- Multiplying a plane equation by a nonzero real scalar does not change the actual reflection. -/
theorem planeReflectionHomeomorph_smul (a : Euclidean n) (t k : ℝ) (ha : a ≠ 0) (hk : k ≠ 0) :
    planeReflectionHomeomorph (k • a) (k * t) (smul_ne_zero hk ha) =
      planeReflectionHomeomorph a t ha := by
  ext z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    simp only [planeReflectionHomeomorph_apply, planeReflection_coe, OnePoint.coe_eq_coe]
    unfold planeReflectionFinite
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right, smul_smul]
    have he : (2 * (k * inner ℝ x a - k * t) / (k ^ 2 * ‖a‖ ^ 2)) * k =
        2 * (inner ℝ x a - t) / ‖a‖ ^ 2 := by
      field_simp [hk, norm_ne_zero_iff.mpr ha]
    rw [he]

/-- A generalized sphere has a unique generating reflection, independently of its equation. -/
theorem IsReflection.eq_of_fixedPoints [NeZero n] {f g : ExtendedHomeomorph n}
    (hf : IsReflection f) (hg : IsReflection g) (he : Function.fixedPoints f = Function.fixedPoints g) :
    f = g := by
  rcases hf with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · rcases hg with ⟨d, s, hs, rfl⟩ | ⟨b, u, hb, rfl⟩
    · rw [fixedPoints_sphereInversion c r hr, fixedPoints_sphereInversion d s hs] at he
      have hc : sphereCoefficientCarrier (euclideanSphereCoefficients c r) =
          sphereCoefficientCarrier (euclideanSphereCoefficients d s) := by
        rw [sphereCoefficientCarrier_euclidean c r hr, sphereCoefficientCarrier_euclidean d s hs, he]
      obtain ⟨k, hk, heq⟩ := sphereCoefficients_proportional _ _
        (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_euclidean c r hr))
        (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_euclidean d s hs))
        (by rw [sphereCoefficientCarrier_euclidean c r hr]; exact Or.inl ⟨c, r, hr, rfl⟩) hc
      have hk1 : k = 1 := by
        have h := congrArg Prod.fst heq
        simpa [euclideanSphereCoefficients] using h.symm
      rw [hk1, one_smul] at heq
      have hcd : c = d := congrArg (fun a : SphereCoefficients n => a.2.1) heq
      have hsq := congrArg (fun a : SphereCoefficients n => a.2.2) heq
      change ‖c‖ ^ 2 - r ^ 2 = ‖d‖ ^ 2 - s ^ 2 at hsq
      have hrs : r = s := by rw [hcd] at hsq; nlinarith
      subst d
      subst s
      rfl
    · rw [fixedPoints_sphereInversion c r hr, fixedPoints_planeReflection b u hb] at he
      have hm : (∞ : ExtendedEuclidean n) ∈ extendedSphere c r := by rw [he]; exact Or.inl rfl
      simp [extendedSphere] at hm
  · rcases hg with ⟨d, s, hs, rfl⟩ | ⟨b, u, hb, rfl⟩
    · rw [fixedPoints_planeReflection a t ha, fixedPoints_sphereInversion d s hs] at he
      have hm : (∞ : ExtendedEuclidean n) ∈ extendedSphere d s := by rw [← he]; exact Or.inl rfl
      simp [extendedSphere] at hm
    · rw [fixedPoints_planeReflection a t ha, fixedPoints_planeReflection b u hb] at he
      have hc : sphereCoefficientCarrier (planeCoefficients a t) =
          sphereCoefficientCarrier (planeCoefficients b u) := by
        rw [sphereCoefficientCarrier_plane, sphereCoefficientCarrier_plane, he]
      obtain ⟨k, hk, heq⟩ := sphereCoefficients_proportional _ _
        (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_plane a t ha))
        (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_plane b u hb))
        (by rw [sphereCoefficientCarrier_plane]; exact Or.inr ⟨a, t, ha, rfl⟩) hc
      have hab : a = k • b := congrArg (fun a : SphereCoefficients n => a.2.1) heq
      have htu : t = k * u := by
        have h := congrArg (fun a : SphereCoefficients n => a.2.2) heq
        change 2 * t = k * (2 * u) at h
        linarith
      subst a
      subst t
      exact planeReflectionHomeomorph_smul b u k hb hk

/-- The existential definition of inverse pairs equals evaluation by the unique reflection in the sphere. -/
theorem isInversePair_iff_reflection_apply [NeZero n] (S : Set (ExtendedEuclidean n))
    (f : ExtendedHomeomorph n) (hf : IsReflection f) (hS : Function.fixedPoints f = S)
    (x y : ExtendedEuclidean n) : IsInversePair S x y ↔ f x = y := by
  constructor
  · rintro ⟨g, hg, hgS, hxy⟩
    have hfg := hf.eq_of_fixedPoints hg (hS.trans hgS.symm)
    simpa [← hfg] using hxy
  · intro h
    exact ⟨f, hf, hS, h⟩


/-- Every genuine reflection is conjugate to unit-sphere inversion inside the reflection-generated group. -/
theorem IsReflection.conjugate_unitSphere [NeZero n] {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    ∃ g : ExtendedHomeomorph n, g ∈ generalMobiusGroup n ∧
      f = g * sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero * g⁻¹ := by
  rcases hf with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · exact ⟨similarityHomeomorph c r hr.ne', similarity_mem_generalMobiusGroup c r hr,
      sphereInversion_similarity_conjugacy c r hr⟩
  · let b := ((1 - t) / ‖a‖ ^ 2) • a
    have hnorm : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
    have hb : inner ℝ b a = 1 - t := by
      dsimp [b]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, div_mul_cancel₀ _ hnorm]
    let I : ExtendedHomeomorph n := sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero
    let T : ExtendedHomeomorph n := translationHomeomorph b
    let q := I * T
    let c := (2 * (1 : ℝ))⁻¹ • a
    let r := ‖a‖ / (2 * |(1 : ℝ)|)
    have hr : 0 < r := div_pos (norm_pos_iff.mpr ha) (by norm_num)
    have hT : T * planeReflectionHomeomorph a t ha * T⁻¹ = planeReflectionHomeomorph a 1 ha := by
      dsimp [T]
      rw [translation_conjugate_plane, hb, show t + (1 - t) = 1 by ring]
    have hI : I * planeReflectionHomeomorph a 1 ha * I⁻¹ =
        sphereInversionHomeomorph c r hr.ne' :=
      unitSphere_conjugate_plane_nonzero a 1 ha one_ne_zero
    have hq : q * planeReflectionHomeomorph a t ha * q⁻¹ =
        sphereInversionHomeomorph c r hr.ne' := by
      calc
        _ = I * (T * planeReflectionHomeomorph a t ha * T⁻¹) * I⁻¹ := by dsimp [q]; group
        _ = _ := by rw [hT, hI]
    let k := similarityHomeomorph c r hr.ne'
    have hk : k ∈ generalMobiusGroup n := similarity_mem_generalMobiusGroup c r hr
    have hqmem : q ∈ generalMobiusGroup n := (generalMobiusGroup n).mul_mem
      (sphereInversion_isReflection (0 : Euclidean n) 1 zero_lt_one).mem_generalMobiusGroup
      (translation_mem_generalMobiusGroup b)
    refine ⟨q⁻¹ * k, (generalMobiusGroup n).mul_mem ((generalMobiusGroup n).inv_mem hqmem) hk, ?_⟩
    calc
      _ = q⁻¹ * (q * planeReflectionHomeomorph a t ha * q⁻¹) * q := by group
      _ = q⁻¹ * (k * I * k⁻¹) * q := by rw [hq, sphereInversion_similarity_conjugacy c r hr]
      _ = _ := by dsimp [I]; group

/-- corollary: any two genuine reflections are conjugate in the full group. -/
theorem reflections_conjugate [NeZero n] (f g : ExtendedHomeomorph n)
    (hf : IsReflection f) (hg : IsReflection g) :
    ∃ h : ExtendedHomeomorph n, h ∈ generalMobiusGroup n ∧ f = h * g * h⁻¹ := by
  obtain ⟨a, ha, he⟩ := hf.conjugate_unitSphere
  obtain ⟨b, hb, he'⟩ := hg.conjugate_unitSphere
  refine ⟨a * b⁻¹, (generalMobiusGroup n).mul_mem ha ((generalMobiusGroup n).inv_mem hb), ?_⟩
  rw [he, he']
  group

end LowDimensionalTopology.Geometry.Inversive
