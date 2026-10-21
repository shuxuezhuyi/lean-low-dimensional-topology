/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Geometry.Euclidean.Inversion.Calculus
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

/-!
# Inversions and plane reflections

Sphere inversions and affine plane reflections extend to the compactified
space. Their finite-coordinate distance and derivative formulas determine
the infinitesimal magnification away from an inversion center.
The ambient space is genuinely n-dimensional Euclidean space. Its extension
uses `OnePoint` with the usual one-point compactification topology.

Mathlib's finite inversion fixes its center. `sphereInversion` instead swaps
the center and infinity. The derivative and distance
statements concern the finite branch away from the center. Stereographic
projection, the chordal metric, and global continuity are not asserted here.
-/

@[expose] public section
noncomputable section
open scoped Topology RealInnerProductSpace OnePoint
open EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive

/-- The real Euclidean n-space. -/
abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Euclidean n-space with one point at infinity. -/
abbrev ExtendedEuclidean (n : ℕ) := OnePoint (Euclidean n)

variable {n : ℕ}

/-- The finite formula denoted by a star. -/
abbrev unitInversion (x : Euclidean n) : Euclidean n := (‖x‖ ^ 2)⁻¹ • x

/-- inversion in the unit sphere has the star formula. -/
theorem inversion_unit (x : Euclidean n) : inversion 0 1 x = unitInversion x := by
  simp [inversion, unitInversion]

/-- The finite inversion formula in Euclidean coordinates. -/
theorem inversion_formula (c : Euclidean n) (r : ℝ) (x : Euclidean n) :
    inversion c r x = c + (r / ‖x - c‖) ^ 2 • (x - c) := by
  simp [inversion, dist_eq_norm, add_comm]

/-- A general sphere inversion expressed with the star formula. -/
theorem inversion_via_unit (c : Euclidean n) (r : ℝ) (x : Euclidean n) :
    inversion c r x = c + r ^ 2 • unitInversion (x - c) := by
  simp [inversion_formula, unitInversion, div_eq_mul_inv, smul_smul, mul_pow, inv_pow]

/-- The sphere with the given center and radius. -/
abbrev sphere (c : Euclidean n) (r : ℝ) : Set (Euclidean n) := Metric.sphere c r

/-- sphere inversion including the center and infinity. -/
def sphereInversion (c : Euclidean n) (r : ℝ) : ExtendedEuclidean n → ExtendedEuclidean n :=
  fun z ↦ z.elim (c : ExtendedEuclidean n)
    (fun x ↦ if x = c then ∞ else ((inversion c r x : Euclidean n) : ExtendedEuclidean n))

/-- infinity is sent to the center. -/
@[simp] theorem sphereInversion_infty (c : Euclidean n) (r : ℝ) :
    sphereInversion c r ∞ = c := rfl

/-- The center is sent to infinity. -/
@[simp] theorem sphereInversion_center (c : Euclidean n) (r : ℝ) :
    sphereInversion c r c = ∞ := by simp [sphereInversion]

/-- equation: agreement with finite inversion away from the center. -/
theorem sphereInversion_coe (c : Euclidean n) (r : ℝ) {x : Euclidean n} (hx : x ≠ c) :
    sphereInversion c r x = ((inversion c r x : Euclidean n) : ExtendedEuclidean n) := by
  simp [sphereInversion, hx]

/-- reflecting twice is the identity, including infinity. -/
theorem sphereInversion_involutive (c : Euclidean n) {r : ℝ} (hr : r ≠ 0) :
    Function.Involutive (sphereInversion c r) := by
  intro z
  induction z using OnePoint.rec with
  | infty => simp
  | coe x =>
    by_cases hx : x = c
    · subst x; simp
    · rw [sphereInversion_coe c r hx,
        sphereInversion_coe c r (by simpa [inversion_eq_center hr] using hx),
        inversion_inversion c hr]

/-- sphere inversion is a bijection of the extended space. -/
theorem sphereInversion_bijective (c : Euclidean n) {r : ℝ} (hr : r ≠ 0) :
    Function.Bijective (sphereInversion c r) :=
  (sphereInversion_involutive c hr).bijective

/-- The finite fixed-point criterion away from the center. -/
theorem inversion_fixed_iff {c x : Euclidean n} {r : ℝ} (hr : 0 < r) (hx : x ≠ c) :
    inversion c r x = x ↔ x ∈ sphere c r := by
  refine ⟨fun h ↦ ?_, inversion_of_mem_sphere⟩
  have hd : 0 < dist x c := dist_pos.mpr hx
  have heq := dist_inversion_center c x r
  rw [h] at heq
  have heq' : dist x c ^ 2 = r ^ 2 := by
    have := (eq_div_iff (ne_of_gt hd)).mp heq
    nlinarith
  change dist x c = r
  nlinarith

/-- The complete fixed set is precisely the reflecting sphere. -/
theorem sphereInversion_fixed_iff (c : Euclidean n) {r : ℝ} (hr : 0 < r)
    (z : ExtendedEuclidean n) :
    sphereInversion c r z = z ↔ ∃ x ∈ sphere c r, (x : ExtendedEuclidean n) = z := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe x =>
    by_cases hx : x = c
    · subst x; simp [sphere, ne_of_gt hr |>.symm]
    · rw [sphereInversion_coe c r hx]
      simp only [OnePoint.coe_eq_coe]
      simpa using inversion_fixed_iff hr hx

/-- The finite reflection across the affine hyperplane with normal a and level t. -/
def planeReflectionFinite (a : Euclidean n) (t : ℝ) (x : Euclidean n) : Euclidean n :=
  x - (2 * (inner ℝ x a - t) / ‖a‖ ^ 2) • a

/-- An affine hyperplane together with infinity. -/
def plane (a : Euclidean n) (t : ℝ) : Set (ExtendedEuclidean n) :=
  {z | z = ∞ ∨ ∃ x : Euclidean n, inner ℝ x a = t ∧ (x : ExtendedEuclidean n) = z}

/-- plane reflection extended by fixing infinity. -/
def planeReflection (a : Euclidean n) (t : ℝ) : ExtendedEuclidean n → ExtendedEuclidean n :=
  OnePoint.map (planeReflectionFinite a t)

/-- Every plane reflection fixes infinity. -/
@[simp] theorem planeReflection_infty (a : Euclidean n) (t : ℝ) :
    planeReflection a t ∞ = ∞ := rfl

/-- The extended plane reflection agrees with its finite-coordinate formula. -/
@[simp] theorem planeReflection_coe (a : Euclidean n) (t : ℝ) (x : Euclidean n) :
    planeReflection a t x = (planeReflectionFinite a t x : ExtendedEuclidean n) := rfl

/-- The normal coordinate is reflected about the defining level of the plane. -/
theorem inner_planeReflectionFinite (a : Euclidean n) (t : ℝ) (ha : a ≠ 0)
    (x : Euclidean n) : inner ℝ (planeReflectionFinite a t x) a = 2 * t - inner ℝ x a := by
  have hn : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  simp only [planeReflectionFinite, inner_sub_left, inner_smul_left,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- The finite plane-reflection formula is involutive. -/
theorem planeReflectionFinite_involutive (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    Function.Involutive (planeReflectionFinite a t) := by
  intro x
  change planeReflectionFinite a t x -
    (2 * (inner ℝ (planeReflectionFinite a t x) a - t) / ‖a‖ ^ 2) • a = x
  rw [inner_planeReflectionFinite a t ha x]
  unfold planeReflectionFinite
  module

/-- plane reflection is involutive on the extended space. -/
theorem planeReflection_involutive (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    Function.Involutive (planeReflection a t) := by
  intro z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x => simp only [planeReflection_coe, planeReflectionFinite_involutive a t ha x]

/-- plane reflection is a bijection of the extended space. -/
theorem planeReflection_bijective (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    Function.Bijective (planeReflection a t) :=
  (planeReflection_involutive a t ha).bijective

/-- finite fixed points are exactly the defining affine hyperplane. -/
theorem planeReflectionFinite_fixed_iff (a : Euclidean n) (t : ℝ) (ha : a ≠ 0)
    (x : Euclidean n) : planeReflectionFinite a t x = x ↔ inner ℝ x a = t := by
  constructor
  · intro h
    have h' := congrArg (fun y ↦ inner ℝ y a) h
    rw [inner_planeReflectionFinite a t ha x] at h'
    linarith
  · intro h
    simp [planeReflectionFinite, h]

/-- The fixed set includes infinity and exactly the plane. -/
theorem planeReflection_fixed_iff (a : Euclidean n) (t : ℝ) (ha : a ≠ 0)
    (z : ExtendedEuclidean n) : planeReflection a t z = z ↔ z ∈ plane a t := by
  induction z using OnePoint.rec with
  | infty => simp [plane]
  | coe x =>
    simp only [planeReflection_coe, OnePoint.coe_eq_coe, plane,
      Set.mem_ofPred_eq, OnePoint.coe_ne_infty, false_or]
    simpa using planeReflectionFinite_fixed_iff a t ha x

/-- equation: the two-point distance scaling formula. -/
theorem sphereInversion_dist {c x y : Euclidean n} (r : ℝ) (hx : x ≠ c) (hy : y ≠ c) :
    dist (inversion c r x) (inversion c r y) =
      r ^ 2 / (dist x c * dist y c) * dist x y :=
  dist_inversion_inversion hx hy r

/--
The finite inversion derivative used.
This does not by itself assert the orientation-reversing part of that theorem.
-/
theorem sphereInversion_hasFDerivAt {c x : Euclidean n} (r : ℝ) (hx : x ≠ c) :
    HasFDerivAt (inversion c r)
      ((r / dist x c) ^ 2 •
        ((ℝ ∙ (x - c))ᗮ.reflection : Euclidean n →L[ℝ] Euclidean n)) x :=
  hasFDerivAt_inversion hx

/-- The local scale expressed by a two-point distance quotient. -/
theorem sphereInversion_scale_limit {c x : Euclidean n} (r : ℝ) (hx : x ≠ c) :
    Filter.Tendsto
      (fun y : Euclidean n ↦ dist (inversion c r y) (inversion c r x) / dist y x)
      (𝓝[≠] x) (𝓝 (r ^ 2 / dist x c ^ 2)) := by
  have hd : dist x c ≠ 0 := dist_ne_zero.mpr hx
  have hcont : ContinuousAt (fun y : Euclidean n ↦ r ^ 2 / (dist y c * dist x c)) x :=
    continuousAt_const.div ((continuousAt_id.dist continuousAt_const).mul continuousAt_const)
      (mul_ne_zero hd hd)
  have hlim : Filter.Tendsto (fun y : Euclidean n ↦ r ^ 2 / (dist y c * dist x c))
      (𝓝[≠] x) (𝓝 (r ^ 2 / dist x c ^ 2)) := by
    simpa only [pow_two] using
      hcont.tendsto.mono_left (show 𝓝[≠] x ≤ 𝓝 x from nhdsWithin_le_nhds)
  apply hlim.congr'
  filter_upwards [(eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with y hyc hyx
  rw [dist_inversion_inversion hyc hx r]
  exact (mul_div_cancel_right₀ _ (dist_ne_zero.mpr hyx)).symm

/-- The concluding infinitesimal magnification formula. -/
theorem sphereInversion_magnification {c x : Euclidean n} (r : ℝ) (hx : x ≠ c) :
    Filter.Tendsto
      (fun h : Euclidean n ↦ ‖inversion c r (x + h) - inversion c r x‖ / ‖h‖)
      (𝓝[≠] 0) (𝓝 (r ^ 2 / ‖x - c‖ ^ 2)) := by
  have htrans : Filter.Tendsto (fun h : Euclidean n ↦ x + h) (𝓝[≠] 0) (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun h : Euclidean n ↦ x + h) := by fun_prop
      simpa only [add_zero] using hc.tendsto (0 : Euclidean n) |>.mono_left
        (show 𝓝[≠] (0 : Euclidean n) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simpa using hh
  simpa only [Function.comp_def, dist_eq_norm, add_sub_cancel_left] using
    (sphereInversion_scale_limit r hx).comp htrans

end LowDimensionalTopology.Geometry.Inversive
