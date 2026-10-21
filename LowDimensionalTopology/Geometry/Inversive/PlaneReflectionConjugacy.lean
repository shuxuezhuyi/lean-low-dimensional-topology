/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.Group
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.DenseEmbedding
/-!
# Unit inversion conjugates plane reflections

The two cases distinguish a hyperplane through the origin from one missing it.
Finite coordinate identities extend to the complete one-point compactification
by continuity on a cofinite dense set. Translation conjugacy is included for
changing the center of the conjugating sphere.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint RealInnerProductSpace
open Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

theorem norm_sq_planeReflectionFinite (a : Euclidean n) (t : ℝ) (ha : a ≠ 0)
    (x : Euclidean n) :
    ‖planeReflectionFinite a t x‖ ^ 2 = ‖x‖ ^ 2 + 4 * t * (t - inner ℝ x a) / ‖a‖ ^ 2 := by
  rw [planeReflectionFinite, norm_sub_sq_real, norm_smul, real_inner_smul_right,
    mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)]
  ring

theorem norm_sq_unitInversion (x : Euclidean n) (hx : x ≠ 0) :
    ‖unitInversion x‖ ^ 2 = (‖x‖ ^ 2)⁻¹ := by
  rw [unitInversion, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)]

theorem norm_sq_plane_unitInversion (a x : Euclidean n) (t : ℝ)
    (ha : a ≠ 0) (hx : x ≠ 0) :
    ‖planeReflectionFinite a t (unitInversion x)‖ ^ 2 =
      (4 * t ^ 2 * ‖x‖ ^ 2 - 4 * t * inner ℝ x a + ‖a‖ ^ 2) / (‖x‖ ^ 2 * ‖a‖ ^ 2) := by
  rw [norm_sq_planeReflectionFinite a t ha, norm_sq_unitInversion x hx]
  simp only [unitInversion, real_inner_smul_left]
  field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr ha), pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)]
  ring

theorem norm_sq_sub_scaled_normal (a x : Euclidean n) (t : ℝ) (ht : t ≠ 0) :
    ‖x - (2 * t)⁻¹ • a‖ ^ 2 =
      (4 * t ^ 2 * ‖x‖ ^ 2 - 4 * t * inner ℝ x a + ‖a‖ ^ 2) / (4 * t ^ 2) := by
  rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_right]
  field_simp [ht]
  ring

theorem extendedHomeomorph_ext_on_cofinite [NeZero n] (F G : ExtendedHomeomorph n)
    (h : ∀ᶠ x : Euclidean n in Filter.cofinite,
      F (x : ExtendedEuclidean n) = G (x : ExtendedEuclidean n)) : F = G := by
  have hd : Dense {x : Euclidean n | F (x : ExtendedEuclidean n) = G (x : ExtendedEuclidean n)} := by
    have hdiff := (dense_univ : Dense (Set.univ : Set (Euclidean n))).sdiff_finite
      (Filter.mem_cofinite.mp h)
    simpa using hdiff
  have heq : (fun x : Euclidean n ↦ F (x : ExtendedEuclidean n)) =
      fun x : Euclidean n ↦ G (x : ExtendedEuclidean n) :=
    Continuous.ext_on hd (F.continuous.comp OnePoint.continuous_coe)
      (G.continuous.comp OnePoint.continuous_coe) (fun _ hx ↦ hx)
  have hfull : (F : ExtendedEuclidean n → ExtendedEuclidean n) = G :=
    OnePoint.denseRange_coe.equalizer F.continuous G.continuous heq
  exact Homeomorph.ext (congrFun hfull)

theorem unit_plane_conjugate_finite (a x : Euclidean n) (t : ℝ)
    (ha : a ≠ 0) (ht : t ≠ 0) (hx : x ≠ 0)
    (hv : planeReflectionFinite a t (unitInversion x) ≠ 0) :
    unitInversion (planeReflectionFinite a t (unitInversion x)) =
      inversion ((2 * t)⁻¹ • a) (‖a‖ / (2 * |t|)) x := by
  let D := 4 * t ^ 2 * ‖x‖ ^ 2 - 4 * t * inner ℝ x a + ‖a‖ ^ 2
  have hD : D ≠ 0 := by
    intro h
    have hn := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    apply hn
    rw [norm_sq_plane_unitInversion a x t ha hx]
    change D / (‖x‖ ^ 2 * ‖a‖ ^ 2) = 0
    rw [h, zero_div]
  have hR : (‖a‖ / (2 * |t|)) ^ 2 = ‖a‖ ^ 2 / (4 * t ^ 2) := by
    rw [div_pow, mul_pow, sq_abs]
    norm_num
  rw [unitInversion, norm_sq_plane_unitInversion a x t ha hx, inversion_via_unit, hR]
  simp only [unitInversion, planeReflectionFinite, real_inner_smul_left]
  rw [norm_sq_sub_scaled_normal a x t ht]
  simp only [smul_sub, smul_smul]
  dsimp [D] at hD
  match_scalars <;>
    field_simp [hD, ht, pow_ne_zero 2 (norm_ne_zero_iff.mpr ha),
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)]
  ring_nf at hD ⊢
  linear_combination (mul_inv_cancel₀ hD)

theorem injective_fiber_compl_cofinite {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (b : β) : ∀ᶠ x : α in Filter.cofinite, f x ≠ b := by
  have hs : Set.Subsingleton {x : α | f x = b} := fun x hx y hy ↦ hf (hx.trans hy.symm)
  exact hs.finite.compl_mem_cofinite

theorem unitInversion_injective : Function.Injective (unitInversion : Euclidean n → Euclidean n) := by
  intro x y h
  apply (inversion_involutive (0 : Euclidean n) one_ne_zero).injective
  simpa only [inversion_unit] using h

theorem unit_plane_regular_ne_center (a x : Euclidean n) (t : ℝ)
    (ha : a ≠ 0) (ht : t ≠ 0) (hx : x ≠ 0)
    (hv : planeReflectionFinite a t (unitInversion x) ≠ 0) : x ≠ (2 * t)⁻¹ • a := by
  intro he
  have hn := norm_sq_sub_scaled_normal a x t ht
  have hz : ‖x - (2 * t)⁻¹ • a‖ ^ 2 = 0 := by
    rw [he, sub_self, norm_zero]
    norm_num
  have hzero := (div_eq_zero_iff.mp (hn.symm.trans hz)).resolve_right
    (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero 2 ht))
  apply pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  rw [norm_sq_plane_unitInversion a x t ha hx, hzero, zero_div]

theorem unitSphere_conjugate_plane_nonzero [NeZero n] (a : Euclidean n) (t : ℝ)
    (ha : a ≠ 0) (ht : t ≠ 0) :
    sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero *
      planeReflectionHomeomorph a t ha *
      (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero)⁻¹ =
    sphereInversionHomeomorph ((2 * t)⁻¹ • a) (‖a‖ / (2 * |t|))
      (div_pos (norm_pos_iff.mpr ha) (mul_pos (by norm_num) (abs_pos.mpr ht))).ne' := by
  rw [(sphereInversion_isReflection (0 : Euclidean n) 1 zero_lt_one).inv_eq]
  apply extendedHomeomorph_ext_on_cofinite
  have hxco := injective_fiber_compl_cofinite (_root_.id : Euclidean n → Euclidean n) Function.injective_id 0
  have hvco := injective_fiber_compl_cofinite
    (fun x : Euclidean n ↦ planeReflectionFinite a t (unitInversion x))
    ((planeReflectionFinite_involutive a t ha).injective.comp unitInversion_injective) 0
  filter_upwards [hxco, hvco] with x hx hv
  have hxc := unit_plane_regular_ne_center a x t ha ht hx hv
  change x ≠ 0 at hx
  simp only [Homeomorph.mul_apply, sphereInversionHomeomorph_apply,
    planeReflectionHomeomorph_apply]
  rw [sphereInversion_coe (0 : Euclidean n) 1 hx, inversion_unit,
    planeReflection_coe, sphereInversion_coe (0 : Euclidean n) 1 hv,
    inversion_unit, sphereInversion_coe _ _ hxc]
  exact congrArg OnePoint.some (unit_plane_conjugate_finite a x t ha ht hx hv)

theorem plane_zero_commutes_unit (a x : Euclidean n) :
    planeReflectionFinite a 0 (unitInversion x) = unitInversion (planeReflectionFinite a 0 x) := by
  simp only [← cartanPlaneLinearIsometry_apply, unitInversion, map_smul,
    LinearIsometryEquiv.norm_map]

theorem unit_plane_zero_conjugate_finite (a x : Euclidean n) :
    unitInversion (planeReflectionFinite a 0 (unitInversion x)) = planeReflectionFinite a 0 x := by
  rw [← plane_zero_commutes_unit a (unitInversion x)]
  have hi : unitInversion (unitInversion x) = x := by
    simpa only [inversion_unit] using inversion_inversion (0 : Euclidean n) one_ne_zero x
  rw [hi]

theorem unitSphere_conjugate_plane_zero [NeZero n] (a : Euclidean n) (ha : a ≠ 0) :
    sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero *
      planeReflectionHomeomorph a 0 ha *
      (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero)⁻¹ =
    planeReflectionHomeomorph a 0 ha := by
  rw [(sphereInversion_isReflection (0 : Euclidean n) 1 zero_lt_one).inv_eq]
  apply extendedHomeomorph_ext_on_cofinite
  have hxco := injective_fiber_compl_cofinite (_root_.id : Euclidean n → Euclidean n) Function.injective_id 0
  have hvco := injective_fiber_compl_cofinite
    (fun x : Euclidean n ↦ planeReflectionFinite a 0 (unitInversion x))
    ((planeReflectionFinite_involutive a 0 ha).injective.comp unitInversion_injective) 0
  filter_upwards [hxco, hvco] with x hx hv
  change x ≠ 0 at hx
  simp only [Homeomorph.mul_apply, sphereInversionHomeomorph_apply,
    planeReflectionHomeomorph_apply]
  rw [sphereInversion_coe (0 : Euclidean n) 1 hx, inversion_unit,
    planeReflection_coe, sphereInversion_coe (0 : Euclidean n) 1 hv,
    inversion_unit, planeReflection_coe]
  exact congrArg OnePoint.some (unit_plane_zero_conjugate_finite a x)

theorem unitSphere_conjugate_plane_isReflection [NeZero n] (a : Euclidean n) (t : ℝ)
    (ha : a ≠ 0) :
    IsReflection (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero *
      planeReflectionHomeomorph a t ha *
      (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero)⁻¹) := by
  by_cases ht : t = 0
  · subst t
    rw [unitSphere_conjugate_plane_zero a ha]
    exact planeReflection_isReflection a 0 ha
  · rw [unitSphere_conjugate_plane_nonzero a t ha ht]
    exact sphereInversion_isReflection _ _
      (div_pos (norm_pos_iff.mpr ha) (mul_pos (by norm_num) (abs_pos.mpr ht)))

theorem planeReflectionFinite_translation (a b x : Euclidean n) (t : ℝ) :
    planeReflectionFinite a (t + inner ℝ b a) x =
      b + planeReflectionFinite a t (x - b) := by
  unfold planeReflectionFinite
  rw [inner_sub_left]
  module

theorem inversion_translation (a b x : Euclidean n) (r : ℝ) :
    inversion (a + b) r x = b + inversion a r (x - b) := by
  have hx : x - (a + b) = (x - b) - a := by abel
  rw [inversion_via_unit, inversion_via_unit, hx]
  abel

theorem translationHomeomorph_inv (b : Euclidean n) :
    (translationHomeomorph b)⁻¹ = translationHomeomorph (-b) := by
  apply inv_eq_of_mul_eq_one_left
  ext z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x => simp

theorem translation_conjugate_plane (a b : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    translationHomeomorph b * planeReflectionHomeomorph a t ha *
      (translationHomeomorph b)⁻¹ =
      planeReflectionHomeomorph a (t + inner ℝ b a) ha := by
  rw [translationHomeomorph_inv]
  ext z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    simp only [Homeomorph.mul_apply, translationHomeomorph_coe,
      planeReflectionHomeomorph_apply, planeReflection_coe, OnePoint.coe_eq_coe]
    rw [planeReflectionFinite_translation]
    simp only [sub_eq_add_neg]
    abel

theorem translation_conjugate_sphere [NeZero n] (a b : Euclidean n) (r : ℝ) (hr : r ≠ 0) :
    translationHomeomorph b * sphereInversionHomeomorph a r hr *
      (translationHomeomorph b)⁻¹ = sphereInversionHomeomorph (a + b) r hr := by
  rw [translationHomeomorph_inv]
  apply extendedHomeomorph_ext_on_cofinite
  have hxco := injective_fiber_compl_cofinite (_root_.id : Euclidean n → Euclidean n)
    Function.injective_id (a + b)
  filter_upwards [hxco] with x hx
  change x ≠ a + b at hx
  have hxb : x + -b ≠ a := by intro h; apply hx; rw [← h]; abel
  simp only [Homeomorph.mul_apply, translationHomeomorph_coe, sphereInversionHomeomorph_apply]
  rw [sphereInversion_coe a r hxb, translationHomeomorph_coe, sphereInversion_coe (a + b) r hx]
  apply congrArg OnePoint.some
  rw [inversion_translation]
  simp only [sub_eq_add_neg]
  abel

theorem translation_conjugate_isReflection [NeZero n] (b : Euclidean n)
    {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    IsReflection (translationHomeomorph b * f * (translationHomeomorph b)⁻¹) := by
  rcases hf with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · rw [translation_conjugate_sphere]
    exact sphereInversion_isReflection _ _ hr
  · rw [translation_conjugate_plane]
    exact planeReflection_isReflection _ _ ha

end LowDimensionalTopology.Geometry.Inversive
