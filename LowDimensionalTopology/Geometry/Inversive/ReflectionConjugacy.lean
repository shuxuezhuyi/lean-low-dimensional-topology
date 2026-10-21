/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.SphereReflectionConjugacy
/-!
# Reflection conjugacy for inversion charts

A unit-radius inversion with any center conjugates each genuine sphere or plane
reflection to another genuine reflection. The formulas come from the two
reflection-conjugacy modules. This geometric fact permits chart changes through
infinity in the orientation proofs without assuming finite intermediate values.
Similarities and orthogonal maps then give conjugacy by every reflection, hence
by each finite word in the full general Möbius group.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint RealInnerProductSpace
open Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

theorem unitSphere_conjugate_isReflection [NeZero n] {f : ExtendedHomeomorph n}
    (hf : IsReflection f) :
    IsReflection (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero * f *
      (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero)⁻¹) := by
  rcases hf with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · exact unitSphere_conjugate_sphere_isReflection c r hr
  · exact unitSphere_conjugate_plane_isReflection a t ha

theorem sphereUnit_conjugate_isReflection [NeZero n] (c : Euclidean n)
    {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    IsReflection (sphereInversionHomeomorph c 1 one_ne_zero * f *
      (sphereInversionHomeomorph c 1 one_ne_zero)⁻¹) := by
  let T := translationHomeomorph c
  let I := sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero
  have hi : IsReflection (T⁻¹ * f * (T⁻¹)⁻¹) := by
    simpa only [T, translationHomeomorph_inv, neg_neg] using translation_conjugate_isReflection (-c) hf
  have hh := translation_conjugate_isReflection c (unitSphere_conjugate_isReflection hi)
  have hT : sphereInversionHomeomorph c 1 one_ne_zero = T * I * T⁻¹ := by
    simpa only [zero_add] using (translation_conjugate_sphere (0 : Euclidean n) c 1 one_ne_zero).symm
  have heq : sphereInversionHomeomorph c 1 one_ne_zero * f *
      (sphereInversionHomeomorph c 1 one_ne_zero)⁻¹ =
      T * (I * (T⁻¹ * f * (T⁻¹)⁻¹) * I⁻¹) * T⁻¹ := by
    rw [hT]
    group
  rw [heq]
  exact hh

/-! ## Similarities, orthogonal maps and arbitrary reflection words -/


theorem dilationHomeomorph_inv (k : ℝ) (hk : k ≠ 0) :
    (dilationHomeomorph k hk : ExtendedHomeomorph n)⁻¹ =
      dilationHomeomorph k⁻¹ (inv_ne_zero hk) := by
  apply inv_eq_of_mul_eq_one_left
  ext z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x => simp [smul_smul, hk]

theorem planeReflectionFinite_dilation (a x : Euclidean n) (t k : ℝ) :
    planeReflectionFinite a (k * t) (k • x) = k • planeReflectionFinite a t x := by
  unfold planeReflectionFinite
  rw [real_inner_smul_left]
  module

theorem inversion_dilation (c x : Euclidean n) (r k : ℝ) (hk : 0 < k) :
    inversion (k • c) (k * r) (k • x) = k • inversion c r x := by
  rw [inversion_formula, inversion_formula, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos hk]
  rw [mul_div_mul_left _ _ hk.ne']
  module

theorem dilation_conjugate_plane (k : ℝ) (hk : 0 < k) (a : Euclidean n)
    (t : ℝ) (ha : a ≠ 0) :
    dilationHomeomorph k hk.ne' * planeReflectionHomeomorph a t ha *
      (dilationHomeomorph k hk.ne')⁻¹ = planeReflectionHomeomorph a (k * t) ha := by
  symm
  apply (eq_mul_inv_iff_mul_eq).mpr
  ext z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    simp only [Homeomorph.mul_apply, dilationHomeomorph_coe,
      planeReflectionHomeomorph_apply, planeReflection_coe]
    exact congrArg OnePoint.some (planeReflectionFinite_dilation a x t k)

theorem dilation_conjugate_sphere [NeZero n] (k : ℝ) (hk : 0 < k)
    (c : Euclidean n) (r : ℝ) (hr : 0 < r) :
    dilationHomeomorph k hk.ne' * sphereInversionHomeomorph c r hr.ne' *
      (dilationHomeomorph k hk.ne')⁻¹ =
      sphereInversionHomeomorph (k • c) (k * r) (mul_pos hk hr).ne' := by
  symm
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply extendedHomeomorph_ext_on_cofinite
  filter_upwards [injective_fiber_compl_cofinite (_root_.id : Euclidean n → Euclidean n)
    Function.injective_id c] with x hx
  change x ≠ c at hx
  have hxc : k • x ≠ k • c := by
    intro h
    apply hx
    have hh := congrArg (fun y : Euclidean n ↦ k⁻¹ • y) h
    simpa [smul_smul, hk.ne'] using hh
  simp only [Homeomorph.mul_apply, dilationHomeomorph_coe, sphereInversionHomeomorph_apply]
  rw [sphereInversion_coe _ _ hxc, sphereInversion_coe c r hx, dilationHomeomorph_coe]
  exact congrArg OnePoint.some (inversion_dilation c x r k hk)

theorem dilation_conjugate_isReflection [NeZero n] (k : ℝ) (hk : 0 < k)
    {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    IsReflection (dilationHomeomorph k hk.ne' * f * (dilationHomeomorph k hk.ne')⁻¹) := by
  rcases hf with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · rw [dilation_conjugate_sphere k hk c r hr]
    exact sphereInversion_isReflection _ _ (mul_pos hk hr)
  · rw [dilation_conjugate_plane k hk a t ha]
    exact planeReflection_isReflection _ _ ha

theorem similarity_conjugate_isReflection [NeZero n] (c : Euclidean n) (r : ℝ)
    (hr : 0 < r) {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    IsReflection (similarityHomeomorph c r hr.ne' * f * (similarityHomeomorph c r hr.ne')⁻¹) := by
  have hh := translation_conjugate_isReflection c (dilation_conjugate_isReflection r hr hf)
  simpa only [similarityHomeomorph, mul_inv_rev, mul_assoc] using hh

theorem similarity_inv_conjugate_isReflection [NeZero n] (c : Euclidean n) (r : ℝ)
    (hr : 0 < r) {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    IsReflection ((similarityHomeomorph c r hr.ne')⁻¹ * f * similarityHomeomorph c r hr.ne') := by
  have hh := dilation_conjugate_isReflection r⁻¹ (inv_pos.mpr hr)
    (translation_conjugate_isReflection (-c) hf)
  simpa only [similarityHomeomorph, mul_inv_rev, dilationHomeomorph_inv,
    translationHomeomorph_inv, inv_inv, neg_neg, mul_assoc] using hh

theorem sphere_conjugate_isReflection [NeZero n] (c : Euclidean n) (r : ℝ)
    (hr : 0 < r) {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    IsReflection (sphereInversionHomeomorph c r hr.ne' * f *
      (sphereInversionHomeomorph c r hr.ne')⁻¹) := by
  have hi := unitSphere_conjugate_isReflection (similarity_inv_conjugate_isReflection c r hr hf)
  have hh := similarity_conjugate_isReflection c r hr hi
  have heq : sphereInversionHomeomorph c r hr.ne' * f *
      (sphereInversionHomeomorph c r hr.ne')⁻¹ =
    similarityHomeomorph c r hr.ne' *
      (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero *
        ((similarityHomeomorph c r hr.ne')⁻¹ * f * similarityHomeomorph c r hr.ne') *
        (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero)⁻¹) *
      (similarityHomeomorph c r hr.ne')⁻¹ := by
    rw [sphereInversion_similarity_conjugacy c r hr]
    group
  rw [heq]
  exact hh


@[simp] theorem cartanLinearExtensionHom_coe (φ : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
    (x : Euclidean n) : cartanLinearExtensionHom φ x = (φ x : ExtendedEuclidean n) := rfl

@[simp] theorem cartanLinearExtensionHom_infty (φ : Euclidean n ≃ₗᵢ[ℝ] Euclidean n) :
    cartanLinearExtensionHom φ ∞ = ∞ := rfl

theorem inversion_linearIsometry (φ : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
    (c x : Euclidean n) (r : ℝ) :
    φ (inversion c r x) = inversion (φ c) r (φ x) := by
  rw [inversion_formula, inversion_formula, map_add, map_smul, ← map_sub, φ.norm_map]

theorem planeReflectionFinite_linearIsometry (φ : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
    (a x : Euclidean n) (t : ℝ) :
    φ (planeReflectionFinite a t x) = planeReflectionFinite (φ a) t (φ x) := by
  simp only [planeReflectionFinite, map_sub, map_smul, LinearIsometryEquiv.inner_map_map,
    LinearIsometryEquiv.norm_map]

theorem linearIsometry_conjugate_sphere [NeZero n]
    (φ : Euclidean n ≃ₗᵢ[ℝ] Euclidean n) (c : Euclidean n) (r : ℝ) (hr : r ≠ 0) :
    cartanLinearExtensionHom φ * sphereInversionHomeomorph c r hr *
      (cartanLinearExtensionHom φ)⁻¹ = sphereInversionHomeomorph (φ c) r hr := by
  symm
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply extendedHomeomorph_ext_on_cofinite
  filter_upwards [injective_fiber_compl_cofinite (_root_.id : Euclidean n → Euclidean n)
    Function.injective_id c] with x hx
  change x ≠ c at hx
  have hxc : φ x ≠ φ c := fun h ↦ hx (φ.injective h)
  simp only [Homeomorph.mul_apply, cartanLinearExtensionHom_coe, sphereInversionHomeomorph_apply]
  rw [sphereInversion_coe _ _ hxc, sphereInversion_coe c r hx, cartanLinearExtensionHom_coe]
  exact congrArg OnePoint.some (inversion_linearIsometry φ c x r).symm

theorem linearIsometry_conjugate_plane (φ : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
    (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    cartanLinearExtensionHom φ * planeReflectionHomeomorph a t ha *
      (cartanLinearExtensionHom φ)⁻¹ =
    planeReflectionHomeomorph (φ a) t (fun h ↦ ha (φ.injective (h.trans φ.map_zero.symm))) := by
  symm
  apply (eq_mul_inv_iff_mul_eq).mpr
  ext z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    simp only [Homeomorph.mul_apply, cartanLinearExtensionHom_coe,
      planeReflectionHomeomorph_apply, planeReflection_coe]
    exact congrArg OnePoint.some (planeReflectionFinite_linearIsometry φ a x t).symm

theorem linearIsometry_conjugate_isReflection [NeZero n]
    (φ : Euclidean n ≃ₗᵢ[ℝ] Euclidean n) {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    IsReflection (cartanLinearExtensionHom φ * f * (cartanLinearExtensionHom φ)⁻¹) := by
  rcases hf with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · rw [linearIsometry_conjugate_sphere]
    exact sphereInversion_isReflection _ _ hr
  · rw [linearIsometry_conjugate_plane]
    exact planeReflection_isReflection _ _ _

theorem plane_conjugate_isReflection [NeZero n] (a : Euclidean n) (t : ℝ)
    (ha : a ≠ 0) {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    IsReflection (planeReflectionHomeomorph a t ha * f * (planeReflectionHomeomorph a t ha)⁻¹) := by
  let b : Euclidean n := (t / ‖a‖ ^ 2) • a
  have hb : inner ℝ b a = t := by
    dsimp only [b]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)]
  have hP : planeReflectionHomeomorph a t ha =
      translationHomeomorph b * cartanLinearExtensionHom (cartanPlaneLinearIsometry a) *
        (translationHomeomorph b)⁻¹ := by
    rw [cartanLinearExtension_plane, translation_conjugate_plane, zero_add, hb]
  have hi : IsReflection ((translationHomeomorph b)⁻¹ * f * translationHomeomorph b) := by
    simpa only [translationHomeomorph_inv, neg_neg] using translation_conjugate_isReflection (-b) hf
  have hh := translation_conjugate_isReflection b
    (linearIsometry_conjugate_isReflection (cartanPlaneLinearIsometry a) hi)
  have heq : planeReflectionHomeomorph a t ha * f * (planeReflectionHomeomorph a t ha)⁻¹ =
      translationHomeomorph b *
        (cartanLinearExtensionHom (cartanPlaneLinearIsometry a) *
          ((translationHomeomorph b)⁻¹ * f * translationHomeomorph b) *
          (cartanLinearExtensionHom (cartanPlaneLinearIsometry a))⁻¹) *
        (translationHomeomorph b)⁻¹ := by
    rw [hP]
    group
  rw [heq]
  exact hh

theorem IsReflection.conjugate [NeZero n] {g f : ExtendedHomeomorph n}
    (hg : IsReflection g) (hf : IsReflection f) : IsReflection (g * f * g⁻¹) := by
  rcases hg with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · exact sphere_conjugate_isReflection c r hr hf
  · exact plane_conjugate_isReflection a t ha hf

theorem generalMobius_conjugate_isReflection [NeZero n] {g f : ExtendedHomeomorph n}
    (hg : g ∈ generalMobiusGroup n) (hf : IsReflection f) : IsReflection (g * f * g⁻¹) := by
  obtain ⟨l, hl, rfl⟩ := (mem_generalMobiusGroup_iff g).mp hg
  clear hg
  induction l with
  | nil => simpa using hf
  | cons g l ih =>
    have hh := (hl g (by simp)).conjugate (ih (fun h hh ↦ hl h (by simp [hh])))
    simpa only [List.prod_cons, mul_inv_rev, mul_assoc] using hh


end LowDimensionalTopology.Geometry.Inversive
