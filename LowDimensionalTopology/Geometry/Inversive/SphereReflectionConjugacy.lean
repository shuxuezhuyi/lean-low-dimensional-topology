/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.PlaneReflectionConjugacy

/-!
# Sphere reflection conjugacy under unit inversion

Polynomial norm identities describe the conjugated sphere away from its
exceptional points. A sphere through the origin becomes a plane; otherwise
it remains a sphere. Continuity on a cofinite dense set supplies the full
extended-space equalities.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint RealInnerProductSpace
open Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

namespace SphereConjugacy

def Q (c x : Inversive.Euclidean n) : ℝ := 1 - 2 * inner ℝ x c + ‖c‖ ^ 2 * ‖x‖ ^ 2

def D (c : Inversive.Euclidean n) (r : ℝ) (x : Inversive.Euclidean n) : ℝ :=
  ‖c‖ ^ 2 - 2 * (‖c‖ ^ 2 - r ^ 2) * inner ℝ x c + (‖c‖ ^ 2 - r ^ 2) ^ 2 * ‖x‖ ^ 2

theorem norm_sq_unit_sub (c x : Inversive.Euclidean n) (hx : x ≠ 0) :
    ‖Inversive.unitInversion x - c‖ ^ 2 = Q c x / ‖x‖ ^ 2 := by
  rw [norm_sub_sq_real, Inversive.norm_sq_unitInversion x hx]
  simp only [Inversive.unitInversion, real_inner_smul_left, Q]
  field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)]

theorem Q_ne_zero (c x : Inversive.Euclidean n) (hx : x ≠ 0) (hc : Inversive.unitInversion x ≠ c) :
    Q c x ≠ 0 := by
  have h := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hc))
  rw [norm_sq_unit_sub c x hx] at h
  exact (div_ne_zero_iff.mp h).1

theorem sphere_unit_formula (c x : Inversive.Euclidean n) (r : ℝ) (hx : x ≠ 0)
    (hc : Inversive.unitInversion x ≠ c) :
    inversion c r (Inversive.unitInversion x) = (r ^ 2 / Q c x) • x +
      ((Q c x - r ^ 2 * ‖x‖ ^ 2) / Q c x) • c := by
  rw [Inversive.inversion_formula, div_pow, norm_sq_unit_sub c x hx]
  simp only [Inversive.unitInversion, smul_sub, smul_smul]
  match_scalars <;> field_simp [Q_ne_zero c x hx hc, pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)]
  ring

theorem norm_sq_sphere_unit (c x : Inversive.Euclidean n) (r : ℝ) (hx : x ≠ 0)
    (hc : Inversive.unitInversion x ≠ c) :
    ‖inversion c r (Inversive.unitInversion x)‖ ^ 2 = D c r x / Q c x := by
  rw [sphere_unit_formula c x r hx hc, norm_add_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  field_simp [Q_ne_zero c x hx hc]
  simp only [Q, D]
  ring

theorem D_ne_zero (c x : Inversive.Euclidean n) (r : ℝ) (hx : x ≠ 0)
    (hc : Inversive.unitInversion x ≠ c) (hy : inversion c r (Inversive.unitInversion x) ≠ 0) :
    D c r x ≠ 0 := by
  have h := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  rw [norm_sq_sphere_unit c x r hx hc] at h
  exact (div_ne_zero_iff.mp h).1

theorem unit_sphere_unit_formula (c x : Inversive.Euclidean n) (r : ℝ) (hx : x ≠ 0)
    (hc : Inversive.unitInversion x ≠ c) (hy : inversion c r (Inversive.unitInversion x) ≠ 0) :
    Inversive.unitInversion (inversion c r (Inversive.unitInversion x)) =
      (r ^ 2 / D c r x) • x +
        ((1 - 2 * inner ℝ x c + (‖c‖ ^ 2 - r ^ 2) * ‖x‖ ^ 2) / D c r x) • c := by
  rw [Inversive.unitInversion, norm_sq_sphere_unit c x r hx hc, sphere_unit_formula c x r hx hc]
  simp only [smul_add, smul_smul]
  match_scalars <;> field_simp [Q_ne_zero c x hx hc, D_ne_zero c x r hx hc hy]
  simp only [Q]
  ring

theorem norm_sq_sub_image_center (c x : Inversive.Euclidean n) (r : ℝ)
    (hs : ‖c‖ ^ 2 - r ^ 2 ≠ 0) :
    ‖x - (‖c‖ ^ 2 - r ^ 2)⁻¹ • c‖ ^ 2 =
      D c r x / (‖c‖ ^ 2 - r ^ 2) ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right]
  field_simp [hs]
  simp only [D]
  ring

theorem image_sphere_formula (c x : Inversive.Euclidean n) (r : ℝ)
    (hs : ‖c‖ ^ 2 - r ^ 2 ≠ 0) (hd : D c r x ≠ 0) :
    inversion ((‖c‖ ^ 2 - r ^ 2)⁻¹ • c) (r / |‖c‖ ^ 2 - r ^ 2|) x =
      (r ^ 2 / D c r x) • x +
        ((1 - 2 * inner ℝ x c + (‖c‖ ^ 2 - r ^ 2) * ‖x‖ ^ 2) / D c r x) • c := by
  rw [Inversive.inversion_formula, div_pow, div_pow, sq_abs, norm_sq_sub_image_center c x r hs]
  simp only [smul_sub, smul_smul]
  match_scalars <;> field_simp [hs, hd]
  simp only [D]
  ring

theorem image_plane_formula (c x : Inversive.Euclidean n) (r : ℝ) (hr : 0 < r)
    (hs : ‖c‖ ^ 2 - r ^ 2 = 0) :
    (r ^ 2 / D c r x) • x +
      ((1 - 2 * inner ℝ x c + (‖c‖ ^ 2 - r ^ 2) * ‖x‖ ^ 2) / D c r x) • c =
        Inversive.planeReflectionFinite c (1 / 2) x := by
  have hr2 : r ^ 2 = ‖c‖ ^ 2 := by linarith
  have hc : ‖c‖ ^ 2 ≠ 0 := by nlinarith [sq_pos_of_pos hr]
  have hcn : ‖c‖ ≠ 0 := fun h => hc (by rw [h]; simp)
  simp only [D, hr2, sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [Inversive.planeReflectionFinite]
  match_scalars <;> (field_simp [hcn]; ring)

theorem eventually_generic (c : Inversive.Euclidean n) (r : ℝ) (hr : r ≠ 0) :
    ∀ᶠ x : Inversive.Euclidean n in Filter.cofinite,
      x ≠ 0 ∧ Inversive.unitInversion x ≠ c ∧ inversion c r (Inversive.unitInversion x) ≠ 0 := by
  have h0 := eventually_cofinite_ne (0 : Inversive.Euclidean n)
  have h1 := (inversion_injective (0 : Inversive.Euclidean n) one_ne_zero).tendsto_cofinite.eventually
    (eventually_cofinite_ne c)
  have h2 := ((inversion_injective c hr).comp
    (inversion_injective (0 : Inversive.Euclidean n) one_ne_zero)).tendsto_cofinite.eventually
      (eventually_cofinite_ne (0 : Inversive.Euclidean n))
  simpa only [Inversive.inversion_unit, Function.comp_def] using h0.and (h1.and h2)

theorem center_ne_zero (c : Inversive.Euclidean n) (r : ℝ) (hr : 0 < r)
    (hs : ‖c‖ ^ 2 - r ^ 2 = 0) : c ≠ 0 := by
  intro hc
  rw [hc, norm_zero] at hs
  nlinarith [sq_pos_of_pos hr]

end SphereConjugacy
/-- Conjugating a sphere not through the origin by unit inversion gives the exact image sphere reflection. -/
theorem unitSphere_conjugate_sphere_eq_sphere [NeZero n] (c : Euclidean n) (r : ℝ) (hr : 0 < r)
    (hs : ‖c‖ ^ 2 - r ^ 2 ≠ 0) :
    sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero *
      sphereInversionHomeomorph c r hr.ne' *
        (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero)⁻¹ =
    sphereInversionHomeomorph ((‖c‖ ^ 2 - r ^ 2)⁻¹ • c) (r / |‖c‖ ^ 2 - r ^ 2|)
      (div_pos hr (abs_pos.mpr hs)).ne' := by
  rw [(sphereInversion_isReflection (0 : Euclidean n) 1 zero_lt_one).inv_eq]
  apply extendedHomeomorph_ext_on_cofinite
  filter_upwards [Inversive.SphereConjugacy.eventually_generic c r hr.ne',
    eventually_cofinite_ne ((‖c‖ ^ 2 - r ^ 2)⁻¹ • c)] with x hx hxt
  obtain ⟨hx0, hxc, hxy⟩ := hx
  simp only [Homeomorph.mul_apply, sphereInversionHomeomorph_apply]
  rw [sphereInversion_coe 0 1 hx0, inversion_unit, sphereInversion_coe c r hxc,
    sphereInversion_coe 0 1 hxy, inversion_unit,
    sphereInversion_coe _ _ hxt, OnePoint.coe_eq_coe]
  exact (Inversive.SphereConjugacy.unit_sphere_unit_formula c x r hx0 hxc hxy).trans
    (Inversive.SphereConjugacy.image_sphere_formula c x r hs (Inversive.SphereConjugacy.D_ne_zero c x r hx0 hxc
      hxy)).symm

/-- Conjugating a sphere through the origin by unit inversion gives the exact image plane reflection. -/
theorem unitSphere_conjugate_sphere_eq_plane [NeZero n] (c : Euclidean n) (r : ℝ) (hr : 0 < r)
    (hs : ‖c‖ ^ 2 - r ^ 2 = 0) :
    sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero *
      sphereInversionHomeomorph c r hr.ne' *
        (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero)⁻¹ =
    planeReflectionHomeomorph c (1 / 2) (Inversive.SphereConjugacy.center_ne_zero c r hr hs) := by
  rw [(sphereInversion_isReflection (0 : Euclidean n) 1 zero_lt_one).inv_eq]
  apply extendedHomeomorph_ext_on_cofinite
  filter_upwards [Inversive.SphereConjugacy.eventually_generic c r hr.ne'] with x hx
  obtain ⟨hx0, hxc, hxy⟩ := hx
  simp only [Homeomorph.mul_apply, sphereInversionHomeomorph_apply, planeReflectionHomeomorph_apply]
  rw [sphereInversion_coe 0 1 hx0, inversion_unit, sphereInversion_coe c r hxc,
    sphereInversion_coe 0 1 hxy, inversion_unit, planeReflection_coe, OnePoint.coe_eq_coe]
  exact (Inversive.SphereConjugacy.unit_sphere_unit_formula c x r hx0 hxc hxy).trans
    (Inversive.SphereConjugacy.image_plane_formula c x r hr hs)

/-- Unit sphere inversion conjugates every genuine sphere reflection to a genuine reflection. -/
theorem unitSphere_conjugate_sphere_isReflection [NeZero n] (c : Euclidean n) (r : ℝ) (hr : 0 < r) :
    IsReflection (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero *
      sphereInversionHomeomorph c r hr.ne' *
        (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero)⁻¹) := by
  by_cases hs : ‖c‖ ^ 2 - r ^ 2 = 0
  · rw [unitSphere_conjugate_sphere_eq_plane c r hr hs]
    exact planeReflection_isReflection _ _ _
  · rw [unitSphere_conjugate_sphere_eq_sphere c r hr hs]
    exact sphereInversion_isReflection _ _ (div_pos hr (abs_pos.mpr hs))

end LowDimensionalTopology.Geometry.Inversive
