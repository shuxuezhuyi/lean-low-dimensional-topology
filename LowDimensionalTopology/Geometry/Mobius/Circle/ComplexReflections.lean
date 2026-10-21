/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.ReflectionDerivatives
public import LowDimensionalTopology.Geometry.Mobius.FractionalLinear
/-!
# Complex coordinates for geometric reflections

Explicit formulas for the genuine extended reflections.
The equalities include the centers, poles and infinity; the generated-group
and orientation comparison are proved in a separate module.
-/

@[expose] public section
noncomputable section
open scoped OnePoint ComplexConjugate
open EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Mobius.ReflectionBridge
open LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
abbrev e := Complex.orthonormalBasisOneI.repr

theorem inversion_coordinates (a z : ℂ) (r : ℝ) :
    e.symm (inversion (e a) r (e z)) = a + (r / ‖z - a‖) ^ 2 • (z - a) := by
  rw [Inversive.inversion_formula, ← map_sub, e.norm_map]
  simp only [map_add, map_smul, e.symm_apply_apply]

theorem inversion_complex_formula (a z : ℂ) (r : ℝ) (hz : z ≠ a) :
    e.symm (inversion (e a) r (e z)) = a + (r : ℂ) ^ 2 / conj (z - a) := by
  rw [inversion_coordinates]
  congr 1
  have hc : conj (z-a) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hz)
  change (((r / ‖z-a‖)^2 : ℝ) : ℂ) * (z-a) = _
  rw [div_pow, Complex.ofReal_div]
  push_cast
  rw [← Complex.mul_conj' (z-a)]
  field_simp [sub_ne_zero.mpr hz, hc]

theorem inner_complex_identity (z a : ℂ) :
    (2 : ℂ) * (inner ℝ z a : ℂ) = z * conj a + conj z * a := by
  apply Complex.ext <;> simp [Complex.inner, Complex.mul_re, Complex.mul_im] <;> ring

theorem planeReflection_complex_formula (a z : ℂ) (t : ℝ) (ha : a ≠ 0) :
    e.symm (Inversive.planeReflectionFinite (e a) t (e z)) =
      -(a / conj a) * conj z + (2 * t : ℝ) / conj a := by
  have hinner : inner ℝ (e z) (e a) = inner ℝ z a := e.inner_map_map _ _
  have hc : conj a ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr ha
  simp only [Inversive.planeReflectionFinite, map_sub, map_smul, e.symm_apply_apply, hinner, e.norm_map]
  change z - (((2*(inner ℝ z a-t)/‖a‖^2 : ℝ) : ℂ) * a) = _
  push_cast
  rw [← Complex.mul_conj' a]
  field_simp [ha, hc]
  linear_combination -(inner_complex_identity z a)
def toComplex (f : Inversive.ExtendedHomeomorph 2) : Equiv.Perm Mobius.ExtendedComplex :=
  (Mobius.extendedComplexEuclideanHomeomorph.toEquiv.trans f.toEquiv).trans
    Mobius.extendedComplexEuclideanHomeomorph.symm.toEquiv

def conjugation : Equiv.Perm Mobius.ExtendedComplex :=
  Complex.conjCLE.toHomeomorph.onePointCongr.toEquiv

@[simp] theorem coordinate_symm_coe (z : Inversive.Euclidean 2) :
    Mobius.extendedComplexEuclideanHomeomorph.symm (z : Inversive.ExtendedEuclidean 2) =
      (e.symm z : Mobius.ExtendedComplex) := rfl

@[simp] theorem coordinate_symm_infty :
    Mobius.extendedComplexEuclideanHomeomorph.symm ∞ = ∞ := rfl

theorem sphereAnti_det (a : ℂ) (r : ℝ) (hr : r ≠ 0) :
    a * (-conj a) - ((r : ℂ)^2 - a * conj a) * 1 ≠ 0 := by
  convert neg_ne_zero.mpr (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr)) using 1; ring

theorem sphereAnti_eq (a : ℂ) (r : ℝ) (hr : r ≠ 0) :
    toComplex (Inversive.sphereInversionHomeomorph (e a) r hr) =
      Mobius.fractionalLinearOfCoefficients a ((r : ℂ)^2-a*conj a) 1 (-conj a)
        (sphereAnti_det a r hr) * conjugation := by
  ext z
  induction z using OnePoint.rec with
  | infty =>
    change Mobius.extendedComplexEuclideanHomeomorph.symm
      (Inversive.sphereInversionHomeomorph (e a) r hr ∞) = _
    simp [Inversive.sphereInversionHomeomorph_apply, Equiv.Perm.mul_apply, conjugation,
      Mobius.fractionalLinearOfCoefficients_infty]
  | coe z =>
    change Mobius.extendedComplexEuclideanHomeomorph.symm
      (Inversive.sphereInversionHomeomorph (e a) r hr (e z)) = _
    rw [Inversive.sphereInversionHomeomorph_apply]
    by_cases hz : z = a
    · subst z
      simp [Equiv.Perm.mul_apply, conjugation, Mobius.fractionalLinearOfCoefficients_coe]
    · have he : e z ≠ e a := fun h => hz (e.injective h)
      rw [Inversive.sphereInversion_coe _ _ he, coordinate_symm_coe, inversion_complex_formula a z r hz]
      have hc : conj z - conj a ≠ 0 := by
        rw [← map_sub]
        exact (map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hz)
      simp only [Equiv.Perm.mul_apply]
      change (a + (r : ℂ)^2 / conj (z-a) : Mobius.ExtendedComplex) =
        Mobius.fractionalLinearOfCoefficients a ((r : ℂ)^2-a*conj a) 1 (-conj a)
          (sphereAnti_det a r hr) (conj z : ℂ)
      rw [Mobius.fractionalLinearOfCoefficients_finite _ _ _ _ _ _ (by simpa [sub_eq_add_neg] using hc)]
      apply congrArg (fun w : ℂ => (w : Mobius.ExtendedComplex))
      rw [map_sub]
      simp only [sub_eq_add_neg] at hc ⊢
      field_simp [hc]
      ring

theorem planeAnti_det (a : ℂ) (t : ℝ) (ha : a ≠ 0) :
    (-a) * conj a - (2*t : ℝ) * 0 ≠ (0 : ℂ) := by
  simp only [mul_zero, sub_zero, neg_mul, neg_ne_zero]
  exact mul_ne_zero ha ((map_ne_zero (starRingEnd ℂ)).mpr ha)

theorem planeAnti_eq (a : ℂ) (t : ℝ) (ha : a ≠ 0) :
    toComplex (Inversive.planeReflectionHomeomorph (e a) t (by intro h; apply ha; exact e.injective (h.trans
      e.map_zero.symm))) =
      Mobius.fractionalLinearOfCoefficients (-a) (2*t : ℝ) 0 (conj a)
        (planeAnti_det a t ha) * conjugation := by
  have hc : conj a ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr ha
  have hea : e a ≠ 0 := by intro h; apply ha; exact e.injective (h.trans e.map_zero.symm)
  ext z
  induction z using OnePoint.rec with
  | infty =>
    change Mobius.extendedComplexEuclideanHomeomorph.symm
      (Inversive.planeReflectionHomeomorph (e a) t hea ∞) = _
    simp [Inversive.planeReflectionHomeomorph_apply, Equiv.Perm.mul_apply, conjugation,
      Mobius.fractionalLinearOfCoefficients_infty]
  | coe z =>
    change Mobius.extendedComplexEuclideanHomeomorph.symm
      (Inversive.planeReflectionHomeomorph (e a) t hea (e z)) = _
    rw [Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_coe, coordinate_symm_coe,
      planeReflection_complex_formula a z t ha]
    simp only [Equiv.Perm.mul_apply]
    change (-(a/conj a)*conj z + ((2*t : ℝ) : ℂ)/conj a : Mobius.ExtendedComplex) =
      Mobius.fractionalLinearOfCoefficients (-a) (2*t : ℝ) 0 (conj a)
        (planeAnti_det a t ha) (conj z : ℂ)
    rw [Mobius.fractionalLinearOfCoefficients_affine]
    apply congrArg (fun w : ℂ => (w : Mobius.ExtendedComplex))
    field_simp

theorem conjugation_sq : conjugation * conjugation = 1 := by
  ext z
  induction z using OnePoint.rec <;> simp [conjugation, Equiv.Perm.mul_apply]

theorem unitSphere_eq_reciprocal_conjugation :
    toComplex (Inversive.sphereInversionHomeomorph (0 : Inversive.Euclidean 2) 1 one_ne_zero) =
      Mobius.reciprocal * conjugation := by
  simpa [Mobius.reciprocal] using sphereAnti_eq 0 1 one_ne_zero

end LowDimensionalTopology.Geometry.Mobius.ReflectionBridge
