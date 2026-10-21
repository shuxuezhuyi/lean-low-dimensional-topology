/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Inversive.Group
public import Mathlib.Analysis.Calculus.Conformal.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Derivatives of geometric reflections

Finite-coordinate derivatives of plane and sphere reflections are positive
scalar multiples of linear reflections. Their real determinant formulas
give the negative Jacobian sign away from a sphere inversion center.
-/

@[expose] public section

open EuclideanGeometry

namespace LowDimensionalTopology.Geometry.Inversive

variable {n : ℕ}

theorem planeReflectionFinite_affine_formula (a : Euclidean n) (t : ℝ) :
    planeReflectionFinite a t = fun x =>
      cartanPlaneLinearIsometry a x + (2 * t / ‖a‖ ^ 2) • a := by
  funext x
  rw [cartanPlaneLinearIsometry_apply]
  unfold planeReflectionFinite
  module

theorem planeReflectionFinite_hasFDerivAt (a : Euclidean n) (t : ℝ) (x : Euclidean n) :
    HasFDerivAt (planeReflectionFinite a t)
      (cartanPlaneLinearIsometry a : Euclidean n →L[ℝ] Euclidean n) x := by
  rw [planeReflectionFinite_affine_formula]
  exact ((cartanPlaneLinearIsometry a : Euclidean n →L[ℝ] Euclidean n).hasFDerivAt).add_const _

theorem planeReflectionFinite_conformalAt (a : Euclidean n) (t : ℝ) (x : Euclidean n) :
    ConformalAt (planeReflectionFinite a t) x :=
  ⟨_, planeReflectionFinite_hasFDerivAt a t x,
    (cartanPlaneLinearIsometry a).toLinearIsometry.isConformalMap⟩

theorem cartanPlaneLinearIsometry_det (a : Euclidean n) (ha : a ≠ 0) :
    LinearMap.det (cartanPlaneLinearIsometry a).toLinearMap = -1 := by
  rw [cartanPlaneLinearIsometry, Submodule.det_reflection]
  have horth : (ℝ ∙ a)ᗮᗮ = ℝ ∙ a := Submodule.orthogonal_orthogonal _
  rw [horth, finrank_span_singleton ha, pow_one]

theorem planeReflectionFinite_fderiv_det (a : Euclidean n) (t : ℝ) (ha : a ≠ 0)
    (x : Euclidean n) :
    LinearMap.det (fderiv ℝ (planeReflectionFinite a t) x).toLinearMap = -1 := by
  rw [(planeReflectionFinite_hasFDerivAt a t x).fderiv]
  exact cartanPlaneLinearIsometry_det a ha

theorem sphereInversion_conformalAt {c x : Euclidean n} {r : ℝ}
    (hr : r ≠ 0) (hx : x ≠ c) : ConformalAt (inversion c r) x := by
  refine ⟨_, sphereInversion_hasFDerivAt r hx, ?_⟩
  exact ((ℝ ∙ (x - c))ᗮ.reflection.toLinearIsometry.isConformalMap).smul
    (pow_ne_zero _ (div_ne_zero hr (dist_ne_zero.mpr hx)))

theorem sphereInversion_fderiv_det {c x : Euclidean n} (r : ℝ) (hx : x ≠ c) :
    LinearMap.det (fderiv ℝ (inversion c r) x).toLinearMap =
      -((r / dist x c) ^ 2) ^ n := by
  rw [(sphereInversion_hasFDerivAt r hx).fderiv]
  change LinearMap.det ((r / dist x c) ^ 2 •
    (ℝ ∙ (x - c))ᗮ.reflection.toLinearMap) = _
  rw [LinearMap.det_smul]
  rw [Submodule.det_reflection]
  have horth : (ℝ ∙ (x - c))ᗮᗮ = ℝ ∙ (x - c) := Submodule.orthogonal_orthogonal _
  rw [horth, finrank_span_singleton (sub_ne_zero.mpr hx), pow_one]
  simp

theorem sphereInversion_fderiv_det_neg {c x : Euclidean n} {r : ℝ}
    (hr : r ≠ 0) (hx : x ≠ c) :
    LinearMap.det (fderiv ℝ (inversion c r) x).toLinearMap < 0 := by
  rw [sphereInversion_fderiv_det r hx]
  exact neg_neg_of_pos (pow_pos (sq_pos_of_ne_zero (div_ne_zero hr (dist_ne_zero.mpr hx))) _)

end LowDimensionalTopology.Geometry.Inversive
