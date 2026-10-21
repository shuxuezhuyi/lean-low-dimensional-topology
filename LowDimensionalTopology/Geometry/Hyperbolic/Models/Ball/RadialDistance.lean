/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfSpaceBall
/-!
# The radial distance in the native ball model

The proof uses the genuine Cayley density isometry and the native
upper-half-space vertical distance. An orthogonal reflection carries any ball
point to the north axis; its actual ball action preserves the path metric.
Thus the formula concerns the original length-infimum metric in every positive
finite dimension, including the origin.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Filter EuclideanGeometry Set
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}

def ballOrigin (n : ℕ) : unitBallDomain n := ⟨0,by simp [unitBallDomain]⟩

theorem norm_smul_northPole (r : ℝ) (hr : 0 ≤ r) : ‖r • Inversive.northPole n‖ = r := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,Inversive.norm_northPole,mul_one]

def ballRadialPoint (n : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : unitBallDomain (n+1) :=
  ⟨r • Inversive.northPole n,by
    change dist (r • Inversive.northPole n) 0 < 1
    rw [dist_zero_right,norm_smul_northPole r hr]
    exact hr1⟩

theorem cayleyBallFinite_vertical (t : ℝ) (ht : 0 < t) :
    cayleyBallFinite (t • Inversive.northPole n) = ((t-1)/(t+1)) • Inversive.northPole n := by
  have hP : Inversive.planeReflectionFinite (Inversive.northPole n) 0 (t • Inversive.northPole n) =
    (-t) • Inversive.northPole n := by
    rw [northPlane_finite_formula]
    have hh : (t • Inversive.northPole n) (Fin.last n) = t := by simp [Inversive.northPole]
    rw [hh]
    module
  have hsub : (-t) • Inversive.northPole n-Inversive.northPole n = (-(t+1)) • Inversive.northPole n := by module
  have htp : 0 < t+1 := by linarith
  rw [cayleyBallFinite,hP,Inversive.inversion_formula,hsub,norm_smul,Real.norm_eq_abs,abs_neg,
    abs_of_pos htp,Inversive.norm_northPole,mul_one,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  match_scalars
  field_simp [htp.ne']
  ring

theorem cayleyBallHomeomorph_vertical (t : ℝ) (ht : 0 < t) :
    (cayleyBallHomeomorph n (verticalPoint n t ht)).val = ((t-1)/(t+1)) • Inversive.northPole n := by
  rw [cayleyBallHomeomorph_val]
  have hp := positiveHeight_ne_cayleyPole (t • Inversive.northPole n) (by simpa [Inversive.northPole] using ht)
  change Inversive.finiteEuclideanPart (cayleyBall n) (t • Inversive.northPole n) = _
  rw [finiteEuclideanPart_cayleyBall _ hp,cayleyBallFinite_vertical t ht]

theorem ballDensity_pathDist_origin_radial (n : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    (ballDensity (n+1)).pathDist (ballOrigin (n+1)) (ballRadialPoint n r hr hr1) =
      Real.log ((1+r)/(1-r)) := by
  let t := (1+r)/(1-r)
  have hden : 0 < 1-r := sub_pos.mpr hr1
  have ht : 0 < t := div_pos (by linarith) hden
  have ht1 : 1 ≤ t := by
    apply (le_div_iff₀ hden).mpr
    linarith
  have hcoeff : (t-1)/(t+1) = r := by
    apply (div_eq_iff (by linarith : t+1 ≠ 0)).mpr
    dsimp only [t]
    field_simp [hden.ne']
    ring
  have hzero : cayleyBallHomeomorph n (verticalPoint n 1 zero_lt_one) = ballOrigin (n+1) := by
    apply Subtype.ext
    rw [cayleyBallHomeomorph_vertical]
    simp [ballOrigin]
  have hradial : cayleyBallHomeomorph n (verticalPoint n t ht) = ballRadialPoint n r hr hr1 := by
    apply Subtype.ext
    rw [cayleyBallHomeomorph_vertical,hcoeff]
    rfl
  rw [← hzero,← hradial,cayleyBallHomeomorph_pathDist,verticalPoint_pathDist]
  rw [one_div,Real.log_inv,abs_neg,abs_of_nonneg (Real.log_nonneg ht1)]

theorem ballDensity_pathDist_origin (x : unitBallDomain (n+1)) :
    (ballDensity (n+1)).pathDist (ballOrigin (n+1)) x =
      Real.log ((1+‖x.val‖)/(1-‖x.val‖)) := by
  let r := ‖x.val‖
  have hr : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := unitBallDomain_norm_lt x
  let L := Inversive.cartanPlaneLinearIsometry (x.val-r • Inversive.northPole n)
  have hnorm : ‖x.val‖ = ‖r • Inversive.northPole n‖ := by rw [norm_smul_northPole r hr]
  have hLx : L x.val = r • Inversive.northPole n := Submodule.reflection_sub hnorm
  let g := Inversive.cartanLinearExtensionHom L
  have hg : g ∈ Inversive.generalMobiusGroup (n+1) :=
    Inversive.extendedIsometry_mem_generalMobiusGroup L.toIsometryEquiv
  have hB : Inversive.PreservesUnitBall g := Inversive.cartanLinearExtension_preservesUnitBall L
  have hzero : ballHomeomorph g hB (ballOrigin (n+1)) = ballOrigin (n+1) := by
    apply Subtype.ext
    rw [ballHomeomorph_val]
    change L 0 = 0
    exact L.map_zero
  have hx : ballHomeomorph g hB x = ballRadialPoint n r hr hr1 := by
    apply Subtype.ext
    rw [ballHomeomorph_val]
    exact hLx
  have he := ballDensity_pathDist_invariant g hg hB (ballOrigin (n+1)) x
  rw [hzero,hx] at he
  exact he.symm.trans (ballDensity_pathDist_origin_radial n r hr hr1)
end LowDimensionalTopology.Geometry.Hyperbolic
