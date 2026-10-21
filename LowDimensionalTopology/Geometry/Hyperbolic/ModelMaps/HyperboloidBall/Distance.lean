/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HyperboloidBall.PathMetric
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.TranslationCoordinates
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Ball.RadialDistance

/-!
# Distances in the ball and hyperboloid models

Original auxiliary distance formulas for. The formulas concern
the full length-infimum metrics, including every finite dimension.
-/

@[expose] public section
noncomputable section
open Set
open scoped Topology RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}

theorem cosh_ball_radial_log {r : ℝ} (hr : 0≤r) (hr1 : r<1) :
    Real.cosh (Real.log ((1+r)/(1-r)))=1+2*r^2/(1-r^2) := by
  have hm : 0<1-r := by linarith
  have hp : 0<1+r := by linarith
  have hs : 0<1-r^2 := by nlinarith
  rw [Real.cosh_log (div_pos hp hm)]
  field_simp [hm.ne',hp.ne',hs.ne']
  ring

theorem pureTranslationBallHomeomorph_self (x : unitBallDomain n) :
    Inversive.pureTranslationBallHomeomorph x x=ballOrigin n := by
  apply Subtype.ext
  apply OnePoint.coe_injective
  rw [Inversive.pureTranslationBallHomeomorph,ballHomeomorph_coe,Inversive.pureTranslation_apply_self]
  rfl

theorem ballDensity_pathDist_cosh_succ (x y : unitBallDomain (n+1)) :
    Real.cosh ((ballDensity (n+1)).pathDist x y)=1+2*Inversive.ballDistanceRatio x.val y.val := by
  let z:=Inversive.pureTranslationBallHomeomorph x y
  have hr : ‖z.val‖<1 := unitBallDomain_norm_lt z
  have hinv:=Inversive.generalMobius_ballDistanceRatio (Inversive.pureTranslation x)
    (Inversive.pureTranslation_mem_generalMobiusGroup x) (Inversive.pureTranslation_preservesUnitBall x)
    x.val y.val
    ((Inversive.pureTranslation_preservesUnitBall x).maps_ball x.val (unitBallDomain_norm_lt x)).1
    ((Inversive.pureTranslation_preservesUnitBall x).maps_ball y.val (unitBallDomain_norm_lt y)).1
  rw [← ballHomeomorph_val,← ballHomeomorph_val] at hinv
  change Inversive.ballDistanceRatio (Inversive.pureTranslationBallHomeomorph x x).val z.val=_ at hinv
  rw [pureTranslationBallHomeomorph_self] at hinv
  have hs : ‖z.val‖^2/(1-‖z.val‖^2)=Inversive.ballDistanceRatio x.val y.val := by
    simpa [Inversive.ballDistanceRatio,ballOrigin] using hinv
  have hd:=Inversive.pureTranslation_pathDist x x y
  rw [pureTranslationBallHomeomorph_self] at hd
  rw [← hd,ballDensity_pathDist_origin]
  change Real.cosh (Real.log ((1+‖z.val‖)/(1-‖z.val‖)))=_
  rw [cosh_ball_radial_log (norm_nonneg _) hr]
  rw [mul_div_assoc,hs]

theorem ballDensity_pathDist_cosh (x y : unitBallDomain n) :
    Real.cosh ((ballDensity n).pathDist x y)=1+2*Inversive.ballDistanceRatio x.val y.val := by
  cases n with
  | zero =>
    have hxy : x=y := Subsingleton.elim _ _
    subst y
    simp [Auxiliary.Analysis.Density.pathDist_self,Inversive.ballDistanceRatio]
  | succ n => exact ballDensity_pathDist_cosh_succ x y

theorem hyperboloidProject_gap {n : ℕ} (x : Hyperboloid n) :
    1 - ‖(hyperboloidProject x).val‖ ^ 2 = 2 / (1 + x.val.1) := by
  change 1 - ‖hyperboloidProjectRaw x.val‖ ^ 2 = _
  rw [hyperboloidProjectRaw_norm_sq]
  have hx : 1 + x.val.1 ≠ 0 := ne_of_gt (by linarith [x.property.2])
  rw [add_comm x.val.1 1]
  field_simp
  ring

theorem hyperboloid_ballDistanceRatio {n : ℕ} (x y : Hyperboloid n) :
    1 + 2 * Inversive.ballDistanceRatio (hyperboloidProject x).val (hyperboloidProject y).val =
      lorentzForm x.val y.val := by
  have hx : 1 + x.val.1 ≠ 0 := ne_of_gt (by linarith [x.property.2])
  have hy : 1 + y.val.1 ≠ 0 := ne_of_gt (by linarith [y.property.2])
  unfold Inversive.ballDistanceRatio
  rw [hyperboloidProject_gap, hyperboloidProject_gap, dist_eq_norm, norm_sub_sq_real]
  change 1 + 2 * ((‖hyperboloidProjectRaw x.val‖ ^ 2 -
    2 * inner ℝ (hyperboloidProjectRaw x.val) (hyperboloidProjectRaw y.val) +
    ‖hyperboloidProjectRaw y.val‖ ^ 2) /
      ((2 / (1 + x.val.1)) * (2 / (1 + y.val.1)))) = _
  rw [hyperboloidProjectRaw_norm_sq, hyperboloidProjectRaw_norm_sq]
  simp only [hyperboloidProjectRaw, inner_smul_left, inner_smul_right, conj_trivial,
    lorentzForm]
  rw [add_comm x.val.1 1, add_comm y.val.1 1]
  field_simp
  ring

theorem hyperboloidPathDist_cosh (x y : Hyperboloid n) :
    Real.cosh (hyperboloidPathDist x y)=lorentzForm x.val y.val := by
  rw [hyperboloidPathDist_eq_ballPathDist,ballDensity_pathDist_cosh]
  exact hyperboloid_ballDistanceRatio x y

end LowDimensionalTopology.Geometry.Hyperbolic
