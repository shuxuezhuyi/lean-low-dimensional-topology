/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.DihedralAxisFundamentalDomains
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HyperbolicReflectionPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeLineReflections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set Topology
open scoped UpperHalfPlane MatrixGroups Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual positive dilation used by one genuine hyperbolic end block. -/
def signatureBoundaryShift (l : ℝ) : ℍ ≃ᵢ ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (Real.exp l) (Real.exp_pos l))

theorem signatureBoundaryShift_coe (l : ℝ) (z : ℍ) :
    ((signatureBoundaryShift l z : ℍ) : ℂ) = (Real.exp l : ℂ) * (z : ℂ) :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe _ _ _

theorem signatureBoundaryShift_re (l : ℝ) (z : ℍ) :
    (signatureBoundaryShift l z).re = Real.exp l * z.re :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re _ _ _

theorem signatureBoundaryShift_norm (l : ℝ) (z : ℍ) :
    ‖(signatureBoundaryShift l z : ℂ)‖ = Real.exp l * ‖(z : ℂ)‖ := by
  rw [signatureBoundaryShift_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos l)]

theorem signatureBoundaryShift_zero : signatureBoundaryShift 0 = 1 := by
  apply IsometryEquiv.ext
  intro z
  apply UpperHalfPlane.ext
  change (signatureBoundaryShift 0 z : ℂ) = (z : ℂ)
  rw [signatureBoundaryShift_coe, Real.exp_zero, Complex.ofReal_one, one_mul]

theorem signatureBoundaryShift_add (l m : ℝ) :
    signatureBoundaryShift (l + m) = signatureBoundaryShift l * signatureBoundaryShift m := by
  apply IsometryEquiv.ext
  intro z
  apply UpperHalfPlane.ext
  change (signatureBoundaryShift (l + m) z : ℂ) =
    (signatureBoundaryShift l (signatureBoundaryShift m z) : ℂ)
  simp only [signatureBoundaryShift_coe, Real.exp_add, Complex.ofReal_mul, mul_assoc]

theorem signatureBoundaryShift_zpow (l : ℝ) (n : ℤ) :
    signatureBoundaryShift l ^ n = signatureBoundaryShift ((n : ℝ) * l) := by
  let F : Multiplicative ℝ →* (ℍ ≃ᵢ ℍ) := {
    toFun := fun t => signatureBoundaryShift t.toAdd
    map_one' := signatureBoundaryShift_zero
    map_mul' := fun t u => signatureBoundaryShift_add t.toAdd u.toAdd }
  have hp := (map_zpow F (Multiplicative.ofAdd l) n).symm
  change signatureBoundaryShift l ^ n =
    signatureBoundaryShift ((Multiplicative.ofAdd l ^ n).toAdd) at hp
  simpa only [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul] using hp

/-- A literal closed quarter-circle ray, including its finite point on the axis. -/
def signatureBoundaryRay (r : ℝ) : Set ℍ := {z | ‖(z : ℂ)‖ = r ∧ 0 ≤ z.re}

theorem signatureBoundaryRay_subset_line (r : ℝ) (hr : 0 < r) :
    signatureBoundaryRay r ⊆ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 r hr).carrier := by
  intro z hz
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier, Complex.ofReal_zero, sub_zero,
    mem_ofPred_eq] using hz.1

theorem signatureBoundaryRay_nonempty (r : ℝ) (hr : 0 < r) :
    (signatureBoundaryRay r).Nonempty := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam (Real.log r), ?_, ?_⟩
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_norm, Real.exp_log hr]
  · simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam]

/-- The actual hyperbolic generator carries each whole literal side ray to its partner. -/
theorem signatureBoundaryShift_ray_image (l r : ℝ) :
    signatureBoundaryShift l '' signatureBoundaryRay r = signatureBoundaryRay (Real.exp l * r) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨by rw [signatureBoundaryShift_norm, hz.1],
      by rw [signatureBoundaryShift_re]; exact mul_nonneg (Real.exp_pos l).le hz.2⟩
  · intro hw
    refine ⟨signatureBoundaryShift (-l) w, ?_, ?_⟩
    · constructor
      · rw [signatureBoundaryShift_norm, hw.1, ← mul_assoc, ← Real.exp_add]
        simp
      · rw [signatureBoundaryShift_re]
        exact mul_nonneg (Real.exp_pos (-l)).le hw.2
    · change (signatureBoundaryShift l * signatureBoundaryShift (-l)) w = w
      rw [← signatureBoundaryShift_add, add_neg_cancel, signatureBoundaryShift_zero]
      rfl

theorem signatureBoundaryBlock_sides_disjoint (l : ℝ) (hl : 0 < l) :
    Disjoint (signatureBoundaryRay 1) (signatureBoundaryRay (Real.exp l)) := by
  apply disjoint_left.mpr
  intro z hz hz'
  exact (ne_of_gt (Real.one_lt_exp_iff.mpr hl)) (hz'.1.symm.trans hz.1)

/-- The positive shift is the product of two actual concentric native reflections. -/
theorem signatureBoundaryShift_reflections (l : ℝ) :
    (signatureBoundaryShift l : ℍ → ℍ) =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 (Real.sqrt (Real.exp l))
      (Real.sqrt_pos.mpr (Real.exp_pos l))).reflection ∘
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one).reflection := by
  funext z
  simpa only [signatureBoundaryShift, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_apply, mul_one,
    Function.comp_apply] using
    congrFun (_root_.LowDimensionalTopology.Geometry.Hyperbolic.dilation_reflection_factor (Real.exp l) 1 (Real.exp_pos l) zero_lt_one) z

theorem signatureBoundaryShift_hyperbolic (l : ℝ) (hl : 0 < l) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (Real.exp l) (Real.exp_pos l))) := by
  have he : Real.exp l ≠ 1 := ne_of_gt (Real.one_lt_exp_iff.mpr hl)
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (Real.exp l) (Real.exp_pos l)) ≠ 1 := by
    intro h
    have hi := congrArg (fun f : Mobius.complexMobiusGroup => f.val ((UpperHalfPlane.I : ℂ) : Mobius.ExtendedComplex)) h
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action] at hi
    have hi' := OnePoint.coe_injective hi
    have him := congrArg Complex.im hi'
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (Real.exp l) (Real.exp_pos l) • UpperHalfPlane.I).im = 1 at him
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_im] at him
    exact he (by simpa using him)
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ hn).mpr
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_trace_gt_four _ _ he)

/-- This is the true finite-cut funnel sector; its outer ideal interval is not a zero-angle cusp. -/
theorem signatureBoundaryBlock_closure (l : ℝ) (hl : 0 < l) :
    closure (dihedralAxisRightAnnulus l) =
      {z : ℍ | 1 ≤ ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ ≤ Real.exp l ∧ 0 ≤ z.re} :=
  closure_dihedralAxisRightAnnulus l hl

/-- Every nontrivial power has genuine positive displacement throughout the entire funnel. -/
theorem signatureBoundaryShift_zpow_displacement (l : ℝ) (n : ℤ) (z : ℍ) :
    |(n : ℝ) * l| ≤ dist z ((signatureBoundaryShift l ^ n) z) := by
  rw [signatureBoundaryShift_zpow]
  simpa only [Real.log_exp, signatureBoundaryShift,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_apply] using
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.dilation_translation_lower_bound (Real.exp ((n : ℝ) * l)) (Real.exp_pos _) z

/-- A fixed positive native ball radius excludes every nontrivial cyclic end return.
This is the local geometric input for the funnel developing-chart consumer. -/
theorem signatureBoundaryShift_uniform_ball (l : ℝ) (hl : 0 < l) (z : ℍ)
    (n : ℤ) (hn : n ≠ 0) :
    Disjoint (Metric.ball z (l / 3)) ((signatureBoundaryShift l ^ n) '' Metric.ball z (l / 3)) := by
  apply disjoint_left.mpr
  rintro _ hy ⟨x, hx, rfl⟩
  have hnA : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hLow := signatureBoundaryShift_zpow_displacement l n z
  rw [abs_mul, abs_of_pos hl] at hLow
  have hTri := dist_triangle z ((signatureBoundaryShift l ^ n) x) ((signatureBoundaryShift l ^ n) z)
  have hNear : dist ((signatureBoundaryShift l ^ n) x) ((signatureBoundaryShift l ^ n) z) < l / 3 := by
    simpa only [IsometryEquiv.dist_eq, Metric.mem_ball] using hx
  have hy' : dist z ((signatureBoundaryShift l ^ n) x) < l / 3 := by
    simpa only [Metric.mem_ball, dist_comm] using hy
  have hOne : l ≤ |(n : ℝ)| * l := le_mul_of_one_le_left hl.le hnA
  linarith

end LowDimensionalTopology.Geometry.Fuchsian
