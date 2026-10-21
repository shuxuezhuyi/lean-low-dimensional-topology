/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.IsometryCoefficients
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineFormulas
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.DiscCircleDistance
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.PoissonKernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology UpperHalfPlane Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- displacement in the native hyperbolic-plane metric. -/
def hDisplacement (g : ℍ ≃ᵢ ℍ) (z : ℍ) : ℝ := dist z (g z)
/-- The half-distance sinh version of the same actual displacement function. -/
def hSinhDisplacement (g : ℍ ≃ᵢ ℍ) (z : ℍ) : ℝ := Real.sinh (hDisplacement g z / 2)

/-- The native isometry attached to an actual real determinant-one matrix. -/
def hSLIsometry (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℍ ≃ᵢ ℍ where
  toEquiv := MulAction.toPerm A
  isometry_toFun := isometry_smul ℍ A

@[simp] theorem hSLIsometry_apply (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    hSLIsometry A z = A • z := rfl

theorem hDisplacement_nonneg (g : ℍ ≃ᵢ ℍ) (z : ℍ) : 0 ≤ hDisplacement g z := dist_nonneg
theorem hSinhDisplacement_nonneg (g : ℍ ≃ᵢ ℍ) (z : ℍ) : 0 ≤ hSinhDisplacement g z :=
  Real.sinh_nonneg_iff.mpr (by unfold hDisplacement; positivity)

theorem hDisplacement_inverse (g : ℍ ≃ᵢ ℍ) (z : ℍ) :
    hDisplacement g.symm z = hDisplacement g z := by
  unfold hDisplacement
  rw [← g.dist_eq z (g.symm z), g.apply_symm_apply, dist_comm]

theorem hSinhDisplacement_inverse (g : ℍ ≃ᵢ ℍ) (z : ℍ) :
    hSinhDisplacement g.symm z = hSinhDisplacement g z := by
  unfold hSinhDisplacement
  rw [hDisplacement_inverse]

theorem hDisplacement_conjugation (g h : ℍ ≃ᵢ ℍ) (z : ℍ) :
    hDisplacement ((h.symm.trans g).trans h) (h z) = hDisplacement g z := by
  change dist (h z) (h (g (h.symm (h z)))) = dist z (g z)
  rw [h.symm_apply_apply, h.dist_eq]

theorem hSinhDisplacement_conjugation (g h : ℍ ≃ᵢ ℍ) (z : ℍ) :
    hSinhDisplacement ((h.symm.trans g).trans h) (h z) = hSinhDisplacement g z := by
  unfold hSinhDisplacement
  rw [hDisplacement_conjugation]

/-- Equality of the sinh variants is exactly equality of the genuine displacement functions. -/
theorem hSinhDisplacement_eq_iff (g h : ℍ ≃ᵢ ℍ) :
    hSinhDisplacement g = hSinhDisplacement h ↔ hDisplacement g = hDisplacement h := by
  constructor
  · intro he
    funext z
    have hz := congrFun he z
    dsimp [hSinhDisplacement] at hz
    have hh := Real.sinh_injective hz
    linarith
  · intro he
    unfold hSinhDisplacement
    rw [he]

/-- The exact standard hyperbolic formula underlying. -/
theorem dilation_half_displacement (k : ℝ) (hk : 0 < k) (z : ℍ) :
    Real.sinh (dist z ((verticalDilationSL k hk • z)) / 2) =
      Real.cosh ((HalfPlaneLine.vertical 0).pointDist z) *
        Real.sinh (|Real.log k| / 2) := by
  rw [halfPlane_sinh_half_dist_eq_norm_formula, verticalLine_pointDist_cosh, verticalDilationSL_coe,
    verticalDilationSL_im]
  simp only [Complex.ofReal_zero, sub_zero]
  have hn : (z : ℂ) - (k : ℂ) * z = ((1-k : ℝ) : ℂ) * z := by push_cast; ring
  rw [hn, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hs : Real.sqrt (z.im * (k * z.im)) = Real.sqrt k * z.im := by
    rw [show z.im * (k * z.im) = k * z.im ^ 2 by ring, Real.sqrt_mul hk.le,
      Real.sqrt_sq (le_of_lt z.im_pos)]
  rw [hs]
  have hlog : Real.sinh (|Real.log k| / 2) = |k - 1| / (2 * Real.sqrt k) := by
    have hp := Real.sqrt_pos.mpr hk
    rw [show |Real.log k| / 2 = |Real.log k / 2| by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)],
      ← Real.abs_sinh, ← Real.log_sqrt hk.le, Real.sinh_log hp, abs_div,
      abs_of_pos (by norm_num : (0:ℝ)<2)]
    have he : Real.sqrt k - (Real.sqrt k)⁻¹ = (k-1) / Real.sqrt k := by
      field_simp
      nlinarith [Real.sq_sqrt hk.le]
    rw [he, abs_div, abs_of_pos hp]
    ring
  rw [hlog, abs_sub_comm]
  field_simp [z.im_ne_zero, (Real.sqrt_pos.mpr hk).ne']


/-- The actual native translation matrix. -/
def hTranslationSL (t : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![1,t;0,1], by simp⟩

theorem hTranslationSL_coe (t : ℝ) (z : ℍ) :
    ((hTranslationSL t • z : ℍ) : ℂ) = (z : ℂ) + t := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [hTranslationSL]

theorem hTranslationSL_im (t : ℝ) (z : ℍ) : (hTranslationSL t • z).im = z.im := by
  change (((hTranslationSL t • z : ℍ) : ℂ)).im = _
  rw [hTranslationSL_coe]
  simp

/-- The standard parabolic case of uses the existing genuine Poisson kernel. -/
theorem translation_half_displacement (t : ℝ) (z : ℍ) :
    Real.sinh (dist z (hTranslationSL t • z) / 2) = |t| / (2 * z.im) := by
  rw [halfPlane_sinh_half_dist_eq_norm_formula, hTranslationSL_coe, hTranslationSL_im]
  rw [show (z : ℂ) - ((z : ℂ) + t) = -(t : ℂ) by abel,
    norm_neg, Complex.norm_real, Real.norm_eq_abs]
  rw [show z.im * z.im = z.im ^ 2 by ring, Real.sqrt_sq z.im_pos.le]

theorem translation_poisson_displacement_constant (t : ℝ) (z : ℍ) :
    Auxiliary.Analysis.halfPlanePoissonKernel z none *
      Real.sinh (dist z (hTranslationSL t • z) / 2) = |t| / 2 := by
  rw [translation_half_displacement, Auxiliary.Analysis.halfPlanePoissonKernel_infinity]
  field_simp [z.im_ne_zero]
  simpa only [UpperHalfPlane.coe_im] using mul_comm z.im |t|

/-- The normalized elliptic formula is expressed in the actual native disc path metric. -/
theorem disc_rotation_half_displacement (u : ℂ) (hu : ‖u‖ = 1) (z : 𝔻) :
    Real.sinh (discPathDist z (discUnitRotation u hu z) / 2) =
      Real.sinh (discPathDist 0 z) * ‖1-u‖ / 2 := by
  have hz : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := sub_pos.mpr z.sq_norm_lt_one
  have hsq := disc_sinh_half_distance_sq z (discUnitRotation u hu z)
  rw [discUnitRotation_coe, norm_mul, hu, one_mul,
    show (z : ℂ) - u * z = (1-u) * z by ring, norm_mul, mul_pow] at hsq
  have hn : 0 ≤ Real.sinh (discPathDist z (discUnitRotation u hu z) / 2) :=
    Real.sinh_nonneg_iff.mpr (by rw [discPathDist_eq_halfPlane]; positivity)
  rw [disc_sinh_distance_zero]
  apply (sq_eq_sq₀ hn (by positivity)).mp
  rw [hsq]
  field_simp [hz.ne']

/-- The actual angle convention yields the usual sine of half the rotation angle. -/
theorem disc_angle_rotation_half_displacement (θ : ℝ) (z : 𝔻) :
    Real.sinh (discPathDist z (discUnitRotation (Complex.exp (Complex.I * θ))
      (by simp [Complex.norm_exp]) z) / 2) =
      Real.sinh (discPathDist 0 z) * |Real.sin (θ / 2)| := by
  rw [disc_rotation_half_displacement, norm_sub_rev,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  norm_num
  ring


/-- The real determinant-one action fixes a point precisely when its real quadratic vanishes. -/
theorem hSL_fixed_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    A • z = z ↔
      (A 1 0 : ℂ) * (z : ℂ) ^ 2 + ((A 1 1 : ℂ) - A 0 0) * z - A 0 1 = 0 := by
  have hd := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ A) z
  change (A 1 0 : ℂ) * z + A 1 1 ≠ 0 at hd
  constructor
  · intro hz
    have he := congrArg (fun w : ℍ => (w : ℂ)) hz
    rw [UpperHalfPlane.coe_specialLinearGroup_apply] at he
    simp only [Algebra.algebraMap_self_apply] at he
    have hm := (div_eq_iff hd).mp he
    linear_combination -hm
  · intro hz
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [Algebra.algebraMap_self_apply]
    apply (div_eq_iff hd).mpr
    linear_combination -hz

/-- A single exact quadratic gives the full native displacement, without choosing a type. -/
theorem hSL_half_displacement_polynomial (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    Real.sinh (dist z (A • z) / 2) =
      ‖(A 1 0 : ℂ) * (z : ℂ) ^ 2 + ((A 1 1 : ℂ) - A 0 0) * z - A 0 1‖ / (2 * z.im) := by
  let D : ℂ := (A 1 0 : ℂ) * z + A 1 1
  have hd : D ≠ 0 := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ A) z
  have hn : 0 < ‖D‖ := norm_pos_iff.mpr hd
  rw [halfPlane_sinh_half_dist_eq_norm_formula, sl2_im_smul, Complex.normSq_eq_norm_sq,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply]
  have hs : Real.sqrt (z.im * (z.im / ‖D‖ ^ 2)) = z.im / ‖D‖ := by
    rw [show z.im * (z.im / ‖D‖ ^ 2) = (z.im / ‖D‖) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  change ‖(z : ℂ) - (((A 0 0 : ℂ) * z + A 0 1) / D)‖ /
    (2 * Real.sqrt (z.im * (z.im / ‖D‖ ^ 2))) = _
  rw [hs]
  have he : (z : ℂ) - (((A 0 0 : ℂ) * z + A 0 1) / D) =
      ((A 1 0 : ℂ) * (z : ℂ) ^ 2 + ((A 1 1 : ℂ) - A 0 0) * z - A 0 1) / D := by
    field_simp
    dsimp [D]
    ring
  rw [he, norm_div]
  field_simp [z.im_ne_zero, hn.ne']

end LowDimensionalTopology.Geometry.Hyperbolic
