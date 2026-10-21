module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineFormulas
public import Mathlib.Tactic

/-!
# Lorentz normal coordinates for half-plane geodesics

Normalized side equations are transported through Klein coordinates to Lorentz normal
vectors. Pairings, boosts and point coordinates express distance, orthogonality and
the direction of the inward normal.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

theorem halfPlaneKleinCoordinate_explicit (z : ℍ) :
    halfPlaneKleinCoordinate z =
      ⟨(z.re ^ 2 + z.im ^ 2 - 1) / (z.re ^ 2 + z.im ^ 2 + 1),
        -2 * z.re / (z.re ^ 2 + z.im ^ 2 + 1)⟩ := by
  let D := z.re ^ 2 + z.im ^ 2 + 1
  let F := z.re ^ 2 + (z.im + 1) ^ 2
  have hD : D ≠ 0 := ne_of_gt (by dsimp [D]; positivity)
  have hF : F ≠ 0 := ne_of_gt (by dsimp [F]; nlinarith [sq_nonneg z.re,z.im_pos])
  have hn : ‖cayleyFormula z‖ ^ 2 = (z.re ^ 2 + (z.im - 1) ^ 2) / F := by
    rw [cayleyFormula,norm_div,div_pow,← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.I_re,Complex.I_im,sub_zero,add_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    dsimp [F]
    ring
  have hden : 1 + ‖cayleyFormula z‖ ^ 2 = 2 * D / F := by
    rw [hn]
    field_simp
    dsimp [D,F]
    ring
  change ((2 / (1 + ‖cayleyFormula z‖ ^ 2) : ℝ) : ℂ) *
    (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) = _
  rw [hden]
  apply Complex.ext
  all_goals
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
      sub_zero,add_zero,Complex.div_re,Complex.div_im,Complex.sub_re,Complex.sub_im,
      Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,Complex.normSq_apply,
      UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    change _ = _ / D
    field_simp
    dsimp [D,F]
    ring

/-- The affine equation of a half-plane geodesic in the Klein chart. -/
def hKleinAffine (n : ℂ) (t : ℝ) (z : ℍ) : ℝ :=
  inner ℝ n (halfPlaneKleinCoordinate z) - t

/-- The normalized Lorentz-affine normal and offset of a genuine half-plane h-line. -/
def HalfPlaneLine.incenterNormal : HalfPlaneLine → ℂ
  | .vertical a => ⟨a, -1⟩
  | .circle c r _ => ⟨(1 - c ^ 2 + r ^ 2) / (2 * r), c / r⟩

def HalfPlaneLine.incenterOffset : HalfPlaneLine → ℝ
  | .vertical a => a
  | .circle c r _ => -(1 + c ^ 2 - r ^ 2) / (2 * r)

def halfPlaneKleinHeight (z : ℍ) : ℝ := (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im)

/-- The positive homogeneous denominator of the half-plane Klein chart. -/
def hKleinDenominator (z : ℍ) : ℝ := z.re ^ 2 + z.im ^ 2 + 1

theorem real_div_abs_mul_self (x : ℝ) : x / |x| * x = |x| := by
  by_cases hx : x = 0
  · simp [hx]
  · apply mul_right_cancel₀ (abs_ne_zero.mpr hx)
    field_simp
    nlinarith only [sq_abs x]

/-- Spatial part of the elementary Lorentz boost sending a positive unit time vector to rest. -/
def sideNormalBoost (x : ℂ) (h : ℝ) (n : ℂ) (t : ℝ) : ℂ :=
  n + (inner ℝ n x / (h + 1) - t) • x

theorem complex_inner_rotate (u v : ℂ) :
    inner ℝ (Complex.I * u) (Complex.I * v) = inner ℝ u v := by
  simp only [Euclidean.complex_real_inner_coordinates,Complex.mul_re,Complex.mul_im,Complex.I_re,
    Complex.I_im,zero_mul,one_mul,zero_sub,zero_add]
  ring

/-- The Lorentz pairing of normalized side equations. -/
def HalfPlaneLine.normalPairing (L M : HalfPlaneLine) : ℝ :=
  inner ℝ L.incenterNormal M.incenterNormal - L.incenterOffset * M.incenterOffset

def halfPlanePointSpatial (z : ℍ) : ℂ := halfPlaneKleinHeight z • halfPlaneKleinCoordinate z

theorem halfPlaneKleinHeight_pos (z : ℍ) : 0 < halfPlaneKleinHeight z := by
  unfold halfPlaneKleinHeight
  positivity

theorem verticalLine_incenter_affine (a : ℝ) (z : ℍ) :
    hKleinAffine (HalfPlaneLine.vertical a).incenterNormal (HalfPlaneLine.vertical a).incenterOffset z =
      2 * (z.re - a) / (z.re ^ 2 + z.im ^ 2 + 1) := by
  simp only [hKleinAffine,HalfPlaneLine.incenterNormal,HalfPlaneLine.incenterOffset,
    halfPlaneKleinCoordinate_explicit,Euclidean.complex_real_inner_coordinates]
  field_simp
  ring

theorem circleLine_incenter_affine (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    hKleinAffine (HalfPlaneLine.circle c r hr).incenterNormal
      (HalfPlaneLine.circle c r hr).incenterOffset z =
      (‖(z : ℂ) - (c : ℂ)‖ ^ 2 - r ^ 2) / (r * (z.re ^ 2 + z.im ^ 2 + 1)) := by
  simp only [hKleinAffine,HalfPlaneLine.incenterNormal,HalfPlaneLine.incenterOffset,
    halfPlaneKleinCoordinate_explicit,Euclidean.complex_real_inner_coordinates]
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
    Complex.ofReal_im,sub_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  field_simp
  ring

theorem hKleinDenominator_pos (z : ℍ) : 0 < hKleinDenominator z := by
  unfold hKleinDenominator
  positivity

theorem sideNormalBoost_inner (x : ℂ) (h : ℝ) (n m : ℂ) (t u : ℝ)
    (hx : h ^ 2 - ‖x‖ ^ 2 = 1) (hh : h + 1 ≠ 0) :
    inner ℝ (sideNormalBoost x h n t) (sideNormalBoost x h m u) =
      inner ℝ n m - t * u + (h * t - inner ℝ n x) * (h * u - inner ℝ m x) := by
  have hxx : ‖x‖ ^ 2 = h ^ 2 - 1 := by linarith
  simp only [sideNormalBoost,inner_add_left,inner_add_right,real_inner_smul_left,
    inner_smul_right,real_inner_self_eq_norm_sq]
  rw [real_inner_comm x m,hxx]
  field_simp
  ring

/-- The unit Euclidean normal obtained from the genuine normalized Klein side equation. -/
def HalfPlaneLine.incenterNormalAt (L : HalfPlaneLine) (z : ℍ) : ℂ :=
  ⟨(L.incenterNormal.re - L.incenterOffset) * z.re - L.incenterNormal.im,
    (L.incenterNormal.re - L.incenterOffset) * z.im⟩

theorem HalfPlaneLine.incenterNormal_lorentz_unit (L : HalfPlaneLine) :
    ‖L.incenterNormal‖ ^ 2 - L.incenterOffset ^ 2 = 1 := by
  cases L with
  | vertical a =>
    rw [← Complex.normSq_eq_norm_sq]
    simp only [HalfPlaneLine.incenterNormal, HalfPlaneLine.incenterOffset, Complex.normSq_apply]
    ring
  | circle c r hr =>
    rw [← Complex.normSq_eq_norm_sq]
    simp only [HalfPlaneLine.incenterNormal, HalfPlaneLine.incenterOffset, Complex.normSq_apply]
    field_simp
    ring

theorem HalfPlaneLine.normalPairing_comm (L M : HalfPlaneLine) :
    L.normalPairing M = M.normalPairing L := by
  change inner ℝ L.incenterNormal M.incenterNormal - L.incenterOffset * M.incenterOffset =
    inner ℝ M.incenterNormal L.incenterNormal - M.incenterOffset * L.incenterOffset
  rw [real_inner_comm L.incenterNormal M.incenterNormal]
  ring

def HalfPlaneLine.normalTimeAt (L : HalfPlaneLine) (z : ℍ) : ℝ :=
  halfPlaneKleinHeight z * L.incenterOffset - inner ℝ L.incenterNormal (halfPlanePointSpatial z)

theorem HalfPlaneLine.incenter_affine_eq_zero_iff (L : HalfPlaneLine) (z : ℍ) :
    hKleinAffine L.incenterNormal L.incenterOffset z = 0 ↔ z ∈ L.carrier := by
  have hD : z.re ^ 2 + z.im ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
  cases L with
  | vertical a =>
    rw [verticalLine_incenter_affine,div_eq_zero_iff]
    simp only [hD,or_false,mul_eq_zero,OfNat.ofNat_ne_zero,false_or,sub_eq_zero]
    rfl
  | circle c r hr =>
    rw [circleLine_incenter_affine]
    rw [div_eq_zero_iff]
    simp only [mul_eq_zero,hr.ne',hD,or_false,sub_eq_zero]
    change ‖(z : ℂ) - (c : ℂ)‖ ^ 2 = r ^ 2 ↔ ‖(z : ℂ) - (c : ℂ)‖ = r
    exact sq_eq_sq₀ (norm_nonneg _) hr.le

/-- The hyperbolic sine of distance to a line is the absolute value of its normalized
Klein equation times a positive factor. -/
theorem HalfPlaneLine.sinh_pointDist_incenter_affine (L : HalfPlaneLine) (z : ℍ) :
    Real.sinh (L.pointDist z) = |hKleinAffine L.incenterNormal L.incenterOffset z| * halfPlaneKleinHeight z := by
  have hD : 0 < z.re ^ 2 + z.im ^ 2 + 1 := by positivity
  cases L with
  | vertical a =>
    rw [verticalLine_pointDist_sinh,verticalLine_incenter_affine]
    unfold halfPlaneKleinHeight
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2),abs_of_pos hD]
    field_simp
  | circle c r hr =>
    rw [circleLine_pointDist_sinh,circleLine_incenter_affine]
    unfold halfPlaneKleinHeight
    rw [abs_div,abs_mul,abs_of_pos hr,abs_of_pos hD]
    field_simp

/-- The Lorentz pairing of hyperboloid point coordinates is the hyperbolic cosine of distance. -/
theorem halfPlanePoint_cosh_distance (z w : ℍ) :
    halfPlaneKleinHeight z * halfPlaneKleinHeight w -
      inner ℝ (halfPlanePointSpatial z) (halfPlanePointSpatial w) = Real.cosh (dist z w) := by
  have hz := (hKleinDenominator_pos z).ne'
  have hw := (hKleinDenominator_pos w).ne'
  rw [UpperHalfPlane.cosh_dist']
  simp only [halfPlanePointSpatial,real_inner_smul_left,inner_smul_right,
    halfPlaneKleinCoordinate_explicit,Euclidean.complex_real_inner_coordinates,halfPlaneKleinHeight]
  field_simp
  ring

theorem halfPlaneKleinHeight_lorentz_unit (z : ℍ) :
    halfPlaneKleinHeight z ^ 2 -
      ‖halfPlaneKleinHeight z • halfPlaneKleinCoordinate z‖ ^ 2 = 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (halfPlaneKleinHeight_pos z),mul_pow,
    halfPlaneKleinCoordinate_explicit,← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,halfPlaneKleinHeight]
  field_simp
  ring

def HalfPlaneLine.normalSpatialAt (L : HalfPlaneLine) (z : ℍ) : ℂ :=
  sideNormalBoost (halfPlanePointSpatial z) (halfPlaneKleinHeight z) L.incenterNormal L.incenterOffset

theorem HalfPlaneLine.incenterNormalAt_vertical (a : ℝ) (z : ℍ) :
    (HalfPlaneLine.vertical a).incenterNormalAt z = 1 := by
  apply Complex.ext <;> simp [HalfPlaneLine.incenterNormalAt,HalfPlaneLine.incenterNormal,
    HalfPlaneLine.incenterOffset]

theorem HalfPlaneLine.incenterNormalAt_circle (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (HalfPlaneLine.circle c r hr).incenterNormalAt z = r⁻¹ • ((z : ℂ) - (c : ℂ)) := by
  apply Complex.ext
  all_goals
    simp only [HalfPlaneLine.incenterNormalAt,HalfPlaneLine.incenterNormal,
      HalfPlaneLine.incenterOffset,Complex.smul_re,Complex.smul_im,smul_eq_mul,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero,
      UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    field_simp
    ring

theorem HalfPlaneLine.normalTimeAt_eq_affine (L : HalfPlaneLine) (z : ℍ) :
    L.normalTimeAt z = -halfPlaneKleinHeight z * hKleinAffine L.incenterNormal L.incenterOffset z := by
  simp only [HalfPlaneLine.normalTimeAt,halfPlanePointSpatial,inner_smul_right,hKleinAffine]
  ring

/-- The sign directing a side normal toward the reference point; it is zero on the line. -/
def HalfPlaneLine.inwardNormalSign (L : HalfPlaneLine) (z : ℍ) : ℝ :=
  -L.normalTimeAt z / |L.normalTimeAt z|

theorem HalfPlaneLine.normalSpatialAt_inner (L M : HalfPlaneLine) (z : ℍ) :
    inner ℝ (L.normalSpatialAt z) (M.normalSpatialAt z) =
      L.normalPairing M + L.normalTimeAt z * M.normalTimeAt z := by
  apply sideNormalBoost_inner
  · exact halfPlaneKleinHeight_lorentz_unit z
  · exact ne_of_gt (by linarith [halfPlaneKleinHeight_pos z])

/-- The transformed spatial point has the correct positive unit time relation. -/
theorem halfPlanePoint_boost_norm (z w : ℍ) :
    ‖sideNormalBoost (halfPlanePointSpatial z) (halfPlaneKleinHeight z)
        (halfPlanePointSpatial w) (halfPlaneKleinHeight w)‖ ^ 2 = Real.cosh (dist z w) ^ 2 - 1 := by
  have he := sideNormalBoost_inner (halfPlanePointSpatial z) (halfPlaneKleinHeight z)
    (halfPlanePointSpatial w) (halfPlanePointSpatial w) (halfPlaneKleinHeight w) (halfPlaneKleinHeight w)
    (halfPlaneKleinHeight_lorentz_unit z) (ne_of_gt (by linarith [halfPlaneKleinHeight_pos z]))
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    real_inner_comm (halfPlanePointSpatial z) (halfPlanePointSpatial w),
    halfPlanePoint_cosh_distance z w] at he
  have hu := halfPlaneKleinHeight_lorentz_unit w
  change halfPlaneKleinHeight w ^ 2 - ‖halfPlanePointSpatial w‖ ^ 2 = 1 at hu
  nlinarith only [he,hu]

theorem HalfPlaneLine.incenterNormalAt_inner (L M : HalfPlaneLine) (z : ℍ)
    (hzL : z ∈ L.carrier) (hzM : z ∈ M.carrier) :
    inner ℝ (L.incenterNormalAt z) (M.incenterNormalAt z) =
      inner ℝ L.incenterNormal M.incenterNormal - L.incenterOffset * M.incenterOffset := by
  cases L with
  | vertical a =>
    have hza : z.re = a := hzL
    cases M with
    | vertical b =>
      rw [HalfPlaneLine.incenterNormalAt_vertical,HalfPlaneLine.incenterNormalAt_vertical]
      simp only [HalfPlaneLine.incenterNormal,HalfPlaneLine.incenterOffset,
        Euclidean.complex_real_inner_coordinates,Complex.one_re,
        Complex.one_im,mul_one,mul_zero,add_zero]
      ring
    | circle c r hr =>
      rw [HalfPlaneLine.incenterNormalAt_vertical,HalfPlaneLine.incenterNormalAt_circle]
      simp only [Euclidean.complex_real_inner_coordinates,Complex.one_re,Complex.one_im,one_mul,
        zero_mul,add_zero,Complex.smul_re,smul_eq_mul,Complex.sub_re,Complex.ofReal_re,
        UpperHalfPlane.coe_re,HalfPlaneLine.incenterNormal,HalfPlaneLine.incenterOffset,hza]
      field_simp
      ring
  | circle c r hr =>
    cases M with
    | vertical a =>
      have hza : z.re = a := hzM
      rw [HalfPlaneLine.incenterNormalAt_circle,HalfPlaneLine.incenterNormalAt_vertical]
      simp only [Euclidean.complex_real_inner_coordinates,Complex.one_re,Complex.one_im,mul_one,
        mul_zero,add_zero,Complex.smul_re,smul_eq_mul,Complex.sub_re,Complex.ofReal_re,
        UpperHalfPlane.coe_re,HalfPlaneLine.incenterNormal,HalfPlaneLine.incenterOffset,hza]
      field_simp
      ring
    | circle d s hs =>
      have hL := norm_sub_real_eq_radius_sq hzL
      have hM := norm_sub_real_eq_radius_sq hzM
      rw [HalfPlaneLine.incenterNormalAt_circle,HalfPlaneLine.incenterNormalAt_circle]
      simp only [Euclidean.complex_real_inner_coordinates,Complex.smul_re,Complex.smul_im,smul_eq_mul,
        Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero,
        UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,HalfPlaneLine.incenterNormal,HalfPlaneLine.incenterOffset]
      field_simp
      nlinarith only [hL,hM]

theorem HalfPlaneLine.tangentAt_eq_incenterNormalAt (L : HalfPlaneLine) (z : ℍ)
    (hz : z ∈ L.carrier) :
    L.tangentAt z = ‖L.tangentAt z‖ • (Complex.I * L.incenterNormalAt z) := by
  cases L with
  | vertical a =>
    rw [HalfPlaneLine.incenterNormalAt_vertical]
    simp [HalfPlaneLine.tangentAt]
  | circle c r hr =>
    have he : ‖(HalfPlaneLine.circle c r hr).tangentAt z‖ = r := by
      change ‖Complex.I * ((z : ℂ) - (c : ℂ))‖ = r
      rw [norm_mul,Complex.norm_I,one_mul]
      exact hz
    rw [he,HalfPlaneLine.incenterNormalAt_circle]
    change Complex.I * ((z : ℂ) - (c : ℂ)) = _
    apply Complex.ext
    all_goals
      simp only [Complex.mul_re,Complex.mul_im,Complex.smul_re,Complex.smul_im,smul_eq_mul,
        Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
        Complex.I_im,zero_mul,one_mul,sub_zero,zero_sub,zero_add,UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im]
      field_simp

theorem HalfPlaneLine.normalTimeAt_eq_zero_iff (L : HalfPlaneLine) (z : ℍ) :
    L.normalTimeAt z = 0 ↔ z ∈ L.carrier := by
  rw [L.normalTimeAt_eq_affine,mul_eq_zero]
  simp only [neg_ne_zero.mpr (halfPlaneKleinHeight_pos z).ne',false_or,
    L.incenter_affine_eq_zero_iff z]

theorem HalfPlaneLine.normalTimeAt_abs (L : HalfPlaneLine) (z : ℍ) :
    |L.normalTimeAt z| = Real.sinh (L.pointDist z) := by
  rw [L.normalTimeAt_eq_affine,L.sinh_pointDist_incenter_affine,abs_mul,abs_neg,
    abs_of_pos (halfPlaneKleinHeight_pos z)]
  ring

theorem HalfPlaneLine.normalSpatialAt_norm_sq (L : HalfPlaneLine) (z : ℍ) :
    ‖L.normalSpatialAt z‖ ^ 2 = 1 + L.normalTimeAt z ^ 2 := by
  have he := L.normalSpatialAt_inner L z
  have hu := L.incenterNormal_lorentz_unit
  rw [real_inner_self_eq_norm_sq] at he
  change ‖L.normalSpatialAt z‖ ^ 2 = inner ℝ L.incenterNormal L.incenterNormal -
    L.incenterOffset * L.incenterOffset + L.normalTimeAt z * L.normalTimeAt z at he
  rw [real_inner_self_eq_norm_sq] at he
  nlinarith only [he,hu]

theorem HalfPlaneLine.normalPairing_orthogonal (L M : HalfPlaneLine) (z : ℍ)
    (hz : L.OrthogonalAt M z) : L.normalPairing M = 0 := by
  have he := hz.2.2
  rw [L.tangentAt_eq_incenterNormalAt z hz.1,M.tangentAt_eq_incenterNormalAt z hz.2.1,
    real_inner_smul_left,inner_smul_right,complex_inner_rotate,
    L.incenterNormalAt_inner M z hz.1 hz.2.1] at he
  have hnL := norm_ne_zero_iff.mpr (L.tangentAt_ne_zero z)
  have hnM := norm_ne_zero_iff.mpr (M.tangentAt_ne_zero z)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hnL)).resolve_left hnM

theorem HalfPlaneLine.inwardNormalSign_sq (L : HalfPlaneLine) (z : ℍ) (hz : z ∉ L.carrier) :
    L.inwardNormalSign z ^ 2 = 1 := by
  have ht : L.normalTimeAt z ≠ 0 := by
    intro he
    exact hz ((L.normalTimeAt_eq_zero_iff z).mp he)
  rw [HalfPlaneLine.inwardNormalSign,div_pow,neg_sq,sq_abs,div_self (pow_ne_zero 2 ht)]

theorem HalfPlaneLine.inwardNormalSign_mul_time (L : HalfPlaneLine) (z : ℍ) :
    L.inwardNormalSign z * L.normalTimeAt z = -Real.sinh (L.pointDist z) := by
  rw [HalfPlaneLine.inwardNormalSign,neg_div,neg_mul,real_div_abs_mul_self,L.normalTimeAt_abs]

/-- Incidence of the second point with a side gives its exact transformed normal component. -/
theorem HalfPlaneLine.normalSpatialAt_inner_boost_point (L : HalfPlaneLine) (z w : ℍ)
    (hw : w ∈ L.carrier) :
    inner ℝ (L.normalSpatialAt z)
      (sideNormalBoost (halfPlanePointSpatial z) (halfPlaneKleinHeight z)
        (halfPlanePointSpatial w) (halfPlaneKleinHeight w)) =
      L.normalTimeAt z * Real.cosh (dist z w) := by
  have he := sideNormalBoost_inner (halfPlanePointSpatial z) (halfPlaneKleinHeight z)
    L.incenterNormal (halfPlanePointSpatial w) L.incenterOffset (halfPlaneKleinHeight w)
    (halfPlaneKleinHeight_lorentz_unit z) (ne_of_gt (by linarith [halfPlaneKleinHeight_pos z]))
  have ht := (L.normalTimeAt_eq_zero_iff w).mpr hw
  change halfPlaneKleinHeight w * L.incenterOffset -
    inner ℝ L.incenterNormal (halfPlanePointSpatial w) = 0 at ht
  rw [real_inner_comm (halfPlanePointSpatial z) (halfPlanePointSpatial w),
    halfPlanePoint_cosh_distance z w] at he
  change inner ℝ (L.normalSpatialAt z)
    (sideNormalBoost (halfPlanePointSpatial z) (halfPlaneKleinHeight z)
      (halfPlanePointSpatial w) (halfPlaneKleinHeight w)) =
    inner ℝ L.incenterNormal (halfPlanePointSpatial w) -
    L.incenterOffset * halfPlaneKleinHeight w + L.normalTimeAt z * Real.cosh (dist z w) at he
  linarith only [he,ht]

end LowDimensionalTopology.Geometry.Hyperbolic
