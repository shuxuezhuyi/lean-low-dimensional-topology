/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticRotationAngles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The literal entries of an elliptic lift are recovered from its actual center and trace. -/
theorem hSL_elliptic_center_coefficients (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    let v := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    A 0 0=Matrix.trace A.val/2+A 1 0*v.re ∧
    A 1 1=Matrix.trace A.val/2-A 1 0*v.re ∧
    A 0 1= -A 1 0*(v.re^2+v.im^2) ∧
    (Matrix.trace A.val/2)^2+(A 1 0*v.im)^2=1 ∧ A 1 0≠0 := by
  let ht := (realSLMobius_elliptic_iff A hA.1).mp hA
  let v := hEllipticCenter A ht
  obtain ⟨q,a,b,hu,hq,hb,hr⟩ := realSLMobius_elliptic_normal_form A hA
  have hv : A • v=v := (hSL_elliptic_fixed_iff A ht v).mpr rfl
  have hd := hSLDenom_at_rotation_center A q a b hu v hv hq hr
  have hre := congrArg Complex.re hd
  have him := congrArg Complex.im hd
  simp only [hSLDenom,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.conj_re] at hre
  simp only [hSLDenom,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero,Complex.conj_im] at him
  change A 1 0*v.re+A 1 1=a at hre
  change A 1 0*v.im= -b at him
  have htr : Matrix.trace A.val=2*a := by
    have he := hSL_trace_conjugation A q
    rw [hr] at he
    simpa [hRotationSL,Matrix.trace_fin_two,two_mul] using he.symm
  have h11 : A 1 1=Matrix.trace A.val/2-A 1 0*v.re := by linarith
  have h00 : A 0 0=Matrix.trace A.val/2+A 1 0*v.re := by
    have he : Matrix.trace A.val=A 0 0+A 1 1 := by rw [Matrix.trace_fin_two]
    linarith
  have hc : A 1 0≠0 := by intro hc;rw [hc,zero_mul] at him;exact hb (by linarith)
  have hunit : (Matrix.trace A.val/2)^2+(A 1 0*v.im)^2=1 := by
    rw [htr,him]
    nlinarith [hu]
  have h01 : A 0 1= -A 1 0*(v.re^2+v.im^2) := by
    have hd := A.det_coe
    rw [Matrix.det_fin_two,h00,h11] at hd
    have he : A 1 0*(A 0 1+A 1 0*(v.re^2+v.im^2))=0 := by nlinarith [hd,hunit]
    have he' := (mul_eq_zero.mp he).resolve_left hc
    linarith
  exact ⟨h00,h11,h01,hunit,hc⟩

/-- The exact trace uses the actual elliptic centers and their hyperbolic distance. -/
theorem hSL_elliptic_product_trace (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B)) :
    let u := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    let v := hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
    Matrix.trace ((A*B).val)/2 = (Matrix.trace A.val/2)*(Matrix.trace B.val/2)-
      Real.cosh (dist u v)*(A 1 0*u.im)*(B 1 0*v.im) := by
  let u := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
  obtain ⟨ha,hd,hb,_hu,_hc⟩ := hSL_elliptic_center_coefficients A hA
  obtain ⟨ha',hd',hb',_hu',_hc'⟩ := hSL_elliptic_center_coefficients B hB
  change Matrix.trace ((A*B).val)/2 = _-Real.cosh (dist u v)*(A 1 0*u.im)*(B 1 0*v.im)
  rw [UpperHalfPlane.cosh_dist']
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  rw [ha,hd,hb,ha',hd',hb']
  have hu : u.im≠0 := u.im_pos.ne'
  have hv : v.im≠0 := v.im_pos.ne'
  field_simp
  ring

/-- The lift sign is the only ambiguity in the true center-angle coefficients. -/
theorem hSL_elliptic_half_angle_coefficients (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    let v := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    let θ := hEllipticRotationAngle A hA/2
    (Matrix.trace A.val/2=Real.cos θ ∧ -A 1 0*v.im=Real.sin θ) ∨
    (Matrix.trace A.val/2= -Real.cos θ ∧ -A 1 0*v.im= -Real.sin θ) := by
  let v := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
  let θ := hEllipticRotationAngle A hA/2
  obtain ⟨_h00,h11,_h01,hu,_hc⟩ := hSL_elliptic_center_coefficients A hA
  let w : ℂ := ⟨Matrix.trace A.val/2,-A 1 0*v.im⟩
  have hD : hSLDenom A v=conj w := by
    apply Complex.ext
    · simp only [hSLDenom,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero,Complex.conj_re]
      change A 1 0*v.re+A 1 1=Matrix.trace A.val/2
      rw [h11]
      ring
    · simp only [hSLDenom,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,add_zero,Complex.conj_im]
      change A 1 0*v.im= -(-A 1 0*v.im)
      ring
  have hm : w*conj w=1 := by
    apply Complex.ext <;> simp only [w,Complex.mul_re,Complex.mul_im,Complex.conj_re,
      Complex.conj_im,Complex.one_re,Complex.one_im] <;> nlinarith [hu]
  have hi : 1/hSLDenom A v=w := by
    apply (div_eq_iff (hSLDenom_ne_zero A v)).mpr
    rw [hD]
    exact hm.symm
  have hd := (realSLMobius_hasDerivAt A v).unique (hEllipticRotationAngle_spec A hA).2.1
  have hpow : 1/hSLDenom A v^2=w^2 := by
    calc
      1/hSLDenom A v^2=(1/hSLDenom A v)^2 := by rw [div_pow,one_pow]
      _=w^2 := by rw [hi]
  rw [hpow] at hd
  have hsq : Complex.exp (Complex.I*θ)^2=Complex.exp (Complex.I*hEllipticRotationAngle A hA) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [θ]
    push_cast
    ring
  have hww : w=Complex.exp (Complex.I*θ) ∨ w= -Complex.exp (Complex.I*θ) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (hd.trans hsq.symm)
  rcases hww with hw | hw
  · left
    have hr := congrArg Complex.re hw
    have him := congrArg Complex.im hw
    simp [w,Complex.exp_re,Complex.exp_im] at hr him
    exact ⟨hr,by change -A 1 0*v.im=Real.sin θ;linarith⟩
  · right
    have hr := congrArg Complex.re hw
    have him := congrArg Complex.im hw
    simp [w,Complex.exp_re,Complex.exp_im] at hr him
    exact ⟨hr,by change -A 1 0*v.im= -Real.sin θ;linarith⟩

/-- The elliptic-product identity includes the necessary absolute value on the right-hand side. -/
theorem hElliptic_product_abs_trace (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B)) :
    let u := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    let v := hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
    let θ := hEllipticRotationAngle A hA/2
    let φ := hEllipticRotationAngle B hB/2
    |Matrix.trace ((A*B).val)|/2 =
      |Real.cosh (dist u v)*Real.sin θ*Real.sin φ-Real.cos θ*Real.cos φ| := by
  let u := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
  let θ := hEllipticRotationAngle A hA/2
  let φ := hEllipticRotationAngle B hB/2
  have he := hSL_elliptic_product_trace A B hA hB
  have ha := hSL_elliptic_half_angle_coefficients A hA
  have hb := hSL_elliptic_half_angle_coefficients B hB
  have hab : |Matrix.trace ((A*B).val)|/2=|Matrix.trace ((A*B).val)/2| := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  rw [hab,he]
  rcases ha with ⟨ha,hsa⟩ | ⟨ha,hsa⟩ <;> rcases hb with ⟨hb,hsb⟩ | ⟨hb,hsb⟩
  all_goals
    have hca : A 1 0*u.im= -( -A 1 0*u.im) := by ring
    have hcb : B 1 0*v.im= -( -B 1 0*v.im) := by ring
    rw [hca,hcb,hsa,hsb,ha,hb]
    apply abs_eq_abs.mpr
    solve | (left;ring) | (right;ring)

/-- The source half-angles are positive and strictly less than pi. -/
theorem hElliptic_halfAngle_mem_Ioo (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    hEllipticRotationAngle A hA/2 ∈ Ioo 0 Real.pi := by
  have hp := hEllipticRotationAngle_pos A hA
  have hu := (hEllipticRotationAngle_spec A hA).1.2
  constructor <;> linarith

/-- Elliptic maps with distinct actual centers cannot have identity product. -/
theorem hElliptic_product_ne_one_of_centers_ne (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B))
    (huv : hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)) : realSLMobius (A*B)≠1 := by
  let u := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
  have hau : A • u=u := (hSL_elliptic_fixed_iff A _ u).mpr rfl
  intro he
  have hab : (A*B) • u=u := by
    apply UpperHalfPlane.coe_injective
    apply OnePoint.coe_injective
    rw [← realSLMobius_action,he]
    rfl
  have hbu : B • u=u := by
    calc
      B • u=A⁻¹ • ((A*B) • u) := by simp only [mul_smul,inv_smul_smul]
      _=A⁻¹ • u := by rw [hab]
      _=u := by
        calc
          A⁻¹ • u=A⁻¹ • (A • u) := congrArg (fun z : ℍ=>A⁻¹ • z) hau.symm
          _=u := inv_smul_smul A u
  exact huv ((hSL_elliptic_fixed_iff B _ u).mp hbu)

/-- For distinct centers the signed source expression is strictly greater than minus one. -/
theorem hElliptic_product_expression_gt_neg_one (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B))
    (huv : hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)) :
    let u := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    let v := hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
    let θ := hEllipticRotationAngle A hA/2
    let φ := hEllipticRotationAngle B hB/2;
    -1 < Real.cosh (dist u v)*Real.sin θ*Real.sin φ-Real.cos θ*Real.cos φ := by
  let u := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
  let θ := hEllipticRotationAngle A hA/2
  let φ := hEllipticRotationAngle B hB/2
  have hθ := hElliptic_halfAngle_mem_Ioo A hA
  have hφ := hElliptic_halfAngle_mem_Ioo B hB
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  have hdist : 1 < Real.cosh (dist u v) := Real.one_lt_cosh.mpr (dist_ne_zero.mpr huv)
  have hc := Real.cos_le_one (θ+φ)
  rw [Real.cos_add] at hc
  have hpos := mul_pos (sub_pos.mpr hdist) (mul_pos hsθ hsφ)
  change -1 < Real.cosh (dist u v)*Real.sin θ*Real.sin φ-Real.cos θ*Real.cos φ
  nlinarith [hpos]

/-- The source parabolic-product criterion follows without its printed sign error. -/
theorem hElliptic_product_parabolic_iff (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B))
    (huv : hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)) :
    let u := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    let v := hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
    let θ := hEllipticRotationAngle A hA/2
    let φ := hEllipticRotationAngle B hB/2
    Mobius.MobiusParabolic (realSLMobius (A*B)) ↔
      Real.cosh (dist u v)=(1+Real.cos θ*Real.cos φ)/(Real.sin θ*Real.sin φ) := by
  let u := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
  let θ := hEllipticRotationAngle A hA/2
  let φ := hEllipticRotationAngle B hB/2
  have hθ := hElliptic_halfAngle_mem_Ioo A hA
  have hφ := hElliptic_halfAngle_mem_Ioo B hB
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  have hs : Real.sin θ*Real.sin φ≠0 := (mul_pos hsθ hsφ).ne'
  have htrace := hElliptic_product_abs_trace A B hA hB
  have hlow := hElliptic_product_expression_gt_neg_one A B hA hB huv
  rw [realSLMobius_parabolic_iff _ (hElliptic_product_ne_one_of_centers_ne A B hA hB huv)]
  change Matrix.trace ((A*B).val)^2=4 ↔ _
  rw [eq_div_iff hs]
  have ht : Matrix.trace ((A*B).val)^2=4 ↔ |Matrix.trace ((A*B).val)|/2=1 := by
    constructor <;> intro h <;> nlinarith [sq_abs (Matrix.trace ((A*B).val)),abs_nonneg (Matrix.trace ((A*B).val))]
  rw [ht,htrace]
  constructor
  · intro h
    rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp h with he | he <;> nlinarith
  · intro h
    have he : Real.cosh (dist u v)*Real.sin θ*Real.sin φ-Real.cos θ*Real.cos φ=1 := by nlinarith
    rw [he,abs_one]

/-- Actual admissible center and angle data make the uncorrected printed expression negative. -/
theorem hElliptic_product_printed_rhs_counterexample :
    Real.cosh (dist UpperHalfPlane.I (metricProbe 0 2 (by norm_num)))*
      Real.sin (Real.pi/6)*Real.sin (Real.pi/6)-
      Real.cos (Real.pi/6)*Real.cos (Real.pi/6)= -(7/16 : ℝ) := by
  rw [UpperHalfPlane.cosh_dist',Real.sin_pi_div_six]
  have hc : Real.cos (Real.pi/6)*Real.cos (Real.pi/6)=(3/4 : ℝ) := by
    simpa only [pow_two] using Real.sq_cos_pi_div_six
  rw [hc]
  norm_num [metricProbe,UpperHalfPlane.I_re,UpperHalfPlane.I_im]

/-- The corrected trace formula is also expressed entirely in the original actual group invariant. -/
theorem hElliptic_product_actual_trace_magnitude (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B)) :
    let u := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    let v := hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
    let θ := hEllipticRotationAngle A hA/2
    let φ := hEllipticRotationAngle B hB/2
    Real.sqrt ‖Mobius.mobiusSquaredTrace (realSLMobius A*realSLMobius B)‖/2 =
      |Real.cosh (dist u v)*Real.sin θ*Real.sin φ-Real.cos θ*Real.cos φ| := by
  rw [← map_mul,realSLMobius_squaredTrace,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _),Real.sqrt_sq_eq_abs]
  exact hElliptic_product_abs_trace A B hA hB

end LowDimensionalTopology.Geometry.Hyperbolic
