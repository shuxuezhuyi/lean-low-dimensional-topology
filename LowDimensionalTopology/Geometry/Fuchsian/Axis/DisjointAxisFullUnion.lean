/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.DisjointAxisConstraints
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.CrossingAxisConstraints
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.DisjointAxisReflectionGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleHyperbolicAxisSeparation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane MatrixGroups OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual diagonal difference used in the native axis-distance formula. -/
def axisDiagonalDifference (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℝ := B 0 0-B 1 1

/-- The exact three-step conjugation recurrence for the actual two-by-two matrices.
The nearest-axis estimate uses this recurrence to compare successive conjugates. -/
theorem axisDiagonalDifference_conjugate_recurrence
    (B C : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    axisDiagonalDifference (C^3*B*(C⁻¹)^3) -
      ((Matrix.trace C.val)^2-1)*axisDiagonalDifference (C^2*B*(C⁻¹)^2) +
      ((Matrix.trace C.val)^2-1)*axisDiagonalDifference (C*B*C⁻¹) -
      axisDiagonalDifference B = 0 := by
  have hd:=C.det_coe
  rw [Matrix.det_fin_two] at hd
  norm_num [axisDiagonalDifference,pow_succ,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.SpecialLinearGroup.coe_one,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.trace_fin_two]
  linear_combination (-(B 0 0)*(C 0 0)^3*(C 1 1) - 3*(B 0 0)*(C 0 0)^2*(C 0 1)*(C 1 0) - (B 0 0)*(C 0 0)^2*(C 1 1)^2 -
    6*(B 0 0)*(C 0 0)*(C 0 1)*(C 1 0)*(C 1 1) - (B 0 0)*(C 0 0)*(C 1 1)^3 + 2*(B 0 0)*(C 0 0)*(C 1 1) - (B 0 0)*(C 0
    1)^2*(C 1 0)^2 - 3*(B 0 0)*(C 0 1)*(C 1 0)*(C 1 1)^2 + (B 0 0) + 4*(B 0 1)*(C 0 0)^3*(C 1 0) + 4*(B 0 1)*(C 0
    0)^2*(C 1 0)*(C 1 1) + 4*(B 0 1)*(C 0 0)*(C 0 1)*(C 1 0)^2 + 2*(B 0 1)*(C 0 0)*(C 1 0)*(C 1 1)^2 - 2*(B 0 1)*(C 0
    0)*(C 1 0) + 2*(B 0 1)*(C 0 1)*(C 1 0)^2*(C 1 1) - 2*(B 1 0)*(C 0 0)^2*(C 0 1)*(C 1 1) - 2*(B 1 0)*(C 0 0)*(C 0
    1)^2*(C 1 0) - 4*(B 1 0)*(C 0 0)*(C 0 1)*(C 1 1)^2 - 4*(B 1 0)*(C 0 1)^2*(C 1 0)*(C 1 1) - 4*(B 1 0)*(C 0 1)*(C 1
    1)^3 + 2*(B 1 0)*(C 0 1)*(C 1 1) + (B 1 1)*(C 0 0)^3*(C 1 1) + 3*(B 1 1)*(C 0 0)^2*(C 0 1)*(C 1 0) + (B 1 1)*(C 0
    0)^2*(C 1 1)^2 + 6*(B 1 1)*(C 0 0)*(C 0 1)*(C 1 0)*(C 1 1) + (B 1 1)*(C 0 0)*(C 1 1)^3 - 2*(B 1 1)*(C 0 0)*(C 1 1) +
    (B 1 1)*(C 0 1)^2*(C 1 0)^2 + 3*(B 1 1)*(C 0 1)*(C 1 0)*(C 1 1)^2 - (B 1 1))*hd


/-- The two-step nearest-axis diagonal difference is an exact actual matrix identity. -/
theorem axisDiagonalDifference_disjoint_step_two
    (t : ℝ) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    let C := hLogDilationSL t * B⁻¹
    let q := Matrix.trace C.val / 2
    let D := Matrix.trace B.val / 2
    Real.sinh t *
      (axisDiagonalDifference (C^2*B*(C⁻¹)^2)-axisDiagonalDifference B) +
      8*q*(Real.cosh t^2+D^2-1+q^2-2*q*Real.cosh t*D)=0 := by
  dsimp only
  have hd:=B.det_coe
  rw [Matrix.det_fin_two] at hd
  have hd' : B 0 1*B 1 0-B 0 0*B 1 1+1=0 := by linarith
  have ht:=Real.cosh_sq_sub_sinh_sq t
  have he1 : Real.exp t=Real.cosh t+Real.sinh t := by
    rw [Real.cosh_eq,Real.sinh_eq]
    ring
  have he2 : Real.exp (-t)=Real.cosh t-Real.sinh t := by
    rw [Real.cosh_eq,Real.sinh_eq]
    ring
  norm_num only [axisDiagonalDifference,pow_succ,pow_zero,
    Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_one,hLogDilationSL,Matrix.adjugate_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.trace_fin_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Matrix.one_apply,Fin.isValue,zero_add,add_zero,zero_mul,mul_zero,mul_one,one_mul,
    sub_zero,neg_zero,neg_neg]
  rw [he1,he2]
  linear_combination (-(Real.sinh t)*((Real.cosh t) - (Real.sinh t))*((Real.cosh t) + (Real.sinh t))*((B 0
    0)^2*(Real.cosh t)^2*(B 1 1) - (B 0 0)^2*(B 1 1)*(Real.sinh t)^2 - (B 0 0)*(B 0 1)*(B 1 0)*(Real.cosh t)^2 + 4*(B 0
    0)*(B 0 1)*(B 1 0)*(Real.cosh t)*(Real.sinh t) - 3*(B 0 0)*(B 0 1)*(B 1 0)*(Real.sinh t)^2 - (B 0 0)*(Real.cosh
    t)^2*(B 1 1)^2 + (B 0 0)*(Real.cosh t)^2 - 4*(B 0 0)*(Real.cosh t)*(Real.sinh t) + (B 0 0)*(B 1 1)^2*(Real.sinh t)^2
    + 3*(B 0 0)*(Real.sinh t)^2 + (B 0 1)*(B 1 0)*(Real.cosh t)^2*(B 1 1) + 4*(B 0 1)*(B 1 0)*(Real.cosh t)*(B 1
    1)*(Real.sinh t) + 3*(B 0 1)*(B 1 0)*(B 1 1)*(Real.sinh t)^2 - (Real.cosh t)^2*(B 1 1) - 4*(Real.cosh t)*(B 1
    1)*(Real.sinh t) - 3*(B 1 1)*(Real.sinh t)^2))*hd' + (-(B 0 0)^3*(Real.cosh t) + (B 0 0)^3*(Real.sinh t) + 4*(B 0
    0)^2*(Real.cosh t)*(B 1 1)*(Real.sinh t)^2 - 3*(B 0 0)^2*(Real.cosh t)*(B 1 1) - 4*(B 0 0)^2*(B 1 1)*(Real.sinh t)^3
    + (B 0 0)^2*(B 1 1)*(Real.sinh t) + (B 0 0)*(Real.cosh t)^2*(Real.sinh t) + 4*(B 0 0)*(Real.cosh t)*(B 1
    1)^2*(Real.sinh t)^2 - 3*(B 0 0)*(Real.cosh t)*(B 1 1)^2 - 4*(B 0 0)*(Real.cosh t)*(Real.sinh t)^2 + 4*(B 0
    0)*(Real.cosh t) + 4*(B 0 0)*(B 1 1)^2*(Real.sinh t)^3 - (B 0 0)*(B 1 1)^2*(Real.sinh t) + 3*(B 0 0)*(Real.sinh t)^3
    - 3*(B 0 0)*(Real.sinh t) - (Real.cosh t)^2*(B 1 1)*(Real.sinh t) - (Real.cosh t)*(B 1 1)^3 - 4*(Real.cosh t)*(B 1
    1)*(Real.sinh t)^2 + 4*(Real.cosh t)*(B 1 1) - (B 1 1)^3*(Real.sinh t) - 3*(B 1 1)*(Real.sinh t)^3 + 3*(B 1
    1)*(Real.sinh t))*ht


/-- The exact bad-gap diagonal recurrences force one of two strictly closer
coefficient candidates. The genuine axis argument supplies these identities. -/
theorem disjointAxis_bad_gap_diagonal_candidates
    (ca sa D q delta delta2 delta3 : ℝ)
    (hca : 1 ≤ ca) (hsa : 0 < sa) (hcs : ca^2-sa^2=1)
    (hD : 1 ≤ D) (hDca : D ≤ ca) (hdelta : 2*D ≤ delta)
    (hrel : sa*delta=2*(ca*D-q)) (hq : 1/2 < q) (hq1 : q < 1)
    (hstep2 : sa*(delta2-delta)+8*q*(ca^2+D^2-1+q^2-2*q*ca*D)=0)
    (hstep3 : delta3-(4*q^2-1)*delta2+(4*q^2-2)*delta=0) :
    (1/2 ≤ q^2 ∧ |delta2| < delta) ∨ (q^2 ≤ 1/2 ∧ |delta3| < delta) := by
  have hcap : 0 < ca := by linarith
  have hDp : 0 < D := by linarith
  have hqpos : 0 < q := by linarith
  have hqq : 0 < 1-q^2 := by nlinarith
  have hcas : sa < ca := by nlinarith
  have hsmall : ca*(ca-sa) < 1 := by
    have hp := mul_pos hsa (sub_pos.mpr hcas)
    nlinarith
  have hqd : q ≤ (ca-sa)*D := by
    have hm:=mul_le_mul_of_nonneg_left hdelta hsa.le
    nlinarith only [hm,hrel]
  have hcaq : ca*q < D := by
    calc
      ca*q ≤ ca*((ca-sa)*D) := mul_le_mul_of_nonneg_left hqd hcap.le
      _ = (ca*(ca-sa))*D := by ring
      _ < 1*D := mul_lt_mul_of_pos_right hsmall hDp
      _ = D := one_mul D
  have hcd : 0 < ca-q*D := by
    have hm:=mul_lt_mul_of_pos_right hq1 hDp
    nlinarith only [hm,hDca]
  let R := ca^2+D^2-1+q^2-2*q*ca*D
  have hR : 0 < R := by
    have he : R=(ca-q*D)^2+(1-q^2)*(D^2-1) := by dsimp only [R];ring
    rw [he]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hcd)
      (mul_nonneg hqq.le (by nlinarith [hD]))
  let den := sa*(1-q^2)
  have hden : 0 < den := mul_pos hsa hqq
  let beta := 2*q*R/den
  have hbeta : 0 < beta := div_pos (by positivity) hden
  have hb : den*beta=2*q*R := by
    dsimp only [beta]
    exact mul_div_cancel₀ _ hden.ne'
  let X := delta-beta
  have hx : den*X = -2*(ca-q*D)*(ca*q-D) := by
    dsimp only [X]
    rw [mul_sub,hb]
    dsimp only [den,R]
    linear_combination (1-q^2)*hrel
  have hX : 0 < X := by
    have hp : 0 < -2*(ca-q*D)*(ca*q-D) :=
      mul_pos_of_neg_of_neg (by nlinarith only [hcd]) (by linarith only [hcaq])
    rw [←hx] at hp
    exact (mul_pos_iff_of_pos_left hden).mp hp
  have hd : delta=X+beta := by dsimp only [X];ring
  have hd2 : delta2=X+beta*(4*q^2-3) := by
    apply (mul_left_cancel₀ hsa.ne')
    dsimp only [X]
    dsimp only [den,R] at hb
    linear_combination hstep2+4*hb
  have hd3 : delta3=X+beta*(16*q^4-20*q^2+5) := by
    rw [hd2,hd] at hstep3
    linear_combination hstep3
  have hbound (r y : ℝ) (hr0 : -1 ≤ r) (hr1 : r < 1)
      (hy : y=X+beta*r) : |y| < delta := by
    rw [hy,hd,abs_lt]
    have hlo := mul_nonneg hbeta.le (show 0 ≤ r+1 by linarith)
    have hhi := mul_pos hbeta (show 0 < 1-r by linarith)
    constructor <;> nlinarith only [hX,hlo,hhi]
  by_cases hs : 1/2 ≤ q^2
  · refine Or.inl ⟨hs,hbound (4*q^2-3) delta2 ?_ ?_ hd2⟩
    · linarith only [hs]
    · linarith only [hqq]
  · have hs' : q^2 ≤ 1/2 := (lt_of_not_ge hs).le
    refine Or.inr ⟨hs',hbound (16*q^4-20*q^2+5) delta3 ?_ ?_ hd3⟩
    · have hp := mul_nonneg (show 0 ≤ 1/2-q^2 by linarith) (show 0 ≤ 3/4-q^2 by linarith)
      nlinarith only [hp]
    · have hq4 : 1/4 < q^2 := by nlinarith only [hq]
      have hp := mul_pos (show 0 < 4*q^2-1 by linarith) hqq
      nlinarith only [hp]


/-- The first actual conjugate has unchanged diagonal difference. -/
theorem axisDiagonalDifference_disjoint_step_one
    (t : ℝ) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    let C := hLogDilationSL t * B⁻¹
    axisDiagonalDifference (C*B*C⁻¹)=axisDiagonalDifference B := by
  dsimp only
  have he : (hLogDilationSL t*B⁻¹)*B*(hLogDilationSL t*B⁻¹)⁻¹=
      hLogDilationSL t*B*(hLogDilationSL t)⁻¹ := by group
  rw [he]
  norm_num only [axisDiagonalDifference,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,hLogDilationSL,Matrix.adjugate_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,Fin.isValue,zero_add,add_zero,
    zero_mul,mul_zero,mul_one,one_mul,sub_zero,neg_zero,neg_neg]
  have he' : Real.exp t*Real.exp (-t)=1 := by rw [←Real.exp_add];simp
  linear_combination (B 0 0-B 1 1)*he'

/-- The genuine second-power off-diagonal entries. -/
theorem axisGap_square_offdiagonal (C : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (C^2) 0 1=Matrix.trace C.val*C 0 1 ∧
    (C^2) 1 0=Matrix.trace C.val*C 1 0 := by
  norm_num [pow_two,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,
    Fin.sum_univ_two,Matrix.trace_fin_two]
  constructor <;> ring

/-- The genuine third-power off-diagonal entries. -/
theorem axisGap_cube_offdiagonal (C : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (C^3) 0 1=((Matrix.trace C.val)^2-1)*C 0 1 ∧
    (C^3) 1 0=((Matrix.trace C.val)^2-1)*C 1 0 := by
  have hd:=C.det_coe
  rw [Matrix.det_fin_two] at hd
  norm_num [pow_succ,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.trace_fin_two]
  constructor
  · linear_combination -(C 0 1)*hd
  · linear_combination -(C 1 0)*hd


/-- A genuine elliptic with nonzero trace cannot preserve the actual
vertical geodesic, whose only elliptic preservers are half-turns. -/
theorem axisGap_elliptic_nonzero_not_preserve_axis0
    (C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : (Matrix.trace C.val)^2<4) (hz : Matrix.trace C.val≠0) :
    (C • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier≠
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  intro he
  have hpair:=hSL_axis0_preserver_mem_pairStabilizer C he
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C≠1 := by
    intro hi
    have hs:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_sq_of_projection_one C hi
    linarith
  rcases _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_zeroInftyPair_cases ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C,hpair⟩ with hf|hs
  · have hc : C 1 0=0 := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff C).mp hf.2
    have hd:=C.det_coe
    rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at hd
    rw [Matrix.trace_fin_two] at ht
    nlinarith [sq_nonneg (C 0 0-C 1 1)]
  · have he2:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_endpoint_exchange_square (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) hs.1 hs.2
    have ho : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)=2 :=
      orderOf_eq_prime (by simpa only [pow_two] using he2) hn
    exact hz ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_order_two_iff_trace_zero C hn).mp ho)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
set_option maxHeartbeats 200000
local notation "L₀" => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (0:ℝ)

/-- The genuine geodesic image used by the corrected full-union consumer. -/
def axisGapLineImage (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (F :
  Matrix.SpecialLinearGroup (Fin 2) ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine :=
  L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F)

theorem axisGapLineImage_mul (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (F G : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    axisGapLineImage L (F*G)=axisGapLineImage (axisGapLineImage L G) F := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
  simp only [axisGapLineImage,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
  change ((F*G) • · : ℍ→ℍ) '' L.carrier=
    (F • · : ℍ→ℍ) '' ((G • · : ℍ→ℍ) '' L.carrier)
  rw [image_image]
  congr 1
  funext z
  exact mul_smul F G z

theorem axisGapLineImage_injective (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Function.Injective (fun L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine=>axisGapLineImage L F) := by
  intro L M he
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
  apply Set.image_injective.mpr (MulAction.injective (Matrix.SpecialLinearGroup.mapGL ℝ F))
  have hc:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier he
  simpa only [axisGapLineImage,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier] using hc

theorem axisGapLineImage_lineDist (L M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (axisGapLineImage L F).lineDist (axisGapLineImage M F)=L.lineDist M := by
  apply L.lineDist_isometry_image M _ _ (F • ·) (isometry_smul ℍ F)
  · rw [axisGapLineImage,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  · rw [axisGapLineImage,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl

theorem axisGap_logDilationAxisImage (t : ℝ) (ht : 0<t)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    logDilationAxisImage t hA htA F=axisGapLineImage L₀ F := by
  dsimp only [logDilationAxisImage,axisGapLineImage]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation (hLogDilationSL t) F hA htA,
    hLogDilationSL_hyperbolic_axis t ht hA htA]

theorem axisGapLineImage_cosh (t : ℝ) (ht : 0<t)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd : (L₀).HDisjoint (axisGapLineImage L₀ F)) :
    Real.cosh ((L₀).lineDist (axisGapLineImage L₀ F))=
      |F 0 0*F 1 1+F 0 1*F 1 0| := by
  have hdi : (L₀).HDisjoint (logDilationAxisImage t hA htA F) := by
    rwa [axisGap_logDilationAxisImage t ht hA htA F]
  have hc:=logDilation_axis_image_cosh t ht hA htA F hdi
  change Real.cosh ((L₀).lineDist (logDilationAxisImage t hA htA F))=_ at hc
  rwa [axisGap_logDilationAxisImage t ht hA htA F] at hc

theorem axisGap_elliptic_offdiagonal_neg (C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : (Matrix.trace C.val)^2<4) : C 0 1*C 1 0<0 := by
  have hd:=C.det_coe
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two] at ht
  nlinarith only [hd,ht,sq_nonneg (C 0 0-C 1 1)]

theorem axisGap_negative_sum_of_negative_offdiagonal
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) (d : ℝ)
    (hu : F 0 1*F 1 0<0)
    (hd : Real.cosh d=|F 0 0*F 1 1+F 0 1*F 1 0|) :
    F 0 0*F 1 1+F 0 1*F 1 0<0 := by
  have hdet:=F.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hc:=Real.one_le_cosh d
  by_contra hn
  rw [abs_of_nonneg (le_of_not_gt hn)] at hd
  nlinarith only [hdet,hu,hd,hc]

/-- Equal genuine simple-axis distances give an equality of the actual
off-diagonal products; no coefficient equality is supplied. -/
theorem axisGap_equal_axis0_dist_offdiagonal
    (t : ℝ) (ht : 0<t)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (F G : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hF : (L₀).HDisjoint (axisGapLineImage L₀ F))
    (hG : (L₀).HDisjoint (axisGapLineImage L₀ G))
    (huF : F 0 1*F 1 0<0) (huG : G 0 1*G 1 0<0)
    (he : (L₀).lineDist (axisGapLineImage L₀ F)=(L₀).lineDist (axisGapLineImage L₀ G)) :
    F 0 1*F 1 0=G 0 1*G 1 0 := by
  have hcF:=axisGapLineImage_cosh t ht hA htA F hF
  have hcG:=axisGapLineImage_cosh t ht hA htA G hG
  have hsF:=axisGap_negative_sum_of_negative_offdiagonal F _ huF hcF
  have hsG:=axisGap_negative_sum_of_negative_offdiagonal G _ huG hcG
  rw [abs_of_neg hsF,he] at hcF
  rw [abs_of_neg hsG] at hcG
  have hdF:=F.det_coe
  have hdG:=G.det_coe
  rw [Matrix.det_fin_two] at hdF hdG
  nlinarith only [hcF,hcG,hdF,hdG]

theorem axisGap_square_axis0_distance_ne
    (t : ℝ) (ht : 0<t)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hlo : 1<Matrix.trace C.val) (hhi : Matrix.trace C.val<2)
    (hC : (L₀).HDisjoint (axisGapLineImage L₀ C))
    (hC2 : (L₀).HDisjoint (axisGapLineImage L₀ (C^2))) :
    (L₀).lineDist (axisGapLineImage L₀ (C^2))≠(L₀).lineDist (axisGapLineImage L₀ C) := by
  have hu:=axisGap_elliptic_offdiagonal_neg C (by nlinarith only [hlo,hhi])
  have hp:=axisGap_square_offdiagonal C
  have hprod : (C^2) 0 1*(C^2) 1 0=(Matrix.trace C.val)^2*(C 0 1*C 1 0) := by
    rw [hp.1,hp.2]
    ring
  have hu2 : (C^2) 0 1*(C^2) 1 0<0 := by
    rw [hprod]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos (by linarith only [hlo])) hu
  intro he
  have hpEq:=axisGap_equal_axis0_dist_offdiagonal t ht hA htA (C^2) C hC2 hC hu2 hu he
  rw [hprod] at hpEq
  have hfactor : (Matrix.trace C.val)^2=1 := by
    apply mul_right_cancel₀ hu.ne
    simpa only [one_mul] using hpEq
  nlinarith only [hfactor,hlo]

theorem axisGap_cube_axis0_distance_ne
    (t : ℝ) (ht : 0<t)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hlo : 1<Matrix.trace C.val) (hhi : (Matrix.trace C.val)^2≤2)
    (hC2 : (L₀).HDisjoint (axisGapLineImage L₀ (C^2)))
    (hC3 : (L₀).HDisjoint (axisGapLineImage L₀ (C^3))) :
    (L₀).lineDist (axisGapLineImage L₀ (C^3))≠(L₀).lineDist (axisGapLineImage L₀ (C^2)) := by
  have hu:=axisGap_elliptic_offdiagonal_neg C (by linarith only [hhi])
  have hsq : 1<(Matrix.trace C.val)^2 := by nlinarith only [hlo]
  have hp2:=axisGap_square_offdiagonal C
  have hp3:=axisGap_cube_offdiagonal C
  have hprod2 : (C^2) 0 1*(C^2) 1 0=(Matrix.trace C.val)^2*(C 0 1*C 1 0) := by
    rw [hp2.1,hp2.2]
    ring
  have hprod3 : (C^3) 0 1*(C^3) 1 0=((Matrix.trace C.val)^2-1)^2*(C 0 1*C 1 0) := by
    rw [hp3.1,hp3.2]
    ring
  have hu2 : (C^2) 0 1*(C^2) 1 0<0 := by
    rw [hprod2]
    exact mul_neg_of_pos_of_neg (by linarith only [hsq]) hu
  have hu3 : (C^3) 0 1*(C^3) 1 0<0 := by
    rw [hprod3]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos (by linarith only [hsq])) hu
  intro he
  have hpEq:=axisGap_equal_axis0_dist_offdiagonal t ht hA htA (C^3) (C^2) hC3 hC2 hu3 hu2 he
  rw [hprod2,hprod3] at hpEq
  have hfactor : ((Matrix.trace C.val)^2-1)^2=(Matrix.trace C.val)^2 :=
    mul_right_cancel₀ hu.ne hpEq
  have hp:=mul_nonneg (show 0≤(Matrix.trace C.val)^2-1 by linarith only [hsq])
    (show 0≤2-(Matrix.trace C.val)^2 by linarith only [hhi])
  nlinarith only [hfactor,hp]

/-- A hypothetical return of the partner axis gives two equal genuine
self-family distances and two distinct actual images. -/
theorem axisGap_coincidence_data (L M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (A C : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℕ)
    (hAL : axisGapLineImage L A=L) (hne : L≠M)
    (hCM : axisGapLineImage M C=axisGapLineImage M A)
    (he : axisGapLineImage M (C^(k+1))=L) :
    L≠axisGapLineImage L (C^(k+1)) ∧ L≠axisGapLineImage L (C^k) ∧
      L.lineDist (axisGapLineImage L (C^(k+1)))=L.lineDist (axisGapLineImage L (C^k)) := by
  have hneCM : L≠axisGapLineImage M C := by
    intro h
    have hi : axisGapLineImage M A=axisGapLineImage L A :=
      hCM.symm.trans (h.symm.trans hAL.symm)
    exact hne ((axisGapLineImage_injective A hi).symm)
  have hek : axisGapLineImage (axisGapLineImage M C) (C^k)=L := by
    rw [←axisGapLineImage_mul,←pow_succ]
    exact he
  have hBig : L≠axisGapLineImage L (C^(k+1)) := by
    intro h
    exact hne ((axisGapLineImage_injective (C^(k+1)) (he.trans h)).symm)
  have hSmall : L≠axisGapLineImage L (C^k) := by
    intro h
    exact hneCM ((axisGapLineImage_injective (C^k) (hek.trans h)).symm)
  refine ⟨hBig,hSmall,?_⟩
  have hBigDist:=axisGapLineImage_lineDist L M (C^(k+1))
  rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.lineDist_comm] at hBigDist
  have hSmallDist:=axisGapLineImage_lineDist L (axisGapLineImage M C) (C^k)
  rw [hek,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.lineDist_comm] at hSmallDist
  have hADist:=axisGapLineImage_lineDist L M A
  rw [hAL,←hCM] at hADist
  exact hBigDist.trans (hADist.symm.trans hSmallDist.symm)

theorem axisGapLineImage_one (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    axisGapLineImage L 1=L := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
  simp only [axisGapLineImage,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
  change ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • · : ℍ→ℍ) '' L.carrier=L.carrier
  simp

theorem axisGapLineImage_inverse_fix (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hF : axisGapLineImage L F=L) :
    axisGapLineImage L F⁻¹=L := by
  have hi:=axisGapLineImage_mul L F⁻¹ F
  rw [inv_mul_cancel,axisGapLineImage_one,hF] at hi
  exact hi.symm

theorem axisGapLineImage_hyperbolic_fix
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2) :
    axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) B=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
  rw [axisGapLineImage,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
  change (B • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier=_
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_invariant B hB htB

theorem axisGapLineImage_dilation_fix (t : ℝ) (ht : 0<t)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2) :
    axisGapLineImage L₀ (hLogDilationSL t)=L₀ := by
  have hf:=axisGapLineImage_hyperbolic_fix (hLogDilationSL t) hA htA
  rwa [hLogDilationSL_hyperbolic_axis t ht hA htA] at hf

theorem axisGapLineImage_partner (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1) (htB : 4<(Matrix.trace B.val)^2) :
    axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) (A*B⁻¹)=
      axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) A := by
  rw [axisGapLineImage_mul,axisGapLineImage_inverse_fix _ B
    (axisGapLineImage_hyperbolic_fix B hB htB)]

theorem HalfPlaneFuchsianGroup.axisGap_simple_image_hDisjoint
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (t : ℝ) (ht : 0<t) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)))
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∈H)
    (hne : L₀≠axisGapLineImage L₀ F) :
    (L₀).HDisjoint (axisGapLineImage L₀ F) := by
  have hne' : L₀≠logDilationAxisImage t hA htA F := by
    rwa [axisGap_logDilationAxisImage t ht hA htA F]
  have hd:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_logDilation_image_hDisjoint P t ht hA htA hs F hF hne'
  change (L₀).HDisjoint (logDilationAxisImage t hA htA F) at hd
  rwa [axisGap_logDilationAxisImage t ht hA htA F] at hd

/-- Actual simplicity excludes the two-step return of the partner axis.
All self-family separation and coefficient information is derived internally. -/
theorem HalfPlaneFuchsianGroup.axisGap_partner_square_ne
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (t : ℝ) (ht : 0<t) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)))
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2) (hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hne : L₀≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
    (hlo : 1<Matrix.trace (hLogDilationSL t*B⁻¹).val)
    (hhi : Matrix.trace (hLogDilationSL t*B⁻¹).val<2) :
    axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) ((hLogDilationSL t*B⁻¹)^2)≠L₀ := by
  let C:=hLogDilationSL t*B⁻¹
  have hCm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈H := by
    dsimp only [C]
    rw [map_mul,map_inv]
    exact H.mul_mem hs.1 (H.inv_mem hBm)
  intro he
  have hd:=axisGap_coincidence_data L₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
    (hLogDilationSL t) C 1 (axisGapLineImage_dilation_fix t ht hA htA) hne
    (axisGapLineImage_partner (hLogDilationSL t) B hB htB) he
  have hd2:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_simple_image_hDisjoint P t ht hA htA hs (C^2)
    (by rw [map_pow]; exact H.pow_mem hCm 2) hd.1
  have hd1:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_simple_image_hDisjoint P t ht hA htA hs C hCm
    (by simpa only [pow_one] using hd.2.1)
  exact axisGap_square_axis0_distance_ne t ht hA htA C hlo hhi hd1 hd2
    (by simpa only [pow_one] using hd.2.2)

/-- Actual simplicity likewise excludes the three-step return in the small-trace branch. -/
theorem HalfPlaneFuchsianGroup.axisGap_partner_cube_ne
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (t : ℝ) (ht : 0<t) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)))
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2) (hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hne : L₀≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
    (hlo : 1<Matrix.trace (hLogDilationSL t*B⁻¹).val)
    (hhi : (Matrix.trace (hLogDilationSL t*B⁻¹).val)^2≤2) :
    axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) ((hLogDilationSL t*B⁻¹)^3)≠L₀ := by
  let C:=hLogDilationSL t*B⁻¹
  have hCm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈H := by
    dsimp only [C]
    rw [map_mul,map_inv]
    exact H.mul_mem hs.1 (H.inv_mem hBm)
  intro he
  have hd:=axisGap_coincidence_data L₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
    (hLogDilationSL t) C 2 (axisGapLineImage_dilation_fix t ht hA htA) hne
    (axisGapLineImage_partner (hLogDilationSL t) B hB htB) he
  have hd3:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_simple_image_hDisjoint P t ht hA htA hs (C^3)
    (by rw [map_pow]; exact H.pow_mem hCm 3) hd.1
  have hd2:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_simple_image_hDisjoint P t ht hA htA hs (C^2)
    (by rw [map_pow]; exact H.pow_mem hCm 2) hd.2.1
  exact axisGap_cube_axis0_distance_ne t ht hA htA C hlo hhi hd2 hd3 hd.2.2

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local notation "L₀" => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (0:ℝ)

theorem axisGap_product_inverse_trace (t : ℝ)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (hLogDilationSL t*B⁻¹).val/2=
      Real.cosh t*(Matrix.trace B.val/2)-Real.sinh t*(axisDiagonalDifference B/2) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  change (Real.exp t*B 1 1+0*(-B 1 0)+(0*(-B 0 1)+Real.exp (-t)*B 0 0))/2=_
  rw [Real.cosh_eq,Real.sinh_eq]
  dsimp only [axisDiagonalDifference]
  ring

/-- The genuine nearest-axis property bounds each actual conjugate diagonal difference. -/
theorem HalfPlaneFuchsianGroup.axisGap_nearest_diagonal_lower
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (t : ℝ) (ht : 0<t) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)∈H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2) (hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hd : (L₀).HDisjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (hdelta : 0<axisDiagonalDifference B)
    (hno : HyperbolicAxisFamiliesNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis
      (hLogDilationSL t) hA htA)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (hmin : ∀F : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∈H→
      L₀≠axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) F→
      (L₀).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)≤
        (L₀).lineDist (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) F))
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∈H)
    (hne : L₀≠axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) F) :
    axisDiagonalDifference B≤|axisDiagonalDifference (F*B*F⁻¹)| := by
  let K:=F*B*F⁻¹
  have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius K≠1:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation B F hB
  have htK : 4<(Matrix.trace K.val)^2 := by dsimp only [K];rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have haxis : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis K hK htK=axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) F :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation B F hB htB
  have hne' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (hLogDilationSL t) hA htA≠
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F) := by
    rwa [hLogDilationSL_hyperbolic_axis t ht hA htA]
  have hdF:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.noncrossing_axis_image_hDisjoint P
    (hLogDilationSL t) B hAm hBm hA hB htA htB hno F hF hne'
  rw [hLogDilationSL_hyperbolic_axis t ht hA htA] at hdF
  have hdK : (L₀).HDisjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis K hK htK) := by rwa [haxis]
  have hcB:=hHyperbolic_axis0_distance_translation_product B hB htB hd
  have hcK:=hHyperbolic_axis0_distance_translation_product K hK htK hdK
  have hlen : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation B F
  rw [hlen,haxis] at hcK
  have hc : Real.cosh ((L₀).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))≤
      Real.cosh ((L₀).lineDist (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) F)) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg ((L₀).lineDist_nonneg _),abs_of_nonneg ((L₀).lineDist_nonneg _)]
    exact hmin F hF hne
  have hp : 0<Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) :=
    Real.sinh_pos_iff.mpr (by linarith only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos B hB htB])
  have hm:=mul_le_mul_of_nonneg_right hc hp.le
  change _=|axisDiagonalDifference B|/2 at hcB
  change _=|axisDiagonalDifference K|/2 at hcK
  rw [abs_of_pos hdelta] at hcB
  dsimp only [K] at hcK
  linarith only [hm,hcB,hcK]

/-- The original finite recurrence now proves the normalized nearest weak bound,
with actual simplicity supplying the missing coincidence exclusion. -/
theorem HalfPlaneFuchsianGroup.axisGap_nearest_positive_weak
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (t : ℝ) (ht : 0<t) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)))
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2) (hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hd : (L₀).HDisjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (htrace : 2<Matrix.trace B.val) (hdelta : 0<axisDiagonalDifference B)
    (hT : Matrix.trace B.val/2≤Real.cosh t)
    (hno : HyperbolicAxisFamiliesNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis
      (hLogDilationSL t) hA htA)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (hmin : ∀F : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∈H→
      L₀≠axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) F→
      (L₀).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)≤
        (L₀).lineDist (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
          F)) :
    Real.cosh t*(Matrix.trace B.val/2)-1/2≤Real.sinh t*(axisDiagonalDifference B/2) := by
  let C:=hLogDilationSL t*B⁻¹
  let q:=Matrix.trace C.val/2
  let D:=Matrix.trace B.val/2
  let delta:=axisDiagonalDifference B
  have hrel : Real.sinh t*delta=2*(Real.cosh t*D-q) := by
    have he:=axisGap_product_inverse_trace t B
    change q=Real.cosh t*D-Real.sinh t*(delta/2) at he
    linarith only [he]
  have had:=hSimple_axis0_disjoint_diagonal_nonpos H (hLogDilationSL t) B hA htA hB htB
    (hLogDilationSL_hyperbolic_axis t ht hA htA) hs hBm hd
  have hdeltaD : 2*D≤delta := by
    have hh : Matrix.trace B.val≤axisDiagonalDifference B := by
      rw [Matrix.trace_fin_two]
      dsimp only [axisDiagonalDifference] at hdelta ⊢
      rw [Matrix.trace_fin_two] at htrace
      nlinarith only [had,hdelta,htrace]
    dsimp only [D,delta]
    linarith only [hh]
  have hDp : 1≤D := by dsimp only [D];linarith only [htrace]
  have hsp : 0<Real.sinh t:=Real.sinh_pos_iff.mpr ht
  by_contra hbad
  have hq : 1/2<q := by
    change ¬(Real.cosh t*D-1/2≤Real.sinh t*(delta/2)) at hbad
    linarith only [hrel,lt_of_not_ge hbad]
  have hq1 : q<1 := by
    have hh:=hyperbolic_collar_positive_branch_lt_one (Real.cosh t) (Real.sinh t) D
      (Real.sinh t*delta/2) (Real.cosh_pos t) hsp (Real.cosh_sq_sub_sinh_sq t)
      (by linarith only [hDp]) hT
      (by nlinarith only [mul_le_mul_of_nonneg_left hdeltaD hsp.le])
    linarith only [hh,hrel]
  have hstep2:=axisDiagonalDifference_disjoint_step_two t B
  change Real.sinh t*(axisDiagonalDifference (C^2*B*(C⁻¹)^2)-delta)+
    8*q*(Real.cosh t^2+D^2-1+q^2-2*q*Real.cosh t*D)=0 at hstep2
  have hstep3:=axisDiagonalDifference_conjugate_recurrence B C
  have hfirst : axisDiagonalDifference (C*B*C⁻¹)=delta:=axisDiagonalDifference_disjoint_step_one t B
  have hCtrace : Matrix.trace C.val=2*q := by dsimp only [q];ring
  rw [hfirst,hCtrace] at hstep3
  have hstep3' : axisDiagonalDifference (C^3*B*(C⁻¹)^3)-
      (4*q^2-1)*axisDiagonalDifference (C^2*B*(C⁻¹)^2)+(4*q^2-2)*delta=0 := by
    nlinarith only [hstep3]
  have hcand:=disjointAxis_bad_gap_diagonal_candidates (Real.cosh t) (Real.sinh t) D q delta
    (axisDiagonalDifference (C^2*B*(C⁻¹)^2)) (axisDiagonalDifference (C^3*B*(C⁻¹)^3))
    (Real.one_le_cosh t) hsp (Real.cosh_sq_sub_sinh_sq t) hDp hT hdeltaD hrel hq hq1 hstep2 hstep3'
  have hCm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈H := by
    dsimp only [C]
    rw [map_mul,map_inv]
    exact H.mul_mem hs.1 (H.inv_mem hBm)
  rcases hcand with hcand|hcand
  · have hne:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_partner_square_ne P t ht hA htA hs B hB htB hBm hd.1
      (by linarith only [hCtrace,hq]) (by linarith only [hCtrace,hq1])
    have hl:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_nearest_diagonal_lower P t ht hA htA hs.1 B hB htB hBm hd
      hdelta hno hmin (C^2) (by rw [map_pow];exact H.pow_mem hCm 2) hne.symm
    rw [←inv_pow] at hl
    exact (not_lt_of_ge hl) hcand.2
  · have hne:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_partner_cube_ne P t ht hA htA hs B hB htB hBm hd.1
      (by linarith only [hCtrace,hq]) (by change (Matrix.trace C.val)^2≤2; rw [hCtrace]; nlinarith only [hcand.1])
    have hl:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_nearest_diagonal_lower P t ht hA htA hs.1 B hB htB hBm hd
      hdelta hno hmin (C^3) (by rw [map_pow];exact H.pow_mem hCm 3) hne.symm
    rw [←inv_pow] at hl
    exact (not_lt_of_ge hl) hcand.2

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local notation "L₀" => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (0:ℝ)

/-- Sign and inverse choices orient a genuine matrix without changing its axis. -/
theorem axisGap_positive_oriented_lift (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (htB : 4<(Matrix.trace B.val)^2) (had : B 0 0*B 1 1≤0) :
    ∃E : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        E=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∨
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        E=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)⁻¹) ∧
      2<Matrix.trace E.val ∧ 0<axisDiagonalDifference E := by
  have hF : ∃F : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∧ 2<Matrix.trace F.val ∧ F 0 0*F 1 1≤0 := by
    by_cases ht : 2<Matrix.trace B.val
    · exact ⟨B,rfl,ht,had⟩
    · refine ⟨-B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg B,?_,?_⟩
      · have he : Matrix.trace (-B).val= -Matrix.trace B.val := by
          simp only [Matrix.SpecialLinearGroup.coe_neg,Matrix.trace_neg]
        rw [he]
        nlinarith only [htB,le_of_not_gt ht]
      · simpa only [Matrix.SpecialLinearGroup.coe_neg,Matrix.neg_apply,neg_mul_neg] using had
  obtain ⟨F,hFB,hFt,hFad⟩:=hF
  by_cases hdelta : 0<axisDiagonalDifference F
  · exact ⟨F,Or.inl hFB,hFt,hdelta⟩
  · refine ⟨F⁻¹,Or.inr ?_,?_,?_⟩
    · rw [map_inv,hFB]
    · rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_inverse]
    · have hne : axisDiagonalDifference F≠0 := by
        intro he
        dsimp only [axisDiagonalDifference] at he
        rw [Matrix.trace_fin_two] at hFt
        nlinarith only [he,hFt,hFad]
      have hneg : axisDiagonalDifference F<0:=lt_of_le_of_ne (le_of_not_gt hdelta) hne
      have hi : axisDiagonalDifference F⁻¹= -axisDiagonalDifference F := by
        norm_num [axisDiagonalDifference,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
      rw [hi]
      exact neg_pos.mpr hneg

/-- Every sign/inverse choice above preserves the actual entire axis and length. -/
theorem axisGap_oriented_axis_length (B E : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1) (htB : 4<(Matrix.trace B.val)^2)
    (hE : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E≠1) (htE : 4<(Matrix.trace E.val)^2)
    (he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      E=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∨
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      E=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)⁻¹) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis E hE htE=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry E)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  rcases he with he|he
  · exact ⟨hHyperbolicAxis_eq_of_realSLMobius_eq E B hE hB htE htB he,
      congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (hSLIsometry_eq_of_realSLMobius_eq E
        B he)⟩
  · have he' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B⁻¹ := by rwa [map_inv]
    have hBi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B⁻¹≠1:=by simpa only [map_inv] using inv_ne_one.mpr hB
    have htBi : 4<(Matrix.trace (B⁻¹).val)^2:=by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_inverse]
    have ha:=hHyperbolicAxis_eq_of_realSLMobius_eq E B⁻¹ hE hBi htE htBi he'
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_inverse B hB htB] at ha
    have hl:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (hSLIsometry_eq_of_realSLMobius_eq E B⁻¹ he')
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_inverse] at hl
    exact ⟨ha,hl⟩

/-- The nearest weak bound has no sign or orientation assumption on the original partner. -/
theorem HalfPlaneFuchsianGroup.axisGap_nearest_weak
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (t : ℝ) (ht : 0<t) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)))
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2) (hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hd : (L₀).HDisjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (hT : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)≤Real.cosh t)
    (hno : HyperbolicAxisFamiliesNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis
      (hLogDilationSL t) hA htA)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (hmin : ∀F : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∈H→
      L₀≠axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) F→
      (L₀).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)≤
        (L₀).lineDist (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
          F)) :
    Real.cosh t*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)-1/2≤
      Real.cosh ((L₀).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
        htB))*Real.sinh t*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
  have had:=hSimple_axis0_disjoint_diagonal_nonpos H (hLogDilationSL t) B hA htA hB htB
    (hLogDilationSL_hyperbolic_axis t ht hA htA) hs hBm hd
  obtain ⟨E,hchoice,htrace,hdelta⟩:=axisGap_positive_oriented_lift B htB had
  have hE : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E≠1 := by
    rcases hchoice with he|he
    · rwa [he]
    · rw [he]
      exact inv_ne_one.mpr hB
  have htE : 4<(Matrix.trace E.val)^2 := by nlinarith only [htrace]
  have hEm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E∈H := by
    rcases hchoice with he|he
    · rwa [he]
    · rw [he]
      exact H.inv_mem hBm
  obtain ⟨ha,hl⟩:=axisGap_oriented_axis_length B E hB htB hE htE hchoice
  have hdE : (L₀).HDisjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis E hE htE) := by rwa [ha]
  have htraceEq : Matrix.trace E.val/2=Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_abs_trace E hE htE
    rwa [abs_of_pos (by linarith only [htrace]),hl] at hh
  have hnoE : HyperbolicAxisFamiliesNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis
    (hLogDilationSL t) hA htA)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis E hE htE) := by rwa [ha]
  have hminE : ∀F : Matrix.SpecialLinearGroup (Fin
    2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∈H→
      L₀≠axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis E hE htE) F→
      (L₀).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis E hE htE)≤
        (L₀).lineDist (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis E hE htE) F) := by
    rwa [ha]
  have hh:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_nearest_positive_weak P t ht hA htA hs E hE htE hEm hdE
    htrace hdelta (by rwa [htraceEq]) hnoE hminE
  rw [htraceEq] at hh
  have hc:=hHyperbolic_axis0_distance_translation_product E hE htE hdE
  change _=|axisDiagonalDifference E|/2 at hc
  rw [abs_of_pos hdelta,ha,hl] at hc
  rw [←hc] at hh
  nlinarith only [hh]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local notation "L₀" => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (0:ℝ)

/-- The genuine closest translated partner gives the weak bound for the original
normalized pair; there is no supplied minimum or coefficient condition. -/
theorem HalfPlaneFuchsianGroup.axisGap_logDilation_weak
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (t : ℝ) (ht : 0<t) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)))
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2) (hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hd : (L₀).HDisjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (hT : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)≤Real.cosh t)
    (hno : HyperbolicAxisFamiliesNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis
      (hLogDilationSL t) hA htA)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    Real.cosh t*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)-1/2≤
      Real.cosh ((L₀).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
        htB))*Real.sinh t*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
  have haxisA:=hLogDilationSL_hyperbolic_axis t ht hA htA
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (hLogDilationSL t) hA htA≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB := by
    rw [haxisA]
    exact hd.1
  obtain ⟨Q,hQ,hQne,hQmin⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.exists_closest_distinct_hyperbolic_axis_pair P
    (hLogDilationSL t) B hs.1 hBm hA hB htA htB hne
  let C:=Q*B*Q⁻¹
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C≠1:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation B Q hB
  have htC : 4<(Matrix.trace C.val)^2 := by dsimp only [C];rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hCm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈H := by
    dsimp only [C]
    rw [map_mul,map_mul,map_inv]
    exact H.mul_mem (H.mul_mem hQ hBm) (H.inv_mem hQ)
  have haxisC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC=axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) Q :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation B Q hB htB
  have hdC:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.noncrossing_axis_image_hDisjoint P
    (hLogDilationSL t) B hs.1 hBm hA hB htA htB hno Q hQ hQne
  rw [haxisA] at hdC
  change (L₀).HDisjoint (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
    Q) at hdC
  rw [←haxisC] at hdC
  have hmap (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC) F=
        axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) (F*Q) := by
    rw [haxisC,axisGapLineImage_mul]
  have hnoC : HyperbolicAxisFamiliesNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis
    (hLogDilationSL t) hA htA)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC) := by
    intro F hF
    have hh:=hno (F*Q) (by rw [map_mul];exact H.mul_mem hF hQ)
    change _=axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC) F ∨
      Disjoint _ (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC)
        F).carrier
    rwa [hmap]
  have hmin : ∀F : Matrix.SpecialLinearGroup (Fin
    2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∈H→
      L₀≠axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC) F→
      (L₀).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC)≤
        (L₀).lineDist (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC) F) := by
    intro F hF hFne
    have hFQne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (hLogDilationSL t) hA htA≠
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ (F*Q)) := by
      rw [haxisA]
      change L₀≠axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) (F*Q)
      rwa [←hmap]
    have hh:=hQmin (F*Q) (by rw [map_mul];exact H.mul_mem hF hQ) hFQne
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (hLogDilationSL t) hA htA).lineDist
        (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) Q)≤
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (hLogDilationSL t) hA htA).lineDist
          (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) (F*Q)) at hh
    rw [haxisA,←haxisC] at hh
    rwa [hmap]
  have hlen : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B):=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation B Q
  have hh:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_nearest_weak P t ht hA htA hs C hC htC hCm hdC
    (by rwa [hlen]) hnoC hmin
  rw [hlen] at hh
  have hone : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (hLogDilationSL t) hA htA≠
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) := by
    change _≠axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) 1
    rwa [axisGapLineImage_one]
  have hdist:=hQmin 1 (by simpa only [map_one] using H.one_mem) hone
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (hLogDilationSL t) hA htA).lineDist
      (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) Q)≤
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (hLogDilationSL t) hA htA).lineDist
        (axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) 1) at hdist
  rw [haxisA,axisGapLineImage_one,←haxisC] at hdist
  have hc : Real.cosh ((L₀).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC))≤
      Real.cosh ((L₀).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) := by
    apply Real.cosh_le_cosh.mpr
    rwa [abs_of_nonneg ((L₀).lineDist_nonneg _),abs_of_nonneg ((L₀).lineDist_nonneg _)]
  have hsinh : 0≤Real.sinh t*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
    apply mul_nonneg (Real.sinh_pos_iff.mpr ht).le
    exact (Real.sinh_pos_iff.mpr (by linarith only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos B hB htB])).le
  have hm:=mul_le_mul_of_nonneg_right hc hsinh
  nlinarith only [hh,hm]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Complete-union noncrossing includes both self families and both cross families.
The existing cross-family-only predicate retains its original meaning. -/
def HyperbolicAxisUnionNoncrossing (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (L M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) : Prop :=
  ∀L'∈({L,M}:Set _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine),∀M'∈({L,M}:Set
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine),
    HyperbolicAxisFamiliesNoncrossing H L' M'

theorem HyperbolicAxisFamiliesNoncrossing.axisGap_conjugation
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {L M :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine}
    (hno : HyperbolicAxisFamiliesNoncrossing H L M)
    (Q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    HyperbolicAxisFamiliesNoncrossing (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q) H)
      (axisGapLineImage L Q) (axisGapLineImage M Q) := by
  intro F hF
  obtain ⟨g,hg,hge⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q) H _).mp hF
  let E:=Q⁻¹*F*Q
  have hE : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E∈H := by
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E=g := by
      dsimp only [E]
      rw [map_mul,map_mul,map_inv,←hge]
      group
    rwa [he]
  have himage : axisGapLineImage (axisGapLineImage M Q) F=
      axisGapLineImage (axisGapLineImage M E) Q := by
    rw [←axisGapLineImage_mul,←axisGapLineImage_mul]
    congr 1
    dsimp only [E]
    group
  change axisGapLineImage L Q=axisGapLineImage (axisGapLineImage M Q) F ∨
    Disjoint (axisGapLineImage L Q).carrier (axisGapLineImage (axisGapLineImage M Q) F).carrier
  rw [himage]
  rcases hno E hE with he|hd
  · exact Or.inl (congrArg (fun N=>axisGapLineImage N Q) he)
  · right
    simp only [axisGapLineImage,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier] at hd
    exact (Set.disjoint_image_iff (MulAction.injective (Matrix.SpecialLinearGroup.mapGL ℝ Q))).mpr hd

/-- Self-family noncrossing is actual simplicity, through the original whole-group lift. -/
theorem HalfPlaneFuchsianGroup.axisGap_simple_of_self_noncrossing
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1)
    (htA : 4<(Matrix.trace A.val)^2) (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H)
    (hno : HyperbolicAxisFamiliesNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA)) : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_iff_native_axis_stable H A hA htA (fun g hg=>
    mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩))).mpr
  refine ⟨hAm,?_⟩
  intro g hg
  obtain ⟨F,rfl⟩:=mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩)
  have hMap : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint ''
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).realGLMap
        (Matrix.SpecialLinearGroup.mapGL ℝ F)).carrier=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F).val '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneSpherePoint_image_realSL F
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier).symm
  rw [←hMap]
  rcases hno F hg with he|hd
  · left
    rw [←he]
  · right
    exact ((Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneSpherePoint_injective).mpr
      hd).symm

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual original ordered pair satisfies the corrected weak bound. -/
theorem HalfPlaneFuchsianGroup.axisGap_ordered_weak
    {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup G)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hs : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (hT : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)≤Real.cosh
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2))
    (hno : HyperbolicAxisFamiliesNoncrossing G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      A)/2)*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)-1/2≤
      Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
  have hAH:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr htA
  obtain ⟨q,t,ht,he⟩:=realSLMobius_hyperbolic_positive_log_normal_form A hAH
  let D:=hLogDilationSL t
  let C:=q*B*q⁻¹
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) G
  have PK : HalfPlaneFuchsianGroup K:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.realSLConjugateData P q
  have hQH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)) := by
    simpa only [map_mul,map_inv] using
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hAH
  have hDH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D):=he ▸ hQH
  have hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D≠1:=hDH.1.1
  have htD : 4<(Matrix.trace D.val)^2:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff D
    hD).mp hDH
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C≠1:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation B q hB
  have htC : 4<(Matrix.trace C.val)^2 := by dsimp only [C];rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hA' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)≠1:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation A q hA
  have htA' : 4<(Matrix.trace (q*A*q⁻¹).val)^2 := by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hAD:=hHyperbolicAxis_eq_of_realSLMobius_eq (q*A*q⁻¹) D hA' hD htA' htD he
  have hDaxis:=hLogDilationSL_hyperbolic_axis t ht hD htD
  have hImageA : (q • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis D hD htD).carrier := by
    rw [←hAD,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation A q hA
      htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hImageB : (q • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC).carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation B q hB
      htB,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hqpos : 0<(Matrix.SpecialLinearGroup.mapGL ℝ q).val.det := by
    change 0<q.val.det
    rw [q.det_coe]
    norm_num
  have hdis':=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
    htA).hDisjoint_realGL_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis D hD
      htD) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC)
    (Matrix.SpecialLinearGroup.mapGL ℝ q) hqpos hImageA hImageB hd
  rw [hDaxis] at hdis'
  have hsQ : IsSimple K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)) := by
    simpa only [map_mul,map_inv] using (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation G
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hs
  have hsD : IsSimple K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D):=he ▸ hsQ
  have hCm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈K := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) G
    rw [map_mul,map_mul,map_inv]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
      _).mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,hBm,rfl⟩
  have hTDA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry D)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) := by
    rw [←hSLIsometry_eq_of_realSLMobius_eq _ _
      he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation]
  have hSA : Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)=Real.sinh t := by
    rw [←hTDA]
    exact hLogDilationSL_sinh_half_translation t ht hD htD
  have hCA : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)=Real.cosh t := by
    rw [Real.sinh_injective hSA]
  have hdist:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
    htA).lineDist_isometry_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis D hD
      htD) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC) (q • ·) (isometry_smul ℍ
      q) hImageA hImageB
  rw [hDaxis] at hdist
  have hTB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B):=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation B q
  have hTC : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C)/2)≤Real.cosh t := by
    rwa [hTB,←hCA]
  have hQaxisA : axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
    htA) q=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis D hD htD :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation A q hA htA).symm.trans hAD
  have hQaxisB : axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
    htB) q=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation B q hB htB).symm
  have hnoK:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HyperbolicAxisFamiliesNoncrossing.axisGap_conjugation hno q
  rw [hQaxisA,hQaxisB] at hnoK
  have hb:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_logDilation_weak PK t ht hD htD hsD C hC htC hCm hdis' hTC hnoK
  rwa [hTB,hdist,←hSA,←hCA] at hb

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The entire union of the two axis families is
noncrossing, so both genuine generators are simple and the weak bound holds. -/
theorem HalfPlaneFuchsianGroup.disjointAxis_fullUnion_weak
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (hno : HyperbolicAxisUnionNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      A)/2)*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)-1/2≤
      Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
  have hsA:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_simple_of_self_noncrossing P A hA htA hAm
    (hno _ (by simp) _ (by simp))
  have hsB:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_simple_of_self_noncrossing P B hB htB hBm
    (hno _ (by simp) _ (by simp))
  rcases le_total (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2))
      (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)) with hT|hT
  · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_ordered_weak P A B hA hB htA htB hsA hBm hd hT
      (hno _ (by simp) _ (by simp))
  · have hd' : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
    htB).HDisjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA):=
      ⟨hd.1.symm,hd.2.1.symm,hd.2.2.symm⟩
    have hh:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_ordered_weak P B A hB hA htB htA hsB hAm hd' hT
      (hno _ (by simp) _ (by simp))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.lineDist_comm] at hh
    nlinarith only [hh]

/-- In the actual elliptic-free group the corrected full-union hypothesis gives
the original stronger bound through the existing genuine simple-axis collar. -/
theorem HalfPlaneFuchsianGroup.disjointAxis_fullUnion_strong
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H) (hEll
      : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (hno : HyperbolicAxisUnionNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    1+Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      A)/2)*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)≤
      Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
  have hsA:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_simple_of_self_noncrossing P A hA htA hAm
    (hno _ (by simp) _ (by simp))
  have hsB:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_simple_of_self_noncrossing P B hB htB hBm
    (hno _ (by simp) _ (by simp))
  exact hSimple_hyperbolic_strong_collar H hEll A B hA hB htA htB hsA hsB hd

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Bounds for the whole group generated by a non-elementary pair.
Complete-union noncrossing internally gives the full separated-axis geometry. -/
theorem HalfPlaneFuchsianGroup.noncrossing_hyperbolic_axes_cosh_gap_weak_and_ellipticFree_strong_bounds
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hno : HyperbolicAxisUnionNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*Real.cosh
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)-1/2≤
      Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
          A)/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)) ∧
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))→
      1+Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
        A)/2)*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)≤
        Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))*
          Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)) := by
  let G:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hGH : G≤H := (Subgroup.closure_le H).mpr (by
    intro g hg
    rcases hg with rfl|rfl
    · exact hAm
    · exact hBm)
  have hGd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G:=discreteMobius_subgroup_of_le H G P.discrete hGH
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB := by
    intro he
    obtain ⟨u,_,huA,_,_⟩:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).exists_two_points
    have huB : u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier := by rwa [←he]
    exact nonElementary_crossing_axes_ne A B hA hB htA htB u huA huB hGd hPair he
  have hne1 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA≠axisGapLineImage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) 1 := by
    rwa [axisGapLineImage_one]
  have hd:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.noncrossing_axis_image_hDisjoint P A B hAm hBm hA hB htA htB
    (hno _ (by simp) _ (by simp)) 1 (by simpa only [map_one] using H.one_mem) hne1
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint (axisGapLineImage
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) 1) at hd
  rw [axisGapLineImage_one] at hd
  refine ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.disjointAxis_fullUnion_weak P A B hA hB
    htA htB hAm hBm hd hno,?_⟩
  intro hEll
  have hsA:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_simple_of_self_noncrossing P A hA htA hAm
    (hno _ (by simp) _ (by simp))
  have hsB:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.axisGap_simple_of_self_noncrossing P B hB htB hBm
    (hno _ (by simp) _ (by simp))
  exact hSimple_hyperbolic_strong_collar G hEll A B hA hB htA htB
    (hsA.subgroup hGH (Subgroup.subset_closure (by simp)))
    (hsB.subgroup hGH (Subgroup.subset_closure (by simp))) hd

end LowDimensionalTopology.Geometry.Fuchsian
