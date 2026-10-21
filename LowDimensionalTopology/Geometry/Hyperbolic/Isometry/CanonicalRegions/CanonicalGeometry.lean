/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Topology.Perfect
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

/-- The real circle-line polynomial controlling the actual canonical region. -/
def hCanonicalQuadratic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) : ℝ :=
  A 1 0*(z.re^2+z.im^2)+(A 1 1-A 0 0)*z.re-A 0 1

/-- Determinant one turns the literal displacement quadratic into a real circle-line inequality. -/
theorem hCanonicalQuadratic_norm_sq (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    ‖(A 1 0 : ℂ)*(z : ℂ)^2+((A 1 1 : ℂ)-A 0 0)*z-A 0 1‖^2 =
      hCanonicalQuadratic A z^2 + ((Matrix.trace A.val)^2-4)*z.im^2 := by
  have hd := A.det_coe
  rw [Matrix.det_fin_two] at hd
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp only [pow_two,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
    Complex.add_im,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,add_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  simp only [hCanonicalQuadratic,Matrix.trace_fin_two]
  linear_combination -4*z.im^2*hd

/-- Away from the genuine half-turn exception, the canonical region has this exact real equation. -/
theorem hCanonicalRegion_mem_quadratic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace A.val ≠ 0) (z : ℍ) :
    z ∈ hCanonicalRegion A ↔ |hCanonicalQuadratic A z| < 2*z.im := by
  rw [hCanonicalRegion_of_trace_ne_zero A ht]
  change Real.sinh (dist z (A • z)/2) < |Matrix.trace A.val|/2 ↔ _
  rw [hSL_half_displacement_polynomial,div_lt_iff₀ (by positivity)]
  rw [show |Matrix.trace A.val|/2*(2*z.im) = |Matrix.trace A.val| *z.im by ring]
  have hn := hCanonicalQuadratic_norm_sq A z
  have hy := z.im_pos
  constructor
  · intro h
    have he := (sq_lt_sq₀ (norm_nonneg _) (by positivity : 0 ≤ |Matrix.trace A.val| *z.im)).mpr h
    rw [mul_pow,sq_abs] at he
    apply (sq_lt_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2*z.im)).mp
    rw [sq_abs]
    nlinarith [hn]
  · intro h
    have he := (sq_lt_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2*z.im)).mpr h
    rw [sq_abs] at he
    apply (sq_lt_sq₀ (norm_nonneg _) (by positivity : 0 ≤ |Matrix.trace A.val| *z.im)).mp
    rw [mul_pow,sq_abs]
    nlinarith [hn]

theorem continuous_hCanonicalQuadratic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Continuous (hCanonicalQuadratic A) := by
  unfold hCanonicalQuadratic
  fun_prop

/-- A non-half-turn canonical region is an actual open subset of the native plane. -/
theorem hCanonicalRegion_isOpen (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace A.val ≠ 0) : IsOpen (hCanonicalRegion A) := by
  have he : hCanonicalRegion A = {z : ℍ | |hCanonicalQuadratic A z| < 2*z.im} := by
    ext z
    exact hCanonicalRegion_mem_quadratic A ht z
  rw [he]
  exact isOpen_lt (continuous_hCanonicalQuadratic A).abs (by fun_prop)

/-- The actual singleton half-turn exception can itself be recovered from the region. -/
theorem hCanonicalRegion_trace_zero_iff (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (he : hCanonicalRegion A = hCanonicalRegion B) :
    Matrix.trace A.val = 0 ↔ Matrix.trace B.val = 0 := by
  have hforward (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (he : hCanonicalRegion A = hCanonicalRegion B) (ht : Matrix.trace A.val=0) :
      Matrix.trace B.val=0 := by
    by_contra hB
    have hopen := hCanonicalRegion_isOpen B hB
    rw [← he,hCanonicalRegion_halfTurn A ht] at hopen
    exact not_isOpen_singleton (hHalfTurnCenter A ht) hopen
  exact ⟨hforward A B he,hforward B A he.symm⟩

/-- A hyperbolic canonical region is the genuine metric-distance strip around its actual axis. -/
theorem hCanonicalRegion_hyperbolic_cosh (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2) :
    hCanonicalRegion A = {z : ℍ | Real.cosh ((hHyperbolicAxis A hA ht).pointDist z) <
      Real.cosh (hTranslationLength (hSLIsometry A)/2) /
        Real.sinh (hTranslationLength (hSLIsometry A)/2)} := by
  have htr : Matrix.trace A.val ≠ 0 := by intro he; rw [he] at ht; norm_num at ht
  have hs : 0 < Real.sinh (hTranslationLength (hSLIsometry A)/2) :=
    Real.sinh_pos_iff.mpr (by have h := hHyperbolic_translationLength_pos A hA ht; linarith)
  ext z
  rw [hCanonicalRegion_of_trace_ne_zero A htr]
  change Real.sinh (dist z (A • z)/2) < |Matrix.trace A.val|/2 ↔ _
  rw [hyperbolic_half_displacement A hA ht,hHyperbolic_translation_abs_trace A hA ht]
  exact (lt_div_iff₀ hs).symm

/-- The strip width is strictly positive and measured with the native point-to-axis infimum. -/
theorem hCanonicalRegion_hyperbolic_strip (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2) :
    ∃ r : ℝ, 0 < r ∧ hCanonicalRegion A = (hHyperbolicAxis A hA ht).distanceSublevel r := by
  let T := hTranslationLength (hSLIsometry A)/2
  have hT : 0 < T := by have h := hHyperbolic_translationLength_pos A hA ht; dsimp [T]; linarith
  have hs : 0 < Real.sinh T := Real.sinh_pos_iff.mpr hT
  have hc := Real.cosh_pos T
  have hsc : Real.sinh T < Real.cosh T :=
    (sq_lt_sq₀ hs.le hc.le).mp (by nlinarith [Real.cosh_sq_sub_sinh_sq T])
  have hr : 1 < Real.cosh T/Real.sinh T := (lt_div_iff₀ hs).mpr (by simpa using hsc)
  refine ⟨Real.arcosh (Real.cosh T/Real.sinh T),Real.arcosh_pos hr,?_⟩
  rw [hCanonicalRegion_hyperbolic_cosh A hA ht]
  ext z
  change Real.cosh ((hHyperbolicAxis A hA ht).pointDist z) < Real.cosh T/Real.sinh T ↔
    (hHyperbolicAxis A hA ht).pointDist z < _
  conv_lhs => rw [← Real.cosh_arcosh hr.le]
  rw [Real.cosh_lt_cosh,
    abs_of_nonneg (show 0 ≤ (hHyperbolicAxis A hA ht).pointDist z from Metric.infDist_nonneg),
    abs_of_pos (Real.arcosh_pos hr)]

/-- A parabolic canonical region is an actual conjugate of its horizontal horoball. -/
theorem hCanonicalRegion_parabolic_horoball (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ t : ℝ, t ≠ 0 ∧
      (fun z : ℍ => q • z) '' hCanonicalRegion A = {z : ℍ | |t|/2 < z.im} := by
  obtain ⟨q,t,ht,he⟩ := realSLMobius_parabolic_normal_form A hA
  refine ⟨q,t,ht,?_⟩
  rw [← hCanonicalRegion_conjugation]
  rcases he with he | he
  · rw [he,hCanonicalRegion_translation]
  · rw [he,hCanonicalRegion_neg,hCanonicalRegion_translation]

/-- The native standard rotation fixes the literal center I. -/
theorem hRotationSL_fixes_I (a b : ℝ) (hu : a^2+b^2=1) :
    hRotationSL a b hu • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [hSL_fixed_iff]
  norm_num [hRotationSL]

/-- The source standard elliptic domain is the actual native hyperbolic ball. -/
theorem hCanonicalRegion_rotation_ball (a b : ℝ) (hu : a^2+b^2=1)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    hCanonicalRegion (hRotationSL a b hu) = Metric.ball UpperHalfPlane.I (Real.arsinh (|a|/|b|)) := by
  have ht : Matrix.trace (hRotationSL a b hu).val ≠ 0 := by
    simpa [Matrix.trace_fin_two,hRotationSL] using ha
  ext z
  rw [hCanonicalRegion_of_trace_ne_zero _ ht]
  change Real.sinh (dist z (hRotationSL a b hu • z)/2) < _ ↔ dist z UpperHalfPlane.I < _
  rw [rotation_half_displacement]
  have htr : |Matrix.trace (hRotationSL a b hu).val|/2 = |a| := by
    simp [Matrix.trace_fin_two,hRotationSL,show a+a=2*a by ring,abs_mul]
  rw [htr]
  rw [← lt_div_iff₀ (abs_pos.mpr hb)]
  simpa only [Real.sinh_arsinh] using
    (Real.sinh_lt_sinh (x := dist z UpperHalfPlane.I) (y := Real.arsinh (|a|/|b|)))

/-- A half-turn's actual canonical region remains its singleton center, rather than an empty ball. -/
theorem hCanonicalRegion_rotation_halfTurn (a b : ℝ) (hu : a^2+b^2=1) (ha : a=0) :
    hCanonicalRegion (hRotationSL a b hu) = {UpperHalfPlane.I} := by
  have ht : Matrix.trace (hRotationSL a b hu).val = 0 := by simp [Matrix.trace_fin_two,hRotationSL,ha]
  have hlt : (Matrix.trace (hRotationSL a b hu).val)^2 < 4 := by rw [ht]; norm_num
  have hI := (hSL_elliptic_fixed_iff _ hlt UpperHalfPlane.I).mp (hRotationSL_fixes_I a b hu)
  rw [hCanonicalRegion_of_trace_zero _ ht]
  ext z
  change (hRotationSL a b hu • z=z) ↔ z=UpperHalfPlane.I
  rw [hSL_elliptic_fixed_iff _ hlt z,← hI]

/-- Every elliptic canonical region is either its genuine half-turn singleton or a genuine metric ball. -/
theorem hCanonicalRegion_elliptic_ball (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    let v := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    (Matrix.trace A.val=0 ∧ hCanonicalRegion A={v}) ∨
      ∃ r : ℝ, 0 < r ∧ Matrix.trace A.val ≠ 0 ∧ hCanonicalRegion A = Metric.ball v r := by
  obtain ⟨q,a,b,hu,hq,hb,hr⟩ := realSLMobius_elliptic_normal_form A hA
  have htr := hSL_trace_conjugation A q
  rw [hr] at htr
  have hta : Matrix.trace A.val = 2*a := by simpa [Matrix.trace_fin_two,hRotationSL,two_mul] using htr.symm
  by_cases ha : a=0
  · left
    refine ⟨by rw [hta,ha]; ring,?_⟩
    ext z
    rw [← hCanonicalRegion_conjugation_mem A q z,hr,hCanonicalRegion_rotation_halfTurn a b hu ha]
    change q • z=UpperHalfPlane.I ↔ z=_
    rw [← hq]
    exact (MulAction.toPerm q).injective.eq_iff
  · right
    refine ⟨Real.arsinh (|a|/|b|),Real.arsinh_pos_iff.mpr (div_pos (abs_pos.mpr ha) (abs_pos.mpr hb)),?_,?_⟩
    · rw [hta]
      exact mul_ne_zero (by norm_num) ha
    · ext z
      rw [← hCanonicalRegion_conjugation_mem A q z,hr,hCanonicalRegion_rotation_ball a b hu ha hb]
      change dist (q • z) UpperHalfPlane.I < _ ↔ dist z _ < _
      rw [← hq,(isometry_smul ℍ q).dist_eq]

/-- The canonical parabolic domain is exactly a strict superlevel of its actual fixed-point Poisson kernel. -/
theorem hCanonicalRegion_parabolic_poisson (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    ∃ p : Option ℝ, ∃ C : ℝ, 0 < C ∧
      (∀ w : Mobius.ExtendedComplex, (realSLMobius A).val w=w ↔ w=hPoissonBoundaryPoint p) ∧
      hCanonicalRegion A = {z : ℍ | C < Auxiliary.Analysis.halfPlanePoissonKernel z p} := by
  obtain ⟨p,C,hC,hfix,hdisp⟩ := parabolic_poisson_displacement A hA
  refine ⟨p,C,hC,hfix,?_⟩
  have ht := (realSLMobius_parabolic_iff A hA.1).mp hA
  have hn : Matrix.trace A.val ≠ 0 := by intro he; rw [he] at ht; norm_num at ht
  have habs : |Matrix.trace A.val|/2 = 1 := by
    have he : |Matrix.trace A.val|^2 = (2:ℝ)^2 := by rw [sq_abs,ht]; norm_num
    have hh := (sq_eq_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤2)).mp he
    rw [hh]
    norm_num
  ext z
  rw [hCanonicalRegion_of_trace_ne_zero A hn]
  change Real.sinh (dist z (A • z)/2) < |Matrix.trace A.val|/2 ↔ _
  rw [habs]
  have hp := Auxiliary.Analysis.halfPlanePoissonKernel_pos z.im_pos p
  have hd := hdisp z
  change Real.sinh (dist z (A • z)/2) < 1 ↔ C < Auxiliary.Analysis.halfPlanePoissonKernel z p
  constructor
  · intro h
    have he := mul_lt_mul_of_pos_left h hp
    simpa only [hd,mul_one] using he
  · intro h
    apply (mul_lt_mul_iff_right₀ hp).mp
    simpa only [hd,mul_one] using h

/-- Finite parabolic Poisson superlevels are literal Euclidean discs tangent to the ideal line. -/
theorem halfPlanePoissonKernel_superlevel_disc (p C : ℝ) (hC : 0 < C) (z : ℍ) :
    C < Auxiliary.Analysis.halfPlanePoissonKernel z (some p) ↔
      (z : ℂ) ∈ Metric.ball ((p : ℂ)+Complex.I/(2*C)) (1/(2*C)) := by
  let r : ℝ := 1/(2*C)
  have hr : 0 < r := by dsimp [r]; positivity
  have hCr : 2*C*r=1 := by dsimp [r]; field_simp
  have hne : (z : ℂ)-(p : ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    exact z.im_ne_zero (by simpa using hi)
  have hn : 0 < ‖(z : ℂ)-(p : ℂ)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hid : Complex.I/(2*C) = (r : ℂ)*Complex.I := by dsimp [r]; push_cast; ring
  have he : ‖(z : ℂ)-((p : ℂ)+(r : ℂ)*Complex.I)‖^2 =
      ‖(z : ℂ)-(p : ℂ)‖^2-2*r*z.im+r^2 := by
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,zero_add,add_zero,sub_zero,UpperHalfPlane.coe_im]
    ring
  rw [Auxiliary.Analysis.halfPlanePoissonKernel_finite,lt_div_iff₀ hn,Metric.mem_ball,dist_eq_norm,hid]
  change C*‖(z : ℂ)-(p : ℂ)‖^2 < z.im ↔ ‖(z : ℂ)-((p : ℂ)+(r : ℂ)*Complex.I)‖ < r
  rw [← sq_lt_sq₀ (norm_nonneg _) hr.le,he]
  constructor <;> intro h <;> nlinarith [hCr, sq_pos_of_pos hr]

end LowDimensionalTopology.Geometry.Hyperbolic
