/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementInvariants
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenInequality
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ParabolicReflectionPencils
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual real quadratic of a nonelliptic isometry has the required norm lower bound. -/
theorem nonelliptic_displacement_quadratic_lower
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ht : 4≤(Matrix.trace A.val)^2) (z : ℍ) :
    |A 1 0| *z.im^2≤
      ‖(A 1 0 : ℂ)*(z : ℂ)^2+((A 1 1 : ℂ)-A 0 0)*z-A 0 1‖ := by
  let a:=A 0 0
  let b:=A 0 1
  let c:=A 1 0
  let d:=A 1 1
  let x:=z.re
  let y:=z.im
  let Q : ℂ := (c:ℂ)*(z:ℂ)^2+((d:ℂ)-a)*z-b
  have hdet : a*d-b*c=1 := by simpa only [Matrix.det_fin_two] using A.det_coe
  have htr : 4≤(a+d)^2 := by simpa only [Matrix.trace_fin_two] using ht
  have hdelta : 0≤(d-a)^2+4*b*c := by nlinarith
  have hnorm : ‖Q‖^2=(c*(x^2-y^2)+(d-a)*x-b)^2+((2*c*x+d-a)*y)^2 := by
    rw [←Complex.normSq_eq_norm_sq]
    simp only [Q,Complex.normSq_apply,pow_two,Complex.add_re,Complex.mul_re,
      Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,Complex.add_im,
      Complex.mul_im,Complex.sub_im,zero_mul,sub_zero,add_zero]
    dsimp [x,y]
    ring
  have hidentity : ‖Q‖^2=(c*x^2+(d-a)*x-b)^2+c^2*y^4+
      y^2/2*((2*c*x+d-a)^2+((d-a)^2+4*b*c)) := by rw [hnorm];ring
  have hn : (|c| *y^2)^2≤‖Q‖^2 := by
    have he : (|c| *y^2)^2=c^2*y^4 := by rw [mul_pow,sq_abs];ring
    rw [he,hidentity]
    have hp := mul_nonneg (by positivity : 0≤y^2/2)
      (add_nonneg (sq_nonneg (2*c*x+d-a)) hdelta)
    calc
      c^2*y^4≤(c*x^2+(d-a)*x-b)^2+c^2*y^4 :=
        le_add_of_nonneg_left (sq_nonneg _)
      _≤_ := le_add_of_nonneg_right hp
  change |c| *y^2≤‖Q‖
  have hcy : 0≤|c| *y^2 := mul_nonneg (abs_nonneg c) (sq_nonneg y)
  nlinarith [norm_nonneg Q]

theorem nonelliptic_half_displacement_lower
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ht : 4≤(Matrix.trace A.val)^2) (z : ℍ) :
    |A 1 0| *z.im/2≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z := by
  change _≤Real.sinh (dist z (A•z)/2)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_half_displacement_polynomial]
  apply (le_div_iff₀ (by positivity : 0<2*z.im)).mpr
  nlinarith [nonelliptic_displacement_quadratic_lower A ht z]

/-- The source product estimate is proved directly for the genuine unit translation. -/
theorem unitTranslation_displacement_product_lower
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ht : 4≤(Matrix.trace A.val)^2) (z : ℍ) :
    |A 1 0|/4≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) z*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z := by
  change _≤Real.sinh (dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z)/2)*_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_half_displacement]
  norm_num only [abs_one,one_div]
  rw [inv_mul_eq_div]
  apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<4) (by positivity : 0<2*z.im)).mpr
  nlinarith [nonelliptic_half_displacement_lower A ht z]

theorem unitTranslation_jorgensen_defect (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=|A 1 0|^2 := by
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection (Matrix.SpecialLinearGroup.map
      Complex.ofRealHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)))
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection (Matrix.SpecialLinearGroup.map
      Complex.ofRealHom A))=_
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect_representatives]
  have hT : Matrix.SpecialLinearGroup.map Complex.ofRealHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)=
      _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hT,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenMatrixDefect_parabolic]
  change ‖(A 1 0 : ℂ)‖^2=|A 1 0|^2
  rw [Complex.norm_real,Real.norm_eq_abs]

/-- Genuine discreteness and non-elementarity imply the numerical coefficient bound. -/
theorem unitTranslation_lowerLeft_bound (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1≤|A 1 0| := by
  have hb := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.one_le_jorgensenDefect_of_discrete_nonElementary _ _ hd hne
  rw [unitTranslation_jorgensen_defect] at hb
  nlinarith [abs_nonneg (A 1 0)]

/-- The universal quarter bound, before transporting the actual arbitrary parabolic chart. -/
theorem unitTranslation_displacementP_quarter (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : 4≤(Matrix.trace A.val)^2)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/4≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_lower_bound _ _ _).mpr
  intro z
  have hc := unitTranslation_lowerLeft_bound A hd hne
  have hp := unitTranslation_displacement_product_lower A ht z
  linarith

theorem translation_jorgensen_defect (t : ℝ) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=|t*A 1 0|^2 := by
  let T : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2 := Matrix.SpecialLinearGroup.map Complex.ofRealHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)
  let B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2 := Matrix.SpecialLinearGroup.map Complex.ofRealHom A
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection T) (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B)=_
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect_representatives]
  have h00 : T 0 0=1 := rfl
  have h01 : T 0 1=(t:ℂ) := rfl
  have h10 : T 1 0=0 := rfl
  have h11 : T 1 1=1 := rfl
  have hc := _root_.LowDimensionalTopology.Geometry.Mobius.Classification.specialCommutator_trace_triangular T B h10
  rw [h00,h01,h11] at hc
  have htrace : Matrix.trace T.val=2 := by rw [Matrix.trace_fin_two,h00,h11];norm_num
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenMatrixDefect,htrace,hc]
  norm_num only [sub_self,mul_zero,zero_mul,sub_zero,zero_add,add_zero]
  rw [norm_zero,zero_add,
    show (2:ℂ)+(t:ℂ)^2*(B 1 0)^2-2=((t:ℂ)*B 1 0)^2 by ring,norm_pow]
  have hB10 : B 1 0=(A 1 0 : ℂ) := rfl
  rw [hB10,←Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs]

theorem translation_displacement_product_lower (t : ℝ)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ht : 4≤(Matrix.trace A.val)^2) (z : ℍ) :
    |t*A 1 0|/4≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) z*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z := by
  change _≤Real.sinh (dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z)/2)*_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_half_displacement,div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<4) (by positivity : 0<2*z.im)).mpr
  have hb := nonelliptic_half_displacement_lower A ht z
  have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg t)
  rw [abs_mul]
  nlinarith

theorem translation_displacementP_quarter (t : ℝ) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : 4≤(Matrix.trace A.val)^2)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/4≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) := by
  have hb := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.one_le_jorgensenDefect_of_discrete_nonElementary _ _ hd hne
  rw [translation_jorgensen_defect] at hb
  have hc : 1≤|t*A 1 0| := by nlinarith [abs_nonneg (t*A 1 0)]
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_lower_bound _ _ _).mpr
  intro z
  have hp := translation_displacement_product_lower t A ht z
  linarith

/-- The literal real determinant-one matrix trace is unchanged by real conjugation. -/
theorem realSL_trace_conjugation (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (q*A*q⁻¹).val=Matrix.trace A.val := by
  change Matrix.trace (q.val*A.val*(q⁻¹).val)=_
  rw [Matrix.trace_mul_cycle]
  change Matrix.trace ((q⁻¹*q).val*A.val)=_
  rw [inv_mul_cancel]
  simp only [Matrix.SpecialLinearGroup.coe_one,one_mul]

theorem hSLIsometry_conjugation (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)=
      (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry q).symm.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)).trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry q)) := by
  apply IsometryEquiv.ext
  intro z
  change (q*A*q⁻¹)•z=q•(A•(q⁻¹•z))
  simp only [mul_smul]

/-- The universal quarter bound for an arbitrary actual parabolic first generator and
an arbitrary actual nonelliptic second generator, without an assumed normal form. -/
theorem parabolic_displacementP_quarter (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (htB : 4≤(Matrix.trace B.val)^2)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/4≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  obtain ⟨q,t,_ht,hnorm⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  have hprojA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    rw [←map_inv,←map_mul,←map_mul]
    rcases hnorm with he | he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  have hprojB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹) := by
    simp only [map_mul,map_inv]
  let H := Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hD' : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    let : DiscreteTopology H := hd
    have he := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
    change DiscreteTopology (H.map (MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      q)).toMonoidHom) at he
    dsimp only [H] at he
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation, hprojA,hprojB] at he
    exact he
  have hN' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    have he := hne.conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,hprojA,hprojB] at he
    exact he
  have hnormI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    rcases hnorm with he | he
    · rw [he]
    · rw [he]
      apply IsometryEquiv.ext
      intro z
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_neg_smul _ z
  calc
    1/4≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*B*q⁻¹)) :=
      translation_displacementP_quarter t _ (by rwa [realSL_trace_conjugation]) hD' hN'
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*B*q⁻¹)) := by rw [hnormI]
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
      rw [hSLIsometry_conjugation A q,hSLIsometry_conjugation B
        q,_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_conjugation]

/-- Both parabolic/nonelliptic branches of the source universal quarter estimate. -/
theorem parabolic_pair_displacementP_quarter (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/4≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  apply parabolic_displacementP_quarter A B hA _ hd hne
  rcases hB with hp | hh
  · exact le_of_eq ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff B hp.1).mp hp).symm
  · exact le_of_lt ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hh.1.1).mp hh)

end LowDimensionalTopology.Geometry.Fuchsian
