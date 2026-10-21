/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeHyperbolicBounds
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalRegions
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.HyperbolicCanonicalHeight
public import Mathlib.Algebra.Group.Subgroup.Lattice
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The genuine distance between two geodesics is bounded by the sum of their actual distances from any point. -/
theorem halfPlaneLine_lineDist_le_pointDist_add (L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (z : ℍ) :
    L.lineDist M≤L.pointDist z+M.pointDist z := by
  have hd:=L.lineDist_le_dist M (L.orthogonalFoot_mem z) (M.orthogonalFoot_mem z)
  have ht:=dist_triangle (L.orthogonalFoot z) z (M.orthogonalFoot z)
  rw [dist_comm (L.orthogonalFoot z) z,←L.pointDist_eq_orthogonalFoot z,
    ←M.pointDist_eq_orthogonalFoot z] at ht
  exact hd.trans ht

/-- A pointwise comparison of actual geodesic distances transfers the strong axis-product bound. -/
theorem halfPlaneLine_cosh_lineDist_le_two_pointDist_cosh_mul (L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (z : ℍ) :
    Real.cosh (L.lineDist M)≤2*Real.cosh (L.pointDist z)*Real.cosh (M.pointDist z) := by
  have hd:=halfPlaneLine_lineDist_le_pointDist_add L M z
  have hc : Real.cosh (L.lineDist M)≤Real.cosh (L.pointDist z+M.pointDist z) := by
    apply Real.cosh_le_cosh.mpr
    rwa [abs_of_nonneg (L.lineDist_nonneg M),
      abs_of_nonneg (add_nonneg (L.pointDist_nonneg z) (M.pointDist_nonneg z))]
  have hs:=mul_le_mul (Real.sinh_lt_cosh (L.pointDist z)).le
    (Real.sinh_lt_cosh (M.pointDist z)).le
    (Real.sinh_nonneg_iff.mpr (M.pointDist_nonneg z)) (Real.cosh_pos (L.pointDist z)).le
  rw [Real.cosh_add] at hc
  nlinarith

/-- The actual pointwise sharp bound follows from the genuine strong disjoint-axis product bound. -/
theorem hHyperbolic_displacement_bound_of_strong_axis_product
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hstrong : 2≤Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
        A)/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2))
    (z : ℍ) : 1≤Real.sinh (dist z (A • z)/2)*Real.sinh (dist z (B • z)/2) := by
  have hsA : 0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2) :=
    Real.sinh_nonneg_iff.mpr (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA htA])
  have hsB : 0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) :=
    Real.sinh_nonneg_iff.mpr (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos B hB htB])
  have hc:=halfPlaneLine_cosh_lineDist_le_two_pointDist_cosh_mul (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) z
  have hh:=mul_le_mul_of_nonneg_right hc (mul_nonneg hsA hsB)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_half_displacement A hA
    htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_half_displacement B hB htB]
  nlinarith

/-- The real exponential respects integer multiplication in its actual positive-real embedding. -/
theorem real_exp_int_mul (t : ℝ) (n : ℤ) : Real.exp ((n:ℝ)*t)=Real.exp t^n := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_intCast,Complex.ofReal_zpow] using
    Complex.exp_int_mul (t:ℂ) n

/-- Every actual logarithmic diagonal word has its literal exponential trace. -/
theorem hLogDilationSL_zpow_mul_trace (t : ℝ) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (n : ℤ) :
    Matrix.trace (hLogDilationSL t^n*B).val=B 0 0*Real.exp t^n+B 1 1*Real.exp t^(-n) := by
  rw [hLogDilationSL_zpow]
  simp only [Matrix.SpecialLinearGroup.coe_mul,hLogDilationSL,Matrix.trace_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,zero_mul,add_zero,zero_add]
  rw [real_exp_int_mul]
  have he : -((n:ℝ)*t)=((-n:ℤ):ℝ)*t := by push_cast;ring
  rw [he,real_exp_int_mul]
  ring

/-- The exact original-group trace-gap bound in a genuine diagonal chart. -/
theorem hEllipticFree_logDilation_trace_gap
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (t : ℝ) (ht : 0<t) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hDm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)∈G) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (ha : 0<B 0 0) (hd : B 1 1<0) :
    4*Real.exp t≤(-B 0 0*B 1 1)*(Real.exp t-1)^2 := by
  apply ellipticFree_exponential_trace_gap (Real.exp t) (B 0 0) (B 1 1)
    (Real.one_lt_exp_iff.mpr ht) ha hd
  intro n
  have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t^n*B)∈G := by
    simpa only [map_mul,map_zpow] using G.mul_mem (G.zpow_mem hDm n) hBm
  have hg:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_not_elliptic_abs_trace (hLogDilationSL t^n*B) (hG
    ⟨_,hm⟩)
  rwa [hLogDilationSL_zpow_mul_trace] at hg

/-- Avoiding the elliptic interval under every diagonal translate forces both diagonal coefficients to be nonzero. -/
theorem ellipticFree_exponential_trace_diagonal_ne_zero (u a d : ℝ) (hu : 1<u)
    (hgap : ∀n : ℤ,2≤|a*u^n+d*u^(-n)|) : a≠0 ∧ d≠0 := by
  have hu0 : 0<u:=by linarith
  have hno (s : ℝ) (h : ∀n : ℕ,2≤|s|/(u^n)) : False := by
    obtain ⟨N,hN⟩:=pow_unbounded_of_one_lt |s| hu
    have hh:=(le_div_iff₀ (pow_pos hu0 N)).mp (h N)
    nlinarith [abs_nonneg s,pow_pos hu0 N]
  constructor
  · intro ha
    apply hno d
    intro n
    have hg:=hgap (n:ℤ)
    simpa only [ha,zero_mul,zero_add,zpow_neg,zpow_natCast,abs_mul,abs_inv,
      abs_of_pos (pow_pos hu0 n),div_eq_mul_inv] using hg
  · intro hd
    apply hno a
    intro n
    have hg:=hgap (-(n:ℤ))
    simpa only [hd,zero_mul,add_zero,zpow_neg,zpow_natCast,abs_mul,abs_inv,
      abs_of_pos (pow_pos hu0 n),div_eq_mul_inv] using hg

/-- The diagonal-word trace-gap inequality needs only a nonpositive original diagonal product. -/
theorem ellipticFree_exponential_trace_gap_of_nonpositive_product (u a d : ℝ) (hu : 1<u)
    (had : a*d≤0) (hgap : ∀n : ℤ,2≤|a*u^n+d*u^(-n)|) :
    4*u≤(-a*d)*(u-1)^2 := by
  obtain ⟨ha0,hd0⟩:=ellipticFree_exponential_trace_diagonal_ne_zero u a d hu hgap
  by_cases ha : 0<a
  · have hd : d<0 := by
      have hh : d≤0 := by
        by_contra hn
        have hp:=mul_pos ha (lt_of_not_ge hn)
        linarith
      exact lt_of_le_of_ne hh hd0
    exact ellipticFree_exponential_trace_gap u a d hu ha hd hgap
  · have han : 0< -a:=neg_pos.mpr (lt_of_le_of_ne (not_lt.mp ha) ha0)
    have hd : 0<d := by
      have hh : 0≤d := by
        by_contra hn
        have hp:=mul_pos_of_neg_of_neg (by linarith : a<0) (lt_of_not_ge hn)
        linarith
      exact lt_of_le_of_ne hh hd0.symm
    have hneg (n : ℤ) : 2≤|(-a)*u^n+(-d)*u^(-n)| := by
      have he : (-a)*u^n+(-d)*u^(-n)= -(a*u^n+d*u^(-n)) := by ring
      rw [he,abs_neg]
      exact hgap n
    have hh:=ellipticFree_exponential_trace_gap u (-a) (-d) hu han (by linarith) hneg
    nlinarith

/-- The image of an actual imaginary-axis point has its literal real coordinate. -/
theorem hSL_imaginaryAxis_image_re (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (y : ℝ) (hy : 0<y) :
    (B • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy).re=
      (B 0 0*B 1 0*y^2+B 0 1*B 1 1)/((B 1 0)^2*y^2+(B 1 1)^2) := by
  change ((B • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy : ℍ):ℂ).re= _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply,Complex.div_re,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  simp [Complex.normSq_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  ring

/-- Nonintersection of the actual imaginary axis with its genuine image forces the original coefficient sign condition. -/
theorem hSL_imaginaryAxis_translate_disjoint_product_nonneg
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd : Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier
      ((B • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier)) :
    0≤(B 0 0*B 1 1)*(B 0 1*B 1 0) := by
  by_contra hn
  have hn : (B 0 0*B 1 0)*(B 0 1*B 1 1)<0 := by nlinarith [lt_of_not_ge hn]
  have hac : B 0 0*B 1 0≠0 := by intro he;rw [he,zero_mul] at hn;linarith
  have hratio : 0< -(B 0 1*B 1 1)/(B 0 0*B 1 0) := by
    apply div_pos_iff.mpr
    rcases mul_neg_iff.mp hn with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inl ⟨by linarith,h1⟩
    · exact Or.inr ⟨by linarith,h1⟩
  let y:=Real.sqrt (-(B 0 1*B 1 1)/(B 0 0*B 1 0))
  have hy : 0<y:=Real.sqrt_pos.mpr hratio
  let p:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy
  have hp : p∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier:=rfl
  have hB : B • p∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
    change (B • p).re=0
    rw [hSL_imaginaryAxis_image_re]
    have he : B 0 0*B 1 0*y^2+B 0 1*B 1 1=0 := by
      dsimp only [y]
      rw [Real.sq_sqrt hratio.le]
      have hh:=div_mul_cancel₀ (-(B 0 1*B 1 1)) hac
      linarith
    rw [he,zero_div]
  exact Set.disjoint_left.mp hd hB (mem_image_of_mem _ hp)

/-- Disjointness from the actual imaginary axis forces the strict opposite off-diagonal signs. -/
theorem hHyperbolic_axis0_disjoint_offdiagonal_product_neg
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    B 0 1*B 1 0<0 := by
  have hb : B 0 1≠0 := by
    intro hb
    have hf : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(0:ℂ) := by
      change _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map Complex.ofRealHom
          B)) ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(0:ℂ)
      apply (_root_.LowDimensionalTopology.Geometry.Mobius.Classification.fractionalLinear_fixed_coe_iff _ 0).mpr
      change (B 1 0:ℂ)*(0*0)+((B 1 1:ℂ)-B 0 0)*0+ -(B 0 1:ℂ)=0
      simp [hb]
    have hp : ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).idealEndpoints := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints]
      exact hf
    apply Set.disjoint_left.mp hd.2.1 (show ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).idealEndpoints by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.vertical_idealEndpoints];simp)
    exact hp
  have hc : B 1 0≠0 := by
    intro hc
    have hp : (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).idealEndpoints := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints]
      exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff B).mpr hc
    apply Set.disjoint_left.mp hd.2.1 (show (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).idealEndpoints by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.vertical_idealEndpoints];simp)
    exact hp
  by_contra hn
  have hbc : 0<B 0 1*B 1 0:=lt_of_le_of_ne (le_of_not_gt hn) (mul_ne_zero hb hc).symm
  have hr : 0<B 0 1/B 1 0:=div_pos_iff.mpr (mul_pos_iff.mp hbc)
  let y:=Real.sqrt (B 0 1/B 1 0)
  have hy : 0<y:=Real.sqrt_pos.mpr hr
  let p:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy
  have hpA : p∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier:=rfl
  have hpB : p∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier := by
    apply (_root_.LowDimensionalTopology.Geometry.Fuchsian.hyperbolic_axis_quadratic_zero B hB htB p).mpr
    change B 1 0*(0^2+y^2)+(B 1 1-B 0 0)*0-B 0 1=0
    simp only [zero_pow (by norm_num : 2≠0),zero_add,mul_zero,add_zero]
    dsimp only [y]
    rw [Real.sq_sqrt hr.le]
    field_simp
    ring
  exact Set.disjoint_left.mp hd.2.2 hpA hpB

/-- An actual real map preserving the full imaginary-axis geodesic preserves its genuine endpoint pair. -/
theorem hSL_axis0_preserver_mem_pairStabilizer
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (he : (B • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
      0).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer := by
  have hg : 0<(Matrix.SpecialLinearGroup.mapGL ℝ B).val.det := by
    change 0<B.val.det
    rw [B.det_coe]
    norm_num
  have hends:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
    0).idealEndpoints_realGL_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0)
    (Matrix.SpecialLinearGroup.mapGL ℝ B) hg he
  have hfrac : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val=_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ B)) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius,MonoidHom.comp_apply,_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_matrix]
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val '' {((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞}={((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞}
  rw [hfrac]
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.vertical_idealEndpoints,Complex.ofReal_zero] using hends.symm

/-- The translate of a genuinely simple axis by a non-elementary partner is actually disjoint. -/
theorem hSimple_axis0_translate_disjoint
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (A B : Matrix.SpecialLinearGroup
      (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA : 4<(Matrix.trace A.val)^2)
    (haxis : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0)
    (hs : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier
      ((B • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier) := by
  rcases hs.2.2 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) hBm with he | hd
  · have himage : (B • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier := by
      apply (Set.image_injective.mpr _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective)
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_image_realSL,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis]
      exact he
    rw [haxis] at himage
    have hBpair:=hSL_axis0_preserver_mem_pairStabilizer B himage
    have hApair:=hSL_axis0_preserver_mem_pairStabilizer A (by
      rw [←haxis]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_invariant A hA htA)
    have hle : Subgroup.closure ({
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)≤
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer := by
      apply (Subgroup.closure_le
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer).mpr
      intro g hg
      rcases hg with rfl | rfl
      · exact hApair
      · exact hBpair
    apply False.elim
    apply hPair
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isElementary_of_invariant_pair
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer
      ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∞
      (fun g=>g.property)).mono hle
  · have hdn : Disjoint ((B • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
    htA).carrier)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier := by
      simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis A hA
        htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_image_realSL,
        Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective] using hd
    rw [haxis] at hdn
    exact hdn.symm

/-- The exact exponential word gap gives the strong product needed for the actual disjoint-axis estimate. -/
theorem ellipticFree_exponential_strong_product (u a d : ℝ) (hu : 1<u)
    (had : a*d≤0) (hgap : ∀n : ℤ,2≤|a*u^n+d*u^(-n)|) :
    2≤((u-u⁻¹)/2)*(|a-d|/2) := by
  have hg:=ellipticFree_exponential_trace_gap_of_nonpositive_product u a d hu had hgap
  have hu0 : 0<u:=by linarith
  let r:=Real.sqrt u
  let k:=Real.sqrt (-a*d)
  have hr : 0<r:=Real.sqrt_pos.mpr hu0
  have hk : 0≤k:=Real.sqrt_nonneg _
  have hrsq : r^2=u:=Real.sq_sqrt hu0.le
  have hksq : k^2= -a*d:=Real.sq_sqrt (by nlinarith : 0≤-a*d)
  have hkr : 2*r≤k*(u-1) := by
    apply (sq_le_sq₀ (by positivity : (0:ℝ)≤2*r) (mul_nonneg hk (by linarith))).mp
    rw [mul_pow,mul_pow,hksq,hrsq]
    norm_num
    nlinarith only [hg]
  have hdiff : 2*k≤|a-d| := by
    apply (sq_le_sq₀ (by positivity : (0:ℝ)≤2*k) (abs_nonneg _)).mp
    rw [mul_pow,hksq,sq_abs]
    norm_num
    nlinarith [sq_nonneg (a+d)]
  have hroot : 2*r≤u+1 := by nlinarith [sq_nonneg (r-1)]
  have hl : 4*r≤|a-d| *(u-1) := by
    have hh:=mul_le_mul_of_nonneg_right hdiff (by linarith : 0≤u-1)
    nlinarith
  have hh:=mul_le_mul_of_nonneg_right hl (by linarith : 0≤u+1)
  have hroot':=mul_le_mul_of_nonneg_left hroot (by positivity : (0:ℝ)≤4*r)
  have hstrong : 8*u≤|a-d| *(u^2-1) := by nlinarith
  have he : ((u-u⁻¹)/2)*(|a-d|/2)=|a-d| *(u^2-1)/(4*u) := by
    field_simp [hu0.ne']
    ring
  rw [he]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<4*u)).mpr
  linarith

/-- The genuine logarithmic diagonal lift has its actual imaginary-axis invariant geodesic. -/
theorem hLogDilationSL_hyperbolic_axis (t : ℝ) (ht : 0<t)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htrace : 4<(Matrix.trace (hLogDilationSL t).val)^2) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (hLogDilationSL t) hA htrace=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
  ext z
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.hyperbolic_axis_quadratic_zero]
  have he : Real.exp (-t)-Real.exp t≠0 :=
    sub_ne_zero.mpr (Real.exp_injective.ne (by linarith : -t≠t))
  change 0*(z.re^2+z.im^2)+(Real.exp (-t)-Real.exp t)*z.re-0=0 ↔ z.re=0
  simp only [zero_mul,zero_add,sub_zero,mul_eq_zero,he,false_or]

/-- The actual metric translation infimum of the diagonal lift has the expected positive half-sinh. -/
theorem hLogDilationSL_sinh_half_translation (t : ℝ) (ht : 0<t)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htrace : 4<(Matrix.trace (hLogDilationSL t).val)^2) :
    Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (hLogDilationSL t))/2)=Real.sinh t := by
  have htr : Matrix.trace (hLogDilationSL t).val=2*Real.cosh t := by
    rw [Matrix.trace_fin_two]
    change Real.exp t+Real.exp (-t)=2*Real.cosh t
    rw [Real.cosh_eq]
    ring
  have hc:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_trace (hLogDilationSL t) hA htrace
  rw [htr] at hc
  apply (sq_eq_sq₀
    (Real.sinh_nonneg_iff.mpr (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos (hLogDilationSL t) hA htrace]))
    (Real.sinh_nonneg_iff.mpr ht.le)).mp
  nlinarith [Real.cosh_sq_sub_sinh_sq t,
    Real.cosh_sq_sub_sinh_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (hLogDilationSL t))/2)]

/-- For an actual simple axis and a disjoint-axis non-elementary partner, the original diagonal product is nonpositive. -/
theorem hSimple_axis0_disjoint_diagonal_product_nonpos
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (A B : Matrix.SpecialLinearGroup
      (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA : 4<(Matrix.trace A.val)^2)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1) (htB : 4<(Matrix.trace B.val)^2)
    (haxis : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0)
    (hs : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hdis : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    B 0 0*B 1 1≤0 := by
  have hi:=hSimple_axis0_translate_disjoint G A B hA htA haxis hs hBm hPair
  have hp:=hSL_imaginaryAxis_translate_disjoint_product_nonneg B hi
  have hc:=hHyperbolic_axis0_disjoint_offdiagonal_product_neg B hB htB hdis
  by_contra hn
  have hh:=mul_neg_of_pos_of_neg (lt_of_not_ge hn) hc
  linarith

/-- The genuine axis-distance factor of an original matrix is exactly its diagonal difference. -/
theorem hHyperbolic_axis0_distance_translation_product
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)=|B 0 0-B 1 1|/2 := by
  have hbc:=hHyperbolic_axis0_disjoint_offdiagonal_product_neg B hB htB hd
  have hc : B 1 0≠0:=by intro he;rw [he,mul_zero] at hbc;linarith
  let m:=(B 0 0-B 1 1)/(2*B 1 0)
  obtain ⟨r,hr,haxis,_hrsq⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.hyperbolic_axis_finite_circle B hB htB hc
  have hτ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAxisSignedSine_abs_eq_sinh_translation B hB htB
  rw [haxis] at hτ
  change |B 1 0*r|=Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) at hτ
  have hcosh : Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))=|m|/r := by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_cosh_lineDist _ _ hd,haxis,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_normal_product,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    change |0*((1-m^2+r^2)/(2*r))+(-1)*(m/r)-0*(-(1+m^2-r^2)/(2*r))|=|m|/r
    simp only [zero_mul,zero_add,neg_one_mul,sub_zero,abs_neg,abs_div,abs_of_pos hr]
  have hcm : B 1 0*m=(B 0 0-B 1 1)/2 := by
    dsimp only [m]
    field_simp
  have habs : |B 1 0| *|m|=|B 0 0-B 1 1|/2 := by
    rw [←abs_mul,hcm,abs_div]
    norm_num
  rw [hcosh,←hτ,abs_mul,abs_of_pos hr]
  calc
    |m|/r*(|B 1 0| *r)=|B 1 0| *|m| := by field_simp
    _=|B 0 0-B 1 1|/2:=habs

/-- All actual nonelliptic group words give the strong diagonal difference product, without chosen signs. -/
theorem hEllipticFree_logDilation_strong_diagonal_product
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (t : ℝ) (ht : 0<t) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hDm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)∈G) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (had : B 0 0*B 1 1≤0) :
    2≤Real.sinh t*(|B 0 0-B 1 1|/2) := by
  have hg : ∀n : ℤ,2≤|B 0 0*Real.exp t^n+B 1 1*Real.exp t^(-n)| := by
    intro n
    have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t^n*B)∈G := by
      simpa only [map_mul,map_zpow] using G.mul_mem (G.zpow_mem hDm n) hBm
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_not_elliptic_abs_trace (hLogDilationSL t^n*B) (hG
      ⟨_,hm⟩)
    rwa [hLogDilationSL_zpow_mul_trace] at hh
  have hh:=ellipticFree_exponential_strong_product (Real.exp t) (B 0 0) (B 1 1)
    (Real.one_lt_exp_iff.mpr ht) had hg
  simpa only [Real.sinh_eq,Real.exp_neg] using hh

/-- The sharp source bound in the actual simple/disjoint diagonal chart, with all coefficient conditions derived. -/
theorem hEllipticFree_simple_disjoint_logDilation_displacement_bound
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (t : ℝ) (ht : 0<t)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htA : 4<(Matrix.trace (hLogDilationSL t).val)^2)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1) (htB : 4<(Matrix.trace B.val)^2)
    (hs : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t))) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hdis : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) (z : ℍ) :
    1≤Real.sinh (dist z (hLogDilationSL t • z)/2)*Real.sinh (dist z (B • z)/2) := by
  have haxis:=hLogDilationSL_hyperbolic_axis t ht hA htA
  have had:=hSimple_axis0_disjoint_diagonal_product_nonpos G (hLogDilationSL t) B hA htA hB htB
    haxis hs hBm hPair hdis
  have hh:=hEllipticFree_logDilation_strong_diagonal_product G hG t ht B hs.1 hBm had
  have hBfactor:=hHyperbolic_axis0_distance_translation_product B hB htB hdis
  apply hHyperbolic_displacement_bound_of_strong_axis_product (hLogDilationSL t) B hA hB htA htB ?_ z
  rw [haxis,hLogDilationSL_sinh_half_translation t ht hA htA]
  calc
    2≤Real.sinh t*(|B 0 0-B 1 1|/2):=hh
    _=Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))*
        Real.sinh t*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
      rw [←hBfactor]
      ring

end LowDimensionalTopology.Geometry.Fuchsian
