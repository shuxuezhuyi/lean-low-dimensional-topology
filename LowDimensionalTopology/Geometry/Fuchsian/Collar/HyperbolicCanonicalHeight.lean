/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalSeparation
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual half-displacement has an exact quadratic identity in the original point. -/
theorem canonical_quadratic_displacement_identity (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    4*z.im^2*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z)^2=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic A z)^2+((Matrix.trace A.val)^2-4)*z.im^2 := by
  have he : 2*z.im*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z=
      ‖(A 1 0 : ℂ)*(z:ℂ)^2+((A 1 1 : ℂ)-A 0 0)*z-A 0 1‖ := by
    change 2*z.im*Real.sinh (dist z (A•z)/2)=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_half_displacement_polynomial]
    field_simp
  have hs:=congrArg (fun x : ℝ=>x^2) he
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic_norm_sq] at hs
  nlinarith [hs]

/-- The actual native hyperbolic axis is exactly the zero locus of its real quadratic. -/
theorem hyperbolic_axis_quadratic_zero (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2) (z : ℍ) :
    z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA ht).carrier ↔ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic A z=0 := by
  have hmin : 4*(Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2))^2=(Matrix.trace A.val)^2-4 := by
    nlinarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_trace A hA ht,
      Real.cosh_sq_sub_sinh_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)]
  have he:=canonical_quadratic_displacement_identity A z
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_minimum A hA ht z]
  constructor
  · intro hz
    change 4*z.im^2*(Real.sinh (dist z (A•z)/2))^2=_ at he
    rw [hz] at he
    have hm:=congrArg (fun x : ℝ=>x*z.im^2) hmin
    nlinarith [sq_nonneg (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic A z)]
  · intro hz
    rw [hz,zero_pow (by norm_num : 2≠0),zero_add] at he
    have hm:=congrArg (fun x : ℝ=>x*z.im^2) hmin
    have hs : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z=
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2) := by
      have hn:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement_nonneg (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z
      have htpos : 0<Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2) :=
        Real.sinh_pos_iff.mpr (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA ht])
      have hy : 0<z.im^2 := sq_pos_of_pos z.im_pos
      apply (sq_eq_sq₀ hn htpos.le).mp
      apply mul_left_cancel₀ (by positivity : 4*z.im^2≠0)
      nlinarith [hm,he]
    change Real.sinh (dist z (A•z)/2)=_ at hs
    have hd:=Real.sinh_injective hs
    linarith

/-- Every genuine hyperbolic quadratic with finite endpoints has its actual centered circle form. -/
theorem canonical_quadratic_centered (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic A z=
      A 1 0*((z.re-(A 0 0-A 1 1)/(2*A 1 0))^2+z.im^2)-
        ((Matrix.trace A.val)^2-4)/(4*A 1 0) := by
  have hd:=A.det_coe
  rw [Matrix.det_fin_two] at hd
  dsimp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic]
  rw [Matrix.trace_fin_two]
  field_simp
  linear_combination 16*hd

/-- Every actual finite-ended canonical region lies below its exact matrix height bound. -/
theorem canonical_region_height_bound (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) (ht : Matrix.trace A.val≠0) (z : ℍ) (hz :
      z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) :
    2*|A 1 0| *z.im< |Matrix.trace A.val|+2 := by
  have hq:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_mem_quadratic A ht z).mp hz
  have hk : 0< |A 1 0| := abs_pos.mpr hc
  have hm : A 1 0*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic A z<2*|A 1 0| *z.im := by
    calc
      _≤|A 1 0*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic A z| := le_abs_self _
      _=|A 1 0| *|_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic A z| := abs_mul _ _
      _< |A 1 0| *(2*z.im) := mul_lt_mul_of_pos_left hq hk
      _=_ := by ring
  have he : A 1 0*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic A z=
      (A 1 0)^2*((z.re-(A 0 0-A 1 1)/(2*A 1 0))^2+z.im^2)-
        ((Matrix.trace A.val)^2-4)/4 := by
    rw [canonical_quadratic_centered A hc z]
    field_simp
  have hs : (2*|A 1 0| *z.im-2)^2< |Matrix.trace A.val|^2 := by
    rw [he] at hm
    have hn:=mul_nonneg (sq_nonneg (A 1 0))
      (sq_nonneg (z.re-(A 0 0-A 1 1)/(2*A 1 0)))
    nlinarith [hm,hn,sq_abs (A 1 0),sq_abs (Matrix.trace A.val)]
  by_contra h
  have hu : |Matrix.trace A.val|≤2*|A 1 0| *z.im-2 := by linarith
  have hsq:=mul_self_le_mul_self (abs_nonneg (Matrix.trace A.val)) hu
  nlinarith [hs,hsq]

/-- Squared Euclidean coordinates characterize the actual semicircle carrier. -/
theorem halfPlane_circle_mem_sq (m r : ℝ) (hr : 0<r) (z : ℍ) :
    z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle m r hr).carrier ↔ (z.re-m)^2+z.im^2=r^2 := by
  change ‖(z:ℂ)-(m:ℂ)‖=r ↔ _
  rw [←sq_eq_sq₀ (norm_nonneg _) hr.le,←Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.ofReal_re,Complex.sub_im,
    Complex.ofReal_im,sub_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring_nf

/-- The actual hyperbolic axis is its constructed finite-ended semicircle, with exact radius. -/
theorem hyperbolic_axis_finite_circle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2) (hc : A 1
      0≠0) :
    ∃ (r : ℝ) (hr : 0<r),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA ht=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle ((A 0 0-A 1 1)/(2*A 1 0)) r hr ∧
      (A 1 0*r)^2=((Matrix.trace A.val)^2-4)/4 := by
  let r:=Real.sqrt ((Matrix.trace A.val)^2-4)/(2*|A 1 0|)
  have hdelta : 0<(Matrix.trace A.val)^2-4 := by linarith
  have hr : 0<r := div_pos (Real.sqrt_pos.mpr hdelta) (by positivity)
  have hrsq : r^2=((Matrix.trace A.val)^2-4)/(4*(A 1 0)^2) := by
    dsimp only [r]
    rw [div_pow,Real.sq_sqrt hdelta.le,mul_pow,sq_abs]
    norm_num
  refine ⟨r,hr,?_,?_⟩
  · apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    ext z
    rw [hyperbolic_axis_quadratic_zero A hA ht z]
    rw [halfPlane_circle_mem_sq]
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic A z=
        A 1 0*((z.re-(A 0 0-A 1 1)/(2*A 1 0))^2+z.im^2-r^2) := by
      rw [canonical_quadratic_centered A hc z,hrsq]
      field_simp
    rw [he,mul_eq_zero]
    simp only [hc,false_or,sub_eq_zero]
  · rw [mul_pow,hrsq]
    field_simp

/-- Actual translation has the expected native real coordinate. -/
theorem canonical_translation_re (t : ℝ) (z : ℍ) : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z).re=z.re+t := by
  change (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z : ℍ):ℂ)).re=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
  simp

/-- A genuine semicircular axis stable under a nonzero parabolic translation has radius at most half its step. -/
theorem circle_translation_stability_radius (m r t : ℝ) (hr : 0<r) (ht : t≠0)
    (hs : (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z) ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle m r hr).carrier=
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle m r hr).carrier ∨
      Disjoint ((fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z) ''
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle m r hr).carrier)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle m r hr).carrier) : 2*r≤|t| := by
  rcases hs with he|hd
  · let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe m r hr
    have hz : z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle m r hr).carrier := by
      rw [halfPlane_circle_mem_sq]
      change (m-m)^2+r^2=r^2
      ring
    have htz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle m r hr).carrier := by
      rw [←he]
      exact mem_image_of_mem _ hz
    have hq:=(halfPlane_circle_mem_sq m r hr _).mp htz
    rw [canonical_translation_re,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_im] at hq
    change (m+t-m)^2+r^2=r^2 at hq
    exact False.elim (ht (by nlinarith [hq]))
  · by_contra hn
    have hlt : |t|<2*r := lt_of_not_ge hn
    have hsquare:=(sq_lt_sq₀ (abs_nonneg t) (by positivity : 0≤2*r)).mpr hlt
    rw [sq_abs] at hsquare
    let y:=Real.sqrt (r^2-(t/2)^2)
    have hy : 0<y := Real.sqrt_pos.mpr (by nlinarith [hsquare])
    have hysq : y^2=r^2-(t/2)^2 := Real.sq_sqrt (by nlinarith [hsquare])
    let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (m+t/2) y hy
    let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (m-t/2) y hy
    have hz : z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle m r hr).carrier := by
      rw [halfPlane_circle_mem_sq]
      change (m+t/2-m)^2+y^2=r^2
      nlinarith [hysq]
    have hq : q∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle m r hr).carrier := by
      rw [halfPlane_circle_mem_sq]
      change (m-t/2-m)^2+y^2=r^2
      nlinarith [hysq]
    have heq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•q=z := by
      apply UpperHalfPlane.ext_re_im
      · rw [canonical_translation_re]
        change m-t/2+t=m+t/2
        ring
      · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_im]
        rfl
    exact Set.disjoint_left.mp hd ⟨q,hq,heq⟩ hz

/-- Original simplicity implies the exact native parabolic-step radius constraint. -/
theorem simple_hyperbolic_translation_radius (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1)
    (htA : 4<(Matrix.trace A.val)^2) (hSimple : IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (t : ℝ) (ht : t≠0) (htm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H)
    (m r : ℝ) (hr : 0<r) (haxis : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle m r hr) :
    2*r≤|t| := by
  have hs:=hSimple.2.2 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) htm
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis A hA
    htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_image_realSL] at hs
  have hn : (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
    t•z) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier=
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier ∨
      Disjoint ((fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z) ''
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier := by
    rcases hs with he|hd
    · exact Or.inl (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective.image_injective he)
    · exact Or.inr ((Set.disjoint_image_iff
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective).mp hd)
  rw [haxis] at hn
  exact circle_translation_stability_radius m r t hr ht hn

end LowDimensionalTopology.Geometry.Fuchsian
