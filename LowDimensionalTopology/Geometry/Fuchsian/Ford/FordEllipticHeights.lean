/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordRegions
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.HorocyclicCycleBounds
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveEllipticAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem realSL_fixed_denominator_coordinates (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (z : ℍ) (hfix : A•z=z) :
    Complex.normSq (_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A z)=1 ∧ 2*A 1 0*z.re=A 0 0-A 1 1 := by
  have hd : _root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A z≠0:=UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ A) z
  have hn : 0<Complex.normSq (_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A
    z):=Complex.normSq_pos.mpr hd
  have him:=_root_.LowDimensionalTopology.Geometry.Fuchsian.realSL_im_action A z
  rw [hfix] at him
  have hn1 : Complex.normSq (_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A z)=1:=by
    have he:=(eq_div_iff hn.ne').mp him
    apply mul_left_cancel₀ z.im_ne_zero
    simpa only [mul_one] using he
  have hpoly:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_fixed_iff A z).mp hfix
  have hi:=congrArg Complex.im hpoly
  simp only [Complex.add_im,Complex.sub_im,Complex.mul_im,pow_two,
    Complex.ofReal_re,Complex.ofReal_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
    Complex.sub_re,Complex.zero_im,sub_zero,zero_mul,add_zero] at hi
  have he : z.im*(2*A 1 0*z.re+A 1 1-A 0 0)=0:=by nlinarith only [hi]
  have hr:=(mul_eq_zero.mp he).resolve_left z.im_ne_zero
  exact ⟨hn1,by linarith only [hr]⟩

theorem realSLDenominator_mul_translation (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (t : ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator (A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) z=_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A z+(t*A 1 0:ℝ) := by
  change ((((A.val*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t).val) 1 0:ℝ):ℂ)*(z:ℂ)+
    (((A.val*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t).val) 1 1:ℝ):ℂ))=
    (A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ)+(t*A 1 0:ℝ)
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem hTranslationSL_neg_one_inverse : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  apply Subtype.ext
  change !![1,(-1:ℝ);0,1]*!![1,(1:ℝ);0,1]=1
  norm_num
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The two adjacent unit translates of a fixed-point matrix force a genuine
Ford elliptic vertex's trace to be bounded by its lower-left matrix entry. -/
theorem fordExterior_fixed_trace_le_entry (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1∈G) (A : Matrix.SpecialLinearGroup (Fin 2)
      ℝ) (hA : A∈G)
    (z : ℍ) (hz : z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.fordExterior G) (hfix : A•z=z) (hc : A 1 0≠0) :
    (Matrix.trace A.val)^2≤(A 1 0)^2 := by
  obtain ⟨hn,hcoord⟩:=realSL_fixed_denominator_coordinates A z hfix
  have hTi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)∈G:=by rw [hTranslationSL_neg_one_inverse];exact G.inv_mem hT
  have hp:=hz ⟨A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1,G.mul_mem hA hT⟩
  have hm:=hz ⟨A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1),G.mul_mem hA hTi⟩
  have hp2 : 1≤Complex.normSq (_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator (A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) z):=by
    rw [Complex.normSq_eq_norm_sq];nlinarith only [hp]
  have hm2 : 1≤Complex.normSq (_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator (A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)) z):=by
    rw [Complex.normSq_eq_norm_sq];nlinarith only [hm]
  rw [realSLDenominator_mul_translation] at hp2 hm2
  change 1≤Complex.normSq ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ)+(1*A 1 0:ℝ)) at hp2
  change 1≤Complex.normSq ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ)+((-1)*A 1 0:ℝ)) at hm2
  have hnorm : Complex.normSq (_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A z)=
      (A 1 0*z.re+A 1 1)^2+(A 1 0*z.im)^2:=by
    change Complex.normSq ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ))=_
    simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im,zero_mul,add_zero,sub_zero]
    ring
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im,zero_mul,add_zero,sub_zero] at hp2 hm2
  rw [Matrix.trace_fin_two]
  have hcc:=congrArg (fun r : ℝ=>A 1 0*r) hcoord
  have hp' : 0≤(A 1 0)^2+A 1 0*(A 0 0+A 1 1):=by nlinarith [hp2,hnorm,hn,hcc]
  have hm' : 0≤(A 1 0)^2-A 1 0*(A 0 0+A 1 1):=by nlinarith [hm2,hnorm,hn,hcc]
  have hmul:=mul_nonneg hp' hm'
  have hc2 : 0<(A 1 0)^2:=sq_pos_of_ne_zero hc
  apply (mul_le_mul_iff_right₀ hc2).mp
  nlinarith only [hmul]

/-- The true fixed-point equations give the exact trace-height relation. -/
theorem realSL_fixed_trace_height_identity (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (z : ℍ) (hfix : A•z=z) :
    4*(A 1 0)^2*z.im^2+(Matrix.trace A.val)^2=4 := by
  obtain ⟨hn,hcoord⟩:=realSL_fixed_denominator_coordinates A z hfix
  have hn' : (A 1 0*z.re+A 1 1)^2+(A 1 0*z.im)^2=1:=by
    change Complex.normSq ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ))=1 at hn
    simpa only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im,zero_mul,add_zero,sub_zero,pow_two] using hn
  have ht : 2*(A 1 0*z.re+A 1 1)=Matrix.trace A.val:=by
    rw [Matrix.trace_fin_two]
    linarith only [hcoord]
  have hs:=congrArg (fun r : ℝ=>r^2) ht
  nlinarith only [hn',hs]

/-- The original Ford inequalities force the sharp elliptic height bound
from the actual fixed point and the genuine primitive rotation trace. -/
theorem fordExterior_elliptic_height_bound (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1∈G) (A : Matrix.SpecialLinearGroup (Fin 2)
      ℝ) (hA : A∈G)
    (z : ℍ) (hz : z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.fordExterior G) (hfix : A•z=z) (hc : A 1 0≠0)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) (Real.pi/2))
    (htrace : (Matrix.trace A.val)^2=4*Real.cos θ^2) : z.im≤Real.tan θ/2 := by
  have htr:=fordExterior_fixed_trace_le_entry G hT A hA z hz hfix hc
  have hid:=realSL_fixed_trace_height_identity A z hfix
  have hmul:=mul_le_mul_of_nonneg_right htr (sq_nonneg z.im)
  have hsincos:=Real.sin_sq_add_cos_sq θ
  have hs : (2*Real.cos θ*z.im)^2≤Real.sin θ^2:=by nlinarith only [hid,hmul,htrace,hsincos]
  have hcos : 0<Real.cos θ:=Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have hsin : 0<Real.sin θ:=Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2,Real.pi_pos])
  have hl:=(sq_le_sq₀ (le_of_lt (mul_pos (mul_pos (by norm_num) hcos) z.im_pos)) hsin.le).mp hs
  rw [Real.tan_eq_sin_div_cos,div_div,le_div_iff₀ (mul_pos hcos (by norm_num))]
  nlinarith only [hl]


/-- The actual sphere-point stabilizer of a half-plane interior point is finite. -/
theorem halfPlanePointStabilizer_finite (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) (z : ℍ) :
    Finite (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) := by
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  have hle : K≤H:=fun f hf=>((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H _
    f).mp hf).1
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_finite_of_common_H3_fixed K (discreteMobius_subgroup_of_le H K hd hle)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z)
  intro f hf
  obtain ⟨hfH,hfz⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H _ f).mp hf
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL f (hpres f hfH)
  have hfix : A•z=z:=by
    rw [←hA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action] at hfz
    exact UpperHalfPlane.ext (OnePoint.coe_eq_coe.mp hfz)
  rw [←hA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_realSL,hfix]

/-- The same actual point stabilizer is cyclic. -/
theorem halfPlanePointStabilizer_isCyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) (z : ℍ) :
    IsCyclic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) := by
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  let : Finite K:=halfPlanePointStabilizer_finite H hd hpres z
  apply finiteMobius_preserves_disc_isCyclic K _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc
  intro f
  exact hpres f.val ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H _ f.val).mp
    f.property).1

/-- The actual order of the original group's stabilizer of the literal point. -/
def fordPointOrder (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (z : ℍ) : ℕ :=
  Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H
    ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))

/-- Every actual Ford elliptic point of stabilizer order at least three obeys
the source height bound, without an assumed cycle angle budget. -/
theorem mobiusFordExterior_elliptic_point_height (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (z : ℍ) (hz : z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior H) (hq : 3≤fordPointOrder H z) :
    z.im≤Real.tan (Real.pi/fordPointOrder H z)/2 := by
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  let : Finite K:=halfPlanePointStabilizer_finite H hd hpres z
  let : IsCyclic K:=halfPlanePointStabilizer_isCyclic H hd hpres z
  have hnontriv : ∃ f : K,f≠1:=by
    by_contra hn
    push Not at hn
    let : Subsingleton K:=⟨fun a b=>(hn a).trans (hn b).symm⟩
    have hcard : Nat.card K=1:=Nat.card_unique
    change 3≤Nat.card K at hq
    omega
  obtain ⟨f,hf⟩:=hnontriv
  have hf0 : f.val≠1:=by intro he;exact hf (Subtype.ext he)
  obtain ⟨g,hg,hgen,_hleast,htrace,_⟩:=primitive_finite_cyclic_exists_least_rotation K
    f.val f.property hf0
  have hg0 : g≠1:=by
    intro he
    have hmem : f.val∈Subgroup.zpowers g:=by rw [hgen];exact f.property
    simp only [he,Subgroup.zpowers_one_eq_bot,Subgroup.mem_bot] at hmem
    exact hf0 hmem
  have hgE:=primitive_elliptic_of_finite_subgroup K g hg hg0
  obtain ⟨hgH,hgz⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H _ g).mp hg
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g (hpres g hgH)
  have hfix : A•z=z:=by
    rw [←hA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action] at hgz
    exact UpperHalfPlane.ext (OnePoint.coe_eq_coe.mp hgz)
  have hAH : A∈H.comap _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius:=by change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H;simpa only [hA] using hgH
  have hTH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1∈H.comap _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)∈H
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation]
    exact hT
  have ht : (Matrix.trace A.val)^2<4:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A (hA
    ▸ hg0)).mp (hA ▸ hgE)
  have hc : A 1 0≠0:=by
    intro hc
    have hdet:=A.det_coe
    rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at hdet
    rw [Matrix.trace_fin_two] at ht
    nlinarith only [ht,hdet,sq_nonneg (A 0 0-A 1 1)]
  have htraceA : (Matrix.trace A.val)^2=4*Real.cos (Real.pi/fordPointOrder H z)^2:=by
    have hs:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace A
    rw [hA,htrace] at hs
    exact (Complex.ofReal_injective hs).symm
  have hqR : (3:ℝ)≤fordPointOrder H z:=by exact_mod_cast hq
  have hq0 : (0:ℝ)<fordPointOrder H z:=by linarith only [hqR]
  have hθ : Real.pi/fordPointOrder H z∈Ioo (0:ℝ) (Real.pi/2):=by
    constructor
    · exact div_pos Real.pi_pos hq0
    · apply (div_lt_div_iff₀ hq0 (by norm_num : (0:ℝ)<2)).mpr
      nlinarith only [Real.pi_pos,hqR]
  exact fordExterior_elliptic_height_bound (H.comap
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius) hTH A hAH z hz hfix hc
    _ hθ htraceA

/-- height clause, on the literal original Ford circle construction. -/
theorem mobiusFordCircle_elliptic_vertex_height (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) (x₀ : ℝ)
    (z : ℍ) (hz : z∈closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordCircleDomain H x₀)) (hq :
      3≤fordPointOrder H z) :
    z.im≤Real.tan (Real.pi/fordPointOrder H z)/2 := by
  apply mobiusFordExterior_elliptic_point_height H hd hT hpres z _ hq
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordCircleDomain_eq H hd hT] at hz
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.closure_fordDomain_subset_exterior _ x₀ hz


/-- The equivalent genuine unit-parabolic half-displacement clause. -/
theorem mobiusFordCircle_elliptic_vertex_displacement (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) (x₀ : ℝ)
    (z : ℍ) (hz : z∈closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordCircleDomain H x₀)) (hq :
      3≤fordPointOrder H z) :
    Real.cot (Real.pi/fordPointOrder H z)≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) z := by
  have h:=unitTranslation_half_displacement_lower_of_height z
    (Real.tan (Real.pi/fordPointOrder H z)/2)
    (mobiusFordCircle_elliptic_vertex_height H hd hT hpres x₀ z hz hq)
  have he : 1/(2*(Real.tan (Real.pi/fordPointOrder H z)/2))=
      Real.cot (Real.pi/fordPointOrder H z):=by
    rw [←Real.tan_inv_eq_cot,inv_eq_one_div]
    congr 1
    ring
  rwa [he] at h


end LowDimensionalTopology.Geometry.Fuchsian
