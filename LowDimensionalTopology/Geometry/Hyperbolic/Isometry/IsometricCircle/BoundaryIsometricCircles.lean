/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.IsometricCircle.GeneralizedIsometricCircles
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HalfPlaneLorentzReflections
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenIdealHull
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeneralizedReflectionGeometry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The ideal-basepoint infinity locus, using the actual height of the original image. -/
def hInfinityIsometricCircle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Set ℍ :=
  {z | (A • z).im=z.im}

/-- The genuine real-centred semicircle with the classical centre and radius. -/
def hInfinityIsometricLine (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hc : A 1 0≠0) :
    HalfPlaneLine :=
  .circle (-A 1 1/A 1 0) (1/|A 1 0|) (one_div_pos.mpr (abs_pos.mpr hc))

/-- Height preservation is exactly unit Euclidean distortion for the original real matrix. -/
theorem mem_hInfinityIsometricCircle_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    z∈hInfinityIsometricCircle A ↔ ((A 1 0*z.re+A 1 1)^2+(A 1 0*z.im)^2)=1 := by
  change (A • z).im=z.im ↔ _
  rw [sl2_im_smul]
  have hd : Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ A) z)≠0 :=
    (Complex.normSq_pos.mpr (UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ A) z)).ne'
  rw [div_eq_iff hd]
  have he : Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ A) z)=
      (A 1 0*z.re+A 1 1)^2+(A 1 0*z.im)^2 := by
    change Complex.normSq ((A 1 0:ℂ)*z+(A 1 1:ℂ))= _
    simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
      sub_zero,add_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    ring
  rw [he]
  constructor <;> intro h
  · exact (mul_left_cancel₀ z.im_ne_zero (by simpa only [mul_one] using h.symm))
  · rw [h,mul_one]

/-- The actual infinity locus is the whole genuine classical geodesic. -/
theorem hInfinityIsometricLine_carrier (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) : (hInfinityIsometricLine A hc).carrier=hInfinityIsometricCircle A := by
  ext z
  rw [mem_hInfinityIsometricCircle_iff]
  change ‖(z:ℂ)-((-A 1 1/A 1 0:ℝ):ℂ)‖=1/|A 1 0| ↔ _
  rw [←sq_eq_sq₀ (norm_nonneg _) (one_div_pos.mpr (abs_pos.mpr hc)).le,norm_sub_real_sq,
    div_pow,one_pow,sq_abs]
  have he : (A 1 0)^2*((z.re- -A 1 1/A 1 0)^2+z.im^2)=
      (A 1 0*z.re+A 1 1)^2+(A 1 0*z.im)^2 := by
    field_simp
    ring
  constructor
  · intro h
    rw [←he,h]
    exact mul_one_div_cancel (pow_ne_zero 2 hc)
  · intro h
    apply (eq_div_iff (pow_ne_zero 2 hc)).mpr
    rw [mul_comm,he,h]

/-- A real-centred circle reflection preserves height exactly on its actual fixed geodesic. -/
theorem circleReflection_preserves_height_iff (c r : ℝ) (hr : 0<r) (z : ℍ) :
    (circleReflection c r hr z).im=z.im ↔ z∈(HalfPlaneLine.circle c r hr).carrier := by
  rw [circleReflection_im]
  have hd : (z.re-c)^2+z.im^2≠0 := by nlinarith [sq_nonneg (z.re-c),sq_pos_of_pos z.im_pos]
  rw [div_eq_iff hd]
  constructor
  · intro h
    apply norm_sub_real_eq_of_sq hr
    nlinarith [z.im_pos]
  · intro h
    have hs:=norm_sub_real_eq_radius_sq h
    rw [hs]
    ring

/-- The ideal-basepoint circle has a true reflection-factor construction, with the other
factor a vertical geodesic through the actual ideal point infinity. -/
theorem hInfinityIsometricLine_reflection_factor (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) :
    (A • · : ℍ→ℍ)=(HalfPlaneLine.vertical ((A 0 0-A 1 1)/(2*A 1 0))).reflection ∘
      (hInfinityIsometricLine A hc).reflection := by
  let t:=(A 0 0-A 1 1)/(2*A 1 0)
  let L:=HalfPlaneLine.vertical t
  let M:=hInfinityIsometricLine A hc
  let u : ℝˣ:=Units.mk0 (1/A 1 0) (one_div_ne_zero hc)
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hm : L.reflectionMatrix*M.reflectionMatrix=
      Matrix.GeneralLinearGroup.scalar (Fin 2) u*Matrix.SpecialLinearGroup.mapGL ℝ A := by
    apply Units.ext
    change (!![-1,2*t;0,1] : Matrix (Fin 2) (Fin 2) ℝ)*
      !![-A 1 1/A 1 0,(1/|A 1 0|)^2-(-A 1 1/A 1 0)^2;1,-(-A 1 1/A 1 0)]=
      Matrix.scalar (Fin 2) (1/A 1 0)*A.val
    rw [div_pow,one_pow,sq_abs]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply,Fin.sum_univ_two,Matrix.scalar_apply,Matrix.diagonal_apply,t]
    all_goals field_simp [hc]
    all_goals nlinarith [hdet]
  funext z
  change (Matrix.SpecialLinearGroup.mapGL ℝ A)•z=L.reflection (M.reflection z)
  rw [←M.reflectionMatrix_action,←L.reflectionMatrix_action,←mul_smul,hm,mul_smul,
    UpperHalfPlane.glScalar_smul]

/-- A map moving infinity genuinely changes the height at some actual interior point. -/
theorem hInfinityIsometricCircle_exists_height_ne (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) : ∃z : ℍ,(A • z).im≠z.im := by
  let r:=1/|A 1 0|
  have hr : 0<r:=one_div_pos.mpr (abs_pos.mpr hc)
  let z : ℍ:=UpperHalfPlane.mk ⟨-A 1 1/A 1 0,2*r⟩ (by positivity)
  refine ⟨z,?_⟩
  intro h
  have hz : z∈(hInfinityIsometricLine A hc).carrier := by
    rw [hInfinityIsometricLine_carrier]
    exact h
  have he:=norm_sub_real_eq_radius_sq hz
  change (-A 1 1/A 1 0- -A 1 1/A 1 0)^2+(2*r)^2=r^2 at he
  nlinarith [sq_pos_of_pos hr]

/-- Every genuine two-reflection factorization whose left line passes through infinity
has exactly the actual infinity-isometric circle as its right reflection line. -/
theorem hInfinityIsometricCircle_factor_carrier (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) (L M : HalfPlaneLine) (hL : (∞:Mobius.ExtendedComplex)∈L.idealEndpoints)
    (hfact : (A • · : ℍ→ℍ)=L.reflection ∘ M.reflection) :
    M.carrier=hInfinityIsometricCircle A := by
  cases L with
  | circle c r hr =>
    simp only [circle_idealEndpoints,mem_insert_iff,mem_singleton_iff] at hL
    exact False.elim (hL.elim (OnePoint.infty_ne_coe _) (OnePoint.infty_ne_coe _))
  | vertical t =>
    cases M with
    | vertical s =>
      obtain ⟨z,hz⟩:=hInfinityIsometricCircle_exists_height_ne A hc
      apply False.elim
      apply hz
      rw [congrFun hfact z]
      simp only [Function.comp_apply,HalfPlaneLine.reflection,verticalReflection_im]
    | circle c r hr =>
      ext z
      change z∈(HalfPlaneLine.circle c r hr).carrier ↔ (A • z).im=z.im
      rw [←circleReflection_preserves_height_iff,congrFun hfact z]
      simp only [Function.comp_apply,HalfPlaneLine.reflection,verticalReflection_im]

/-- Existence and uniqueness of the actual reflection-defined circle at the genuine ideal
basepoint infinity; neither an interior-point surrogate nor a supplied factorization is used. -/
theorem existsUnique_hInfinityIsometricCircle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) : ∃!M : HalfPlaneLine,∃L : HalfPlaneLine,
      (∞:Mobius.ExtendedComplex)∈L.idealEndpoints ∧ (A • · : ℍ→ℍ)=L.reflection ∘ M.reflection := by
  refine ⟨hInfinityIsometricLine A hc,?_,?_⟩
  · refine ⟨.vertical ((A 0 0-A 1 1)/(2*A 1 0)),?_,hInfinityIsometricLine_reflection_factor A hc⟩
    rw [vertical_idealEndpoints]
    exact mem_insert_of_mem _ (mem_singleton _)
  · rintro M ⟨L,hL,hfact⟩
    exact HalfPlaneLine.carrier_injective ((hInfinityIsometricCircle_factor_carrier A hc L M hL hfact).trans
      (hInfinityIsometricLine_carrier A hc).symm)

/-- The actual extended-plane reflection-factor condition, including finite interior,
ideal and reflected exterior base points. -/
def IsHIsometricReflectionLine (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : Mobius.ExtendedComplex) (M : HalfPlaneLine) : Prop :=
  ∃L : HalfPlaneLine,w∈L.extendedCircle.val ∧ (A • · : ℍ→ℍ)=L.reflection ∘ M.reflection

/-- The original real matrix has exactly the usual full extended-plane fractional action. -/
theorem realSLMobius_extended_action (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : Mobius.ExtendedComplex) :
    (realSLMobius A).val w=Mobius.fractionalLinear (complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ
      A)) w := by
  change (Mobius.mobiusMatrixProjection (Matrix.SpecialLinearGroup.toGL
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom A))).val w= _
  rw [realSLMobius_matrix,Mobius.mobiusMatrixProjection_coe]

/-- A genuine real matrix moves the ideal point infinity exactly when its lower-left entry is nonzero. -/
theorem realSLMobius_infty_ne_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (realSLMobius A).val ∞≠∞ ↔ A 1 0≠0 := by
  rw [realSLMobius_extended_action,Mobius.fractionalLinear_infty]
  change (if (A 1 0:ℂ)=0 then ∞ else ((((A 0 0:ℂ)/(A 1 0:ℂ)):ℂ):Mobius.ExtendedComplex))≠∞ ↔ _
  by_cases hc : A 1 0=0
  · simp only [hc,Complex.ofReal_zero,ite_true,ne_eq,not_true_eq_false]
  · simp only [Complex.ofReal_ne_zero.mpr hc,ite_false,OnePoint.coe_ne_infty,ne_eq,hc,not_false_eq_true]

/-- Native conjugacy carries the true extended-plane reflection-factor condition to the
actual image geodesic and actual image basepoint. -/
theorem IsHIsometricReflectionLine.conjugation
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {w : Mobius.ExtendedComplex} {M : HalfPlaneLine}
    (h : IsHIsometricReflectionLine A w M) (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsHIsometricReflectionLine (q*A*q⁻¹) ((realSLMobius q).val w)
      (M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)) := by
  obtain ⟨L,hw,hfact⟩:=h
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ q
  have hg : 0<g.val.det := by change 0<q.val.det;rw [q.property];norm_num
  refine ⟨L.realGLMap g,?_,?_⟩
  · rw [realSLMobius_extended_action]
    have he:=L.extendedCircle_image_realGL (L.realGLMap g) g hg (L.realGLMap_carrier g).symm
    rw [←he]
    exact mem_image_of_mem _ hw
  · funext z
    have hM:=M.reflection_realGL_conjugation g z
    have hL:=L.reflection_realGL_conjugation g ((M.realGLMap g).reflection z)
    rw [←hM,inv_smul_smul] at hL
    change (q*A*q⁻¹)•z=(L.realGLMap g).reflection ((M.realGLMap g).reflection z)
    rw [←hM,←hL]
    change (q*A*q⁻¹)•z=q•L.reflection (M.reflection (q⁻¹•z))
    have hfz:=congrFun hfact (q⁻¹•z)
    change A•(q⁻¹•z)=L.reflection (M.reflection (q⁻¹•z)) at hfz
    rw [←hfz]
    simp only [mul_smul]

/-- The full generalized h-line contains infinity exactly when its true ideal endpoint set does. -/
theorem infty_mem_hLine_extendedCircle_iff (L : HalfPlaneLine) :
    (∞:Mobius.ExtendedComplex)∈L.extendedCircle.val ↔ (∞:Mobius.ExtendedComplex)∈L.idealEndpoints := by
  cases L with
  | vertical x => simp [HalfPlaneLine.extendedCircle,vertical_idealEndpoints]
  | circle c r hr => simp [HalfPlaneLine.extendedCircle,circle_idealEndpoints]

/-- The whole geometric h-line is invariant under reflection across the actual real boundary. -/
theorem hLine_extendedCircle_conjugation_iff (L : HalfPlaneLine) (w : Mobius.ExtendedComplex) :
    Mobius.complexConjugation w∈L.extendedCircle.val ↔ w∈L.extendedCircle.val := by
  cases w using OnePoint.rec with
  | infty => rw [Mobius.complexConjugation_infty]
  | coe z =>
    rw [Mobius.complexConjugation_coe]
    cases L with
    | vertical x => simp [HalfPlaneLine.extendedCircle,Complex.inner]
    | circle c r hr =>
      simp only [HalfPlaneLine.extendedCircle,Mobius.complexCircle_coe]
      rw [show conj z-(c:ℂ)=conj (z-(c:ℂ)) by simp,Complex.norm_conj]

/-- Exterior basepoints give exactly the same genuine reflection line as their boundary-reflected point. -/
theorem isHIsometricReflectionLine_boundary_reflection_iff
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : Mobius.ExtendedComplex) (M : HalfPlaneLine) :
    IsHIsometricReflectionLine A (Mobius.complexConjugation w) M ↔ IsHIsometricReflectionLine A w M := by
  constructor <;> rintro ⟨L,hw,hfact⟩
  · exact ⟨L,(hLine_extendedCircle_conjugation_iff L w).mp hw,hfact⟩
  · exact ⟨L,(hLine_extendedCircle_conjugation_iff L w).mpr hw,hfact⟩

/-- An actual moved interior point gives a unique genuine reflection-defined line. -/
theorem existsUnique_isHIsometricReflectionLine_interior
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℍ) (hw : A•w≠w) :
    ∃!M : HalfPlaneLine,IsHIsometricReflectionLine A ((w:ℂ):Mobius.ExtendedComplex) M := by
  obtain ⟨M,⟨hM,L,hwL,hfact⟩,_⟩:=existsUnique_hWIsometricCircle A w hw
  refine ⟨M,⟨L,(L.mem_extendedCircle w).mpr hwL,hfact⟩,?_⟩
  rintro N ⟨L,hwL,hN⟩
  have hfix : L.reflection w=w:=(L.reflection_fixed_iff w).mpr ((L.mem_extendedCircle w).mp hwL)
  have hswap : N.reflection w=A⁻¹•w := by
    apply (MulAction.injective A)
    change A•N.reflection w=A•(A⁻¹•w)
    calc
      A•N.reflection w=L.reflection (N.reflection (N.reflection w)):=congrFun hN _
      _=w:=by rw [N.reflection_involutive,hfix]
      _=A•(A⁻¹•w):=(smul_inv_smul A w).symm
  have hww : w≠A⁻¹•w := by
    intro h
    apply hw
    have hh:=congrArg (fun z:ℍ=>A•z) h
    simpa only [smul_inv_smul] using hh
  exact HalfPlaneLine.carrier_injective
    ((N.carrier_eq_equidistant_of_reflection_swap w (A⁻¹•w) hww hswap).trans hM.symm)

/-- The full actual real fractional action commutes with geometric boundary reflection. -/
theorem realSLMobius_commutes_complexConjugation
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : Mobius.ExtendedComplex) :
    (realSLMobius A).val (Mobius.complexConjugation w)=Mobius.complexConjugation ((realSLMobius A).val w) := by
  let g:=complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ A)
  have hg : g.map (starRingEnd ℂ)=g := by
    apply Units.ext
    ext i j
    change star ((A i j:ℝ):ℂ)=((A i j:ℝ):ℂ)
    simp only [Complex.star_def,Complex.conj_ofReal]
  have he:=Mobius.complexConjugation_fractionalLinear g
  rw [hg] at he
  rw [realSLMobius_extended_action,realSLMobius_extended_action]
  exact (congrArg (fun f : Equiv.Perm Mobius.ExtendedComplex=>f w) he).symm

/-- Every genuine moved ideal basepoint admits a unique actual reflection-factor line. -/
theorem existsUnique_isHIsometricReflectionLine_boundary
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : Mobius.ExtendedComplex)
    (hw : w∈halfPlaneIdealBoundary) (hmove : (realSLMobius A).val w≠w) :
    ∃!M : HalfPlaneLine,IsHIsometricReflectionLine A w M := by
  obtain ⟨q,hqw⟩:=realSLMobius_exists_send_to_infty w hw
  let B:=q*A*q⁻¹
  have hqact : realSLMobius q•w=∞:=hqw
  have hBm : (realSLMobius B).val ∞≠∞ := by
    intro h
    apply hmove
    apply (realSLMobius q).val.injective
    have hconj : realSLMobius B•(realSLMobius q•w)=
        realSLMobius q•(realSLMobius A•w) := by
      simp only [B,map_mul,map_inv,mul_smul,inv_smul_smul]
    rw [hqact] at hconj
    exact hconj.symm.trans (h.trans hqw.symm)
  have hBc : B 1 0≠0:=(realSLMobius_infty_ne_iff B).mp hBm
  obtain ⟨M,hM,huniq⟩:=existsUnique_hInfinityIsometricCircle B hBc
  have hMp : IsHIsometricReflectionLine B ∞ M := by
    obtain ⟨L,hL,hfact⟩:=hM
    exact ⟨L,(infty_mem_hLine_extendedCircle_iff L).mpr hL,hfact⟩
  have hback : q⁻¹*B*(q⁻¹)⁻¹=A := by dsimp only [B];group
  have hwback : (realSLMobius q⁻¹).val ∞=w := by
    rw [map_inv]
    change (realSLMobius q)⁻¹•∞=w
    rw [←hqact,inv_smul_smul]
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ q
  have hginv : Matrix.SpecialLinearGroup.mapGL ℝ q⁻¹=g⁻¹:=map_inv _ _
  refine ⟨M.realGLMap g⁻¹,?_,?_⟩
  · simpa only [hback,hwback,hginv] using hMp.conjugation q⁻¹
  · intro N hN
    have hNq:=hN.conjugation q
    rw [hqw] at hNq
    obtain ⟨L,hL,hfact⟩:=hNq
    have hNM : N.realGLMap g=M :=huniq _ ⟨L,(infty_mem_hLine_extendedCircle_iff L).mp hL,hfact⟩
    calc N=(N.realGLMap g).realGLMap g⁻¹:=(N.realGLMap_inv g).symm
      _=M.realGLMap g⁻¹:=by rw [hNM]

/-- Every point of the full extended complex plane moved by the original isometry admits
one genuine geometric reflection-factor line, including all ideal and exterior cases. -/
theorem existsUnique_isHIsometricReflectionLine
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : Mobius.ExtendedComplex)
    (hmove : (realSLMobius A).val w≠w) :
    ∃!M : HalfPlaneLine,IsHIsometricReflectionLine A w M := by
  cases w using OnePoint.rec with
  | infty =>
    exact existsUnique_isHIsometricReflectionLine_boundary A ∞ (by simp [halfPlaneIdealBoundary]) hmove
  | coe z =>
    rcases lt_trichotomy 0 z.im with hz | hz | hz
    · let p : ℍ:=UpperHalfPlane.mk z hz
      apply existsUnique_isHIsometricReflectionLine_interior A p
      intro h
      apply hmove
      change (realSLMobius A).val ((p:ℂ):Mobius.ExtendedComplex)=((p:ℂ):Mobius.ExtendedComplex)
      rw [realSLMobius_action]
      exact congrArg (fun p:ℍ=>((p:ℂ):Mobius.ExtendedComplex)) h
    · apply existsUnique_isHIsometricReflectionLine_boundary A z
      · rw [coe_mem_halfPlaneIdealBoundary]
        exact hz.symm
      · exact hmove
    · let p : ℍ:=UpperHalfPlane.mk (conj z) (by simpa only [Complex.conj_im] using neg_pos.mpr hz)
      have hp : A•p≠p := by
        intro h
        have hc : (realSLMobius A).val (Mobius.complexConjugation (z:Mobius.ExtendedComplex))=
            Mobius.complexConjugation (z:Mobius.ExtendedComplex) := by
          rw [Mobius.complexConjugation_coe]
          change (realSLMobius A).val ((p:ℂ):Mobius.ExtendedComplex)=((p:ℂ):Mobius.ExtendedComplex)
          rw [realSLMobius_action]
          exact congrArg (fun p:ℍ=>((p:ℂ):Mobius.ExtendedComplex)) h
        rw [realSLMobius_commutes_complexConjugation] at hc
        exact hmove (Mobius.complexConjugation.injective hc)
      obtain ⟨M,hM,huniq⟩:=existsUnique_isHIsometricReflectionLine_interior A p hp
      refine ⟨M,(isHIsometricReflectionLine_boundary_reflection_iff A z M).mp hM,?_⟩
      intro N hN
      exact huniq N ((isHIsometricReflectionLine_boundary_reflection_iff A z N).mpr hN)

/-- The full extended-plane w-isometric circle, specified by the source's actual reflection
factorization. Its nondegeneracy and uniqueness for every moved w are proved below. -/
def extendedHIsometricCircle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : Mobius.ExtendedComplex) : Set Mobius.ExtendedComplex :=
  {z | ∃M : HalfPlaneLine,IsHIsometricReflectionLine A w M ∧ z∈M.extendedCircle.val}

/-- The reflection-defined set really is the full generalized circle of the unique genuine h-line. -/
theorem extendedHIsometricCircle_eq_of_factor (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : Mobius.ExtendedComplex) (hw : (realSLMobius A).val w≠w) (M : HalfPlaneLine)
    (hM : IsHIsometricReflectionLine A w M) : extendedHIsometricCircle A w=M.extendedCircle.val := by
  obtain ⟨N,_hN,huniq⟩:=existsUnique_isHIsometricReflectionLine A w hw
  ext z
  constructor
  · rintro ⟨P,hP,hz⟩
    have he : P=M:=(huniq P hP).trans (huniq M hM).symm
    exact he ▸ hz
  · intro hz
    exact ⟨M,hM,hz⟩

/-- Every moved extended basepoint gives a genuine generalized circle, rather than a formal union. -/
theorem extendedHIsometricCircle_isGeneralized (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : Mobius.ExtendedComplex) (hw : (realSLMobius A).val w≠w) :
    Mobius.IsComplexGeneralizedCircle (extendedHIsometricCircle A w) := by
  obtain ⟨M,hM,_⟩:=existsUnique_isHIsometricReflectionLine A w hw
  rw [extendedHIsometricCircle_eq_of_factor A w hw M hM]
  exact M.extendedCircle.property

/-- Boundary reflection leaves the actual full w-isometric circle unchanged. -/
theorem extendedHIsometricCircle_boundary_reflection (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : Mobius.ExtendedComplex) :
    extendedHIsometricCircle A (Mobius.complexConjugation w)=extendedHIsometricCircle A w := by
  ext z
  simp only [extendedHIsometricCircle,isHIsometricReflectionLine_boundary_reflection_iff]

/-- The actual image of every source reflection-defined circle is contained in the reflection-defined
circle of the genuine conjugate; no coordinate normalizer is supplied as a hypothesis. -/
theorem extendedHIsometricCircle_image_subset (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : Mobius.ExtendedComplex) :
    (realSLMobius q).val '' extendedHIsometricCircle A w⊆
      extendedHIsometricCircle (q*A*q⁻¹) ((realSLMobius q).val w) := by
  rintro z ⟨u,⟨M,hM,hu⟩,rfl⟩
  refine ⟨M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q),hM.conjugation q,?_⟩
  have hg : 0<(Matrix.SpecialLinearGroup.mapGL ℝ q).val.det := by
    change 0<q.val.det
    rw [q.property]
    norm_num
  have he:=M.extendedCircle_image_realGL (M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q))
    (Matrix.SpecialLinearGroup.mapGL ℝ q) hg (M.realGLMap_carrier _).symm
  rw [←he]
  refine ⟨u,hu,?_⟩
  exact (realSLMobius_extended_action q u).symm

/-- Full extended-plane conjugacy covariance, including all ideal and exterior basepoints. -/
theorem extendedHIsometricCircle_conjugation (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : Mobius.ExtendedComplex) :
    extendedHIsometricCircle (q*A*q⁻¹) ((realSLMobius q).val w)=
      (realSLMobius q).val '' extendedHIsometricCircle A w := by
  apply Subset.antisymm
  · intro z hz
    have hzin : (realSLMobius q⁻¹).val z∈
        (realSLMobius q⁻¹).val '' extendedHIsometricCircle (q*A*q⁻¹) ((realSLMobius q).val w) :=
      mem_image_of_mem _ hz
    have hpre:=extendedHIsometricCircle_image_subset (q*A*q⁻¹) q⁻¹ ((realSLMobius q).val w) hzin
    have hA : q⁻¹*(q*A*q⁻¹)*(q⁻¹)⁻¹=A := by group
    have hw : (realSLMobius q⁻¹).val ((realSLMobius q).val w)=w := by
      rw [map_inv]
      exact (realSLMobius q).val.symm_apply_apply w
    rw [hA,hw] at hpre
    refine ⟨(realSLMobius q⁻¹).val z,hpre,?_⟩
    rw [map_inv]
    exact (realSLMobius q).val.apply_symm_apply z
  · exact extendedHIsometricCircle_image_subset A q w

/-- The genuine disc-preserving Mobius map of the same original real matrix. -/
def discCayleyMobius (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Mobius.complexMobiusGroup :=
  cayleyMobius*realSLMobius A*cayleyMobius⁻¹

/-- The full actual w-isometric circle in the disc model, transported as a real generalized
circle by the actual Cayley map. No exterior or ideal basepoint is discarded. -/
def extendedDiscWIsometricCircle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : Mobius.ExtendedComplex) : Set Mobius.ExtendedComplex :=
  cayleyMobius.val '' extendedHIsometricCircle A ((cayleyMobius⁻¹).val w)

/-- All disc-model moved basepoints produce genuine full generalized circles. -/
theorem extendedDiscWIsometricCircle_isGeneralized
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : Mobius.ExtendedComplex)
    (hw : (discCayleyMobius A).val w≠w) :
    Mobius.IsComplexGeneralizedCircle (extendedDiscWIsometricCircle A w) := by
  have hm : (realSLMobius A).val ((cayleyMobius⁻¹).val w)≠(cayleyMobius⁻¹).val w := by
    intro h
    apply hw
    change cayleyMobius.val ((realSLMobius A).val ((cayleyMobius⁻¹).val w))=w
    rw [h]
    exact cayleyMobius.val.apply_symm_apply w
  exact (Mobius.ComplexGeneralizedCircle.image cayleyMobius
    ⟨extendedHIsometricCircle A ((cayleyMobius⁻¹).val w),extendedHIsometricCircle_isGeneralized A _ hm⟩).property

/-- The source conjugacy formula in the original disc model, on the entire extended plane. -/
theorem extendedDiscWIsometricCircle_conjugation
    (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : Mobius.ExtendedComplex) :
    extendedDiscWIsometricCircle (q*A*q⁻¹) ((discCayleyMobius q).val w)=
      (discCayleyMobius q).val '' extendedDiscWIsometricCircle A w := by
  have hp : (cayleyMobius⁻¹).val ((discCayleyMobius q).val w)=
      (realSLMobius q).val ((cayleyMobius⁻¹).val w) := by
    change cayleyMobius⁻¹•(cayleyMobius•(realSLMobius q•(cayleyMobius⁻¹•w)))=_
    rw [inv_smul_smul]
    rfl
  unfold extendedDiscWIsometricCircle
  rw [hp,extendedHIsometricCircle_conjugation,image_image,image_image]
  congr 1
  funext z
  change cayleyMobius•(realSLMobius q•z)=
    cayleyMobius•(realSLMobius q•(cayleyMobius⁻¹•(cayleyMobius•z)))
  rw [inv_smul_smul]

/-- Cayley transports actual real-axis reflection to actual inversion in the unit circle,
including both zero and infinity. -/
theorem cayley_complexConjugation_unitReflection (w : Mobius.ExtendedComplex) :
    cayleyMobius.val (Mobius.complexConjugation w)=Mobius.reciprocal (Mobius.complexConjugation (cayleyMobius.val w)) :=
      by
  let R:=Mobius.coefficientMatrix 0 1 1 0 (by norm_num)
  have hm : R*(extendedCayleyMatrix.map (starRingEnd ℂ))=extendedCayleyMatrix := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [R,extendedCayleyMatrix,Mobius.coefficientMatrix,Matrix.mul_apply,Fin.sum_univ_two,
        Matrix.GeneralLinearGroup.map]
  have hF : Mobius.reciprocal*Mobius.fractionalLinear (extendedCayleyMatrix.map (starRingEnd ℂ))=
      Mobius.fractionalLinear extendedCayleyMatrix := by
    change Mobius.fractionalLinearHom R*Mobius.fractionalLinearHom _=Mobius.fractionalLinearHom _
    rw [←map_mul,hm]
  have he : cayleyMobius.val*Mobius.complexConjugation=Mobius.reciprocal*Mobius.complexConjugation*cayleyMobius.val :=
    by
    change Mobius.fractionalLinear extendedCayleyMatrix*Mobius.complexConjugation=
      Mobius.reciprocal*Mobius.complexConjugation*Mobius.fractionalLinear extendedCayleyMatrix
    rw [mul_assoc,Mobius.complexConjugation_fractionalLinear,←mul_assoc,hF]
  exact congrArg (fun f : Equiv.Perm Mobius.ExtendedComplex=>f w) he

/-- The source unit-circle reflection identity for every extended-plane basepoint. -/
theorem extendedDiscWIsometricCircle_unitReflection
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : Mobius.ExtendedComplex) :
    extendedDiscWIsometricCircle A (Mobius.reciprocal (Mobius.complexConjugation w))=
      extendedDiscWIsometricCircle A w := by
  have hp : (cayleyMobius⁻¹).val (Mobius.reciprocal (Mobius.complexConjugation w))=
      Mobius.complexConjugation ((cayleyMobius⁻¹).val w) := by
    apply cayleyMobius.val.injective
    have he:=cayley_complexConjugation_unitReflection ((cayleyMobius⁻¹).val w)
    have hc (x : Mobius.ExtendedComplex) : cayleyMobius.val ((cayleyMobius⁻¹).val x)=x :=
      cayleyMobius.val.apply_symm_apply x
    simpa only [hc] using he.symm
  unfold extendedDiscWIsometricCircle
  rw [hp,extendedHIsometricCircle_boundary_reflection]

/-- The ordinary circle at zero equals the full circle at infinity, with the actual pole
values of unit-circle reflection accounted for. -/
theorem extendedDiscWIsometricCircle_zero_eq_infty (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    extendedDiscWIsometricCircle A ((0:ℂ):Mobius.ExtendedComplex)=extendedDiscWIsometricCircle A ∞ := by
  simpa only [Mobius.complexConjugation_infty,Mobius.reciprocal_infty] using
    extendedDiscWIsometricCircle_unitReflection A ∞

/-- The source factor condition depends on the actual transformation, not on its chosen real lift. -/
theorem isHIsometricReflectionLine_eq_of_realSLMobius_eq
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h : realSLMobius A=realSLMobius B)
    (w : Mobius.ExtendedComplex) (M : HalfPlaneLine) :
    IsHIsometricReflectionLine A w M ↔ IsHIsometricReflectionLine B w M := by
  have hact : (A • · : ℍ→ℍ)=(B • · : ℍ→ℍ) := by
    funext z
    apply UpperHalfPlane.coe_injective
    apply OnePoint.coe_injective
    rw [←realSLMobius_action,←realSLMobius_action,h]
  simp only [IsHIsometricReflectionLine,hact]

/-- The whole extended-plane circle is independent of the actual real matrix representative. -/
theorem extendedHIsometricCircle_eq_of_realSLMobius_eq
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h : realSLMobius A=realSLMobius B)
    (w : Mobius.ExtendedComplex) : extendedHIsometricCircle A w=extendedHIsometricCircle B w := by
  ext z
  simp only [extendedHIsometricCircle,isHIsometricReflectionLine_eq_of_realSLMobius_eq A B h]

/-- Equality of the original disc transformations is exactly equality of their real-plane transforms. -/
theorem discCayleyMobius_eq_iff (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    discCayleyMobius A=discCayleyMobius B ↔ realSLMobius A=realSLMobius B := by
  constructor
  · intro h
    have he:=congrArg (fun f:Mobius.complexMobiusGroup=>cayleyMobius⁻¹*f*cayleyMobius) h
    simpa [discCayleyMobius,mul_assoc] using he
  · intro h
    simp only [discCayleyMobius,h]

/-- All actual unit-disc-preserving Mobius transformations have a real representative;
the final source theorem therefore does not assume or supply such a lift. -/
theorem discCayleyMobius_exists_of_preserves_disc (f : Mobius.complexMobiusGroup)
    (hf : f.val '' extendedUnitDisc=extendedUnitDisc) :
    ∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,discCayleyMobius A=f := by
  obtain ⟨A,hA⟩:=Fuchsian.mobius_preserves_halfPlane_exists_SL (cayleyMobius⁻¹*f*cayleyMobius)
    (Fuchsian.nielsen_discPreserver_conjugate_halfPlane f hf)
  refine ⟨A,?_⟩
  simp [discCayleyMobius,hA,mul_assoc]

/-- The genuine full disc-circle is independent of every choice of matrix lift. -/
theorem extendedDiscWIsometricCircle_eq_of_discCayleyMobius_eq
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h : discCayleyMobius A=discCayleyMobius B)
    (w : Mobius.ExtendedComplex) : extendedDiscWIsometricCircle A w=extendedDiscWIsometricCircle B w := by
  unfold extendedDiscWIsometricCircle
  rw [extendedHIsometricCircle_eq_of_realSLMobius_eq A B ((discCayleyMobius_eq_iff A B).mp h)]

/-- The original actual-transformation w-isometric circle. All matrix choices are removed
by the representation-independence theorem; genuine existence is proved without a lift hypothesis. -/
def actualDiscWIsometricCircle (f : Mobius.complexMobiusGroup) (w :
  Mobius.ExtendedComplex) : Set Mobius.ExtendedComplex :=
  {z | ∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,discCayleyMobius A=f ∧ z∈extendedDiscWIsometricCircle A w}

/-- Every actual representative computes precisely the same full source circle. -/
theorem actualDiscWIsometricCircle_eq_of_lift (f : Mobius.complexMobiusGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : discCayleyMobius A=f) (w : Mobius.ExtendedComplex) :
    actualDiscWIsometricCircle f w=extendedDiscWIsometricCircle A w := by
  ext z
  constructor
  · rintro ⟨B,hB,hz⟩
    exact extendedDiscWIsometricCircle_eq_of_discCayleyMobius_eq B A (hB.trans hA.symm) w ▸ hz
  · exact fun hz=>⟨A,hA,hz⟩

/-- The full circle for an arbitrary original disc preserver and arbitrary moved extended
basepoint is a genuine geometric generalized circle, without any chosen normalizer hypothesis. -/
theorem actualDiscWIsometricCircle_isGeneralized (f : Mobius.complexMobiusGroup)
    (hf : f.val '' extendedUnitDisc=extendedUnitDisc) (w : Mobius.ExtendedComplex) (hw : f.val w≠w) :
    Mobius.IsComplexGeneralizedCircle (actualDiscWIsometricCircle f w) := by
  obtain ⟨A,hA⟩:=discCayleyMobius_exists_of_preserves_disc f hf
  rw [actualDiscWIsometricCircle_eq_of_lift f A hA]
  exact extendedDiscWIsometricCircle_isGeneralized A w (by simpa only [hA] using hw)

/-- Unit-circle reflection invariance for the original actual transformation and all extended points. -/
theorem actualDiscWIsometricCircle_unitReflection (f : Mobius.complexMobiusGroup)
    (hf : f.val '' extendedUnitDisc=extendedUnitDisc) (w : Mobius.ExtendedComplex) :
    actualDiscWIsometricCircle f (Mobius.reciprocal (Mobius.complexConjugation w))=actualDiscWIsometricCircle f w := by
  obtain ⟨A,hA⟩:=discCayleyMobius_exists_of_preserves_disc f hf
  rw [actualDiscWIsometricCircle_eq_of_lift f A hA,actualDiscWIsometricCircle_eq_of_lift f A hA,
    extendedDiscWIsometricCircle_unitReflection]

/-- The original actual circle at zero is precisely the circle at infinity. -/
theorem actualDiscWIsometricCircle_zero_eq_infty (f : Mobius.complexMobiusGroup)
    (hf : f.val '' extendedUnitDisc=extendedUnitDisc) :
    actualDiscWIsometricCircle f ((0:ℂ):Mobius.ExtendedComplex)=actualDiscWIsometricCircle f ∞ := by
  simpa only [Mobius.complexConjugation_infty,
    Mobius.reciprocal_infty] using actualDiscWIsometricCircle_unitReflection f hf ∞

/-- Actual conjugation of the real action becomes actual conjugation of its disc transform. -/
theorem discCayleyMobius_conjugation (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    discCayleyMobius (q*A*q⁻¹)=discCayleyMobius q*discCayleyMobius A*(discCayleyMobius q)⁻¹ := by
  simp only [discCayleyMobius,map_mul,map_inv,mul_inv_rev,inv_inv]
  group

/-- Full source covariance for arbitrary original disc-preserving transformations. -/
theorem actualDiscWIsometricCircle_conjugation (f h : Mobius.complexMobiusGroup)
    (hf : f.val '' extendedUnitDisc=extendedUnitDisc)
    (hh : h.val '' extendedUnitDisc=extendedUnitDisc) (w : Mobius.ExtendedComplex) :
    actualDiscWIsometricCircle (h*f*h⁻¹) (h.val w)=h.val '' actualDiscWIsometricCircle f w := by
  obtain ⟨A,hA⟩:=discCayleyMobius_exists_of_preserves_disc f hf
  obtain ⟨q,hq⟩:=discCayleyMobius_exists_of_preserves_disc h hh
  have hc : discCayleyMobius (q*A*q⁻¹)=h*f*h⁻¹ := by
    rw [discCayleyMobius_conjugation,hA,hq]
  rw [actualDiscWIsometricCircle_eq_of_lift _ _ hc,actualDiscWIsometricCircle_eq_of_lift _ _ hA,←hq]
  exact extendedDiscWIsometricCircle_conjugation A q w

/-- The actual inverse Cayley image of an original disc point is its native half-plane point. -/
theorem cayleyMobius_inv_disc_point (z : Complex.UnitDisc) :
    (cayleyMobius⁻¹).val ((z:ℂ):Mobius.ExtendedComplex)=((discToHalfPlane z:ℂ):Mobius.ExtendedComplex) := by
  apply cayleyMobius.val.injective
  calc
    cayleyMobius.val ((cayleyMobius⁻¹).val ((z:ℂ):Mobius.ExtendedComplex))=((z:ℂ):Mobius.ExtendedComplex):=
      cayleyMobius.val.apply_symm_apply _
    _=cayleyMobius.val ((discToHalfPlane z:ℂ):Mobius.ExtendedComplex):=by
      rw [cayleyMobius_apply,extendedCayley_halfPlane,halfPlaneToDisc_discToHalfPlane]

/-- The full extended disc transformation has exactly its native actual-disc action. -/
theorem discCayleyMobius_action (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : Complex.UnitDisc) :
    (discCayleyMobius A).val ((z:ℂ):Mobius.ExtendedComplex)=((discSL2Action A z:ℂ):Mobius.ExtendedComplex) := by
  change cayleyMobius.val ((realSLMobius A).val ((cayleyMobius⁻¹).val ((z:ℂ):Mobius.ExtendedComplex)))=_
  rw [cayleyMobius_inv_disc_point,realSLMobius_action,cayleyMobius_apply,extendedCayley_halfPlane]
  rfl

/-- The actual original full circle is the source's genuine two-reflection construction on
native disc points, with the left geometric circle passing through the original extended basepoint. -/
theorem actualDiscWIsometricCircle_reflection_factor (f : Mobius.complexMobiusGroup)
    (hf : f.val '' extendedUnitDisc=extendedUnitDisc) (w : Mobius.ExtendedComplex) (hw : f.val w≠w) :
    ∃L M : DiscLine,w∈L.val.val ∧ actualDiscWIsometricCircle f w=M.val.val ∧
      ∀z : Complex.UnitDisc,f.val ((z:ℂ):Mobius.ExtendedComplex)=
        ((L.reflection (M.reflection z):ℂ):Mobius.ExtendedComplex) := by
  obtain ⟨A,hA⟩:=discCayleyMobius_exists_of_preserves_disc f hf
  have hm : (realSLMobius A).val ((cayleyMobius⁻¹).val w)≠(cayleyMobius⁻¹).val w := by
    intro h
    apply hw
    rw [←hA]
    change cayleyMobius.val ((realSLMobius A).val ((cayleyMobius⁻¹).val w))=w
    rw [h]
    exact cayleyMobius.val.apply_symm_apply w
  obtain ⟨M,hM,_⟩:=existsUnique_isHIsometricReflectionLine A ((cayleyMobius⁻¹).val w) hm
  obtain ⟨L,hwL,hfact⟩:=hM
  refine ⟨L.toDiscLine,M.toDiscLine,?_,?_,?_⟩
  · exact ⟨(cayleyMobius⁻¹).val w,hwL,cayleyMobius.val.apply_symm_apply w⟩
  · rw [actualDiscWIsometricCircle_eq_of_lift _ _ hA]
    unfold extendedDiscWIsometricCircle
    rw [extendedHIsometricCircle_eq_of_factor A _ hm M ⟨L,hwL,hfact⟩]
    rfl
  · intro z
    rw [←hA,discCayleyMobius_action]
    apply congrArg (fun z:Complex.UnitDisc=>((z:ℂ):Mobius.ExtendedComplex))
    unfold DiscLine.reflection
    rw [L.toDiscLine_toHalfPlane,M.toDiscLine_toHalfPlane,discToHalfPlane_halfPlaneToDisc]
    exact congrArg halfPlaneToDisc (congrFun hfact (discToHalfPlane z))

/-- Restricting the full reflection-defined circle to genuine interior points recovers the
actual hyperbolic perpendicular bisector of the point and its true inverse image. -/
theorem extendedHIsometricCircle_interior_iff
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℍ) (hw : A•w≠w) (z : ℍ) :
    ((z:ℂ):Mobius.ExtendedComplex)∈extendedHIsometricCircle A ((w:ℂ):Mobius.ExtendedComplex) ↔
      z∈hWIsometricCircle A w := by
  obtain ⟨M,⟨hM,L,hwL,hfact⟩,_⟩:=existsUnique_hWIsometricCircle A w hw
  have hm : (realSLMobius A).val ((w:ℂ):Mobius.ExtendedComplex)≠((w:ℂ):Mobius.ExtendedComplex) := by
    rw [realSLMobius_action]
    intro h
    exact hw (UpperHalfPlane.coe_injective (OnePoint.coe_injective h))
  rw [extendedHIsometricCircle_eq_of_factor A _ hm M ⟨L,(L.mem_extendedCircle w).mpr hwL,hfact⟩,
    M.mem_extendedCircle,hM]

/-- In the native disc the complete geometric circle restricts to the genuine inverse-image bisector. -/
theorem extendedDiscWIsometricCircle_interior_carrier
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : Complex.UnitDisc) (hw : discSL2Action A w≠w) :
    {z : Complex.UnitDisc | ((z:ℂ):Mobius.ExtendedComplex)∈extendedDiscWIsometricCircle A
      ((w:ℂ):Mobius.ExtendedComplex)}=
      DiscEquidistantLocus w (discSL2Action A⁻¹ w) := by
  have hm : A•discToHalfPlane w≠discToHalfPlane w := by
    intro h
    apply hw
    change halfPlaneToDisc (A•discToHalfPlane w)=w
    rw [h,halfPlaneToDisc_discToHalfPlane]
  ext z
  change ((z:ℂ):Mobius.ExtendedComplex)∈cayleyMobius.val '' extendedHIsometricCircle A
    ((cayleyMobius⁻¹).val ((w:ℂ):Mobius.ExtendedComplex)) ↔ _
  rw [Set.mem_image_equiv]
  change (cayleyMobius⁻¹).val ((z:ℂ):Mobius.ExtendedComplex)∈extendedHIsometricCircle A
    ((cayleyMobius⁻¹).val ((w:ℂ):Mobius.ExtendedComplex)) ↔ _
  rw [cayleyMobius_inv_disc_point,cayleyMobius_inv_disc_point,extendedHIsometricCircle_interior_iff A _ hm]
  change dist (discToHalfPlane z) (discToHalfPlane w)=
    dist (discToHalfPlane z) (A⁻¹•discToHalfPlane w) ↔
    discPathDist z w=discPathDist z (discSL2Action A⁻¹ w)
  rw [discPathDist_eq_halfPlane,discPathDist_eq_halfPlane]
  simp only [discSL2Action,discToHalfPlane_halfPlaneToDisc]

/-- The original actual full circle is exactly the complete whole-sphere geometric reflection
factor in the source, with both mirrors genuinely orthogonal to the disc boundary. -/
theorem actualDiscWIsometricCircle_complete_geometric_factor (f : Mobius.complexMobiusGroup)
    (hf : f.val '' extendedUnitDisc=extendedUnitDisc) (w : Mobius.ExtendedComplex) (hw : f.val w≠w) :
    ∃S T : Mobius.ComplexGeneralizedCircle,actualDiscWIsometricCircle f w=S.val ∧
      Mobius.IsGeometricNormalizedReflectionFactor discBoundaryCircle f w S T := by
  obtain ⟨A,hA⟩:=discCayleyMobius_exists_of_preserves_disc f hf
  have hm : (realSLMobius A).val ((cayleyMobius⁻¹).val w)≠(cayleyMobius⁻¹).val w := by
    intro h
    apply hw
    rw [←hA]
    change cayleyMobius.val ((realSLMobius A).val ((cayleyMobius⁻¹).val w))=w
    rw [h]
    exact cayleyMobius.val.apply_symm_apply w
  obtain ⟨M,hM,_⟩:=existsUnique_isHIsometricReflectionLine A ((cayleyMobius⁻¹).val w) hm
  obtain ⟨L,hwL,hfact⟩:=hM
  refine ⟨M.discCircle,L.discCircle,?_,?_⟩
  · rw [actualDiscWIsometricCircle_eq_of_lift _ _ hA]
    unfold extendedDiscWIsometricCircle
    rw [extendedHIsometricCircle_eq_of_factor A _ hm M ⟨L,hwL,hfact⟩]
    rfl
  · have hgeo : Mobius.IsGeometricNormalizedReflectionFactor halfPlaneBoundaryCircle (realSLMobius A)
        ((cayleyMobius⁻¹).val w) M.extendedCircle L.extendedCircle :=
      (Mobius.isHNormalizedReflectionFactor_iff_geometric A _ M L).mp ⟨hfact,hwL⟩
    have hconj:=hgeo.conjugation cayleyMobius
    have hp : cayleyMobius.val ((cayleyMobius⁻¹).val w)=w:=cayleyMobius.val.apply_symm_apply w
    change Mobius.IsGeometricNormalizedReflectionFactor discBoundaryCircle f w
      (M.extendedCircle.image cayleyMobius) (L.extendedCircle.image cayleyMobius)
    rw [←hA]
    simpa only [cayley_image_boundary,discCayleyMobius,hp] using hconj

/-- At the origin the geometric extended circle has exactly the classical Euclidean
isometric circle's native disc points, for the source's arbitrary normalized coefficients. -/
theorem extendedDiscWIsometricCircle_classical_origin (a c : ℂ)
    (h : ‖a‖^2-‖c‖^2=1) (h0 : discCoefficientAction a c h 0≠0) :
    {z : Complex.UnitDisc | ((z:ℂ):Mobius.ExtendedComplex)∈
      extendedDiscWIsometricCircle (discCoefficientsToSL a c h) ((0:ℂ):Mobius.ExtendedComplex)}=
    {z : Complex.UnitDisc | (z:ℂ)∈Mobius.isometricCircle a (conj c) c (conj a)} := by
  have hz : (((0:Complex.UnitDisc):ℂ):Mobius.ExtendedComplex)=((0:ℂ):Mobius.ExtendedComplex) := by simp
  rw [←hz]
  rw [extendedDiscWIsometricCircle_interior_carrier _ 0 h0,←discCoefficientsToSL_inverse]
  exact (disc_classical_isometricCircle_inverse_bisector_of_origin_ne a c h h0).symm

/-- The original actual-transformation circle at infinity is the same classical circle,
including the genuine zero/infinity boundary-reflection identity. -/
theorem actualDiscWIsometricCircle_classical_infty (a c : ℂ)
    (h : ‖a‖^2-‖c‖^2=1) (h0 : discCoefficientAction a c h 0≠0) :
    {z : Complex.UnitDisc | ((z:ℂ):Mobius.ExtendedComplex)∈
      actualDiscWIsometricCircle (discCayleyMobius (discCoefficientsToSL a c h)) ∞}=
    {z : Complex.UnitDisc | (z:ℂ)∈Mobius.isometricCircle a (conj c) c (conj a)} := by
  rw [actualDiscWIsometricCircle_eq_of_lift _ _ rfl,←extendedDiscWIsometricCircle_zero_eq_infty]
  exact extendedDiscWIsometricCircle_classical_origin a c h h0

end LowDimensionalTopology.Geometry.Hyperbolic
