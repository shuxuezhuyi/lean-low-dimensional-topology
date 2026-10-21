/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordExteriorGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.IsometricCircle.GeneralizedIsometricCircles
@[expose] public section
open Set
open scoped Topology OnePoint Pointwise UpperHalfPlane MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- The second mirror in the infinity-normalized decomposition is vertical. -/
def fordVerticalMirror (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (_hc : A 1 0≠0) : HalfPlaneLine:=
  .vertical ((A 0 0-A 1 1)/(2*A 1 0))

/-- An actual determinant-one map is the product of its normalized Ford mirrors. -/
theorem realSL_ford_reflection_factor (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) :
    (A • · : ℍ→ℍ)=(fordVerticalMirror A hc).reflection ∘ (Fuchsian.fordCircleMirror A hc).reflection := by
  funext z
  apply UpperHalfPlane.ext
  change ((A • z : ℍ) : ℂ)=(verticalReflection _ (circleReflection _ _ _ z) : ℂ)
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,verticalReflection_coe,circleReflection_coe]
  simp only [map_add,map_div₀,map_pow,map_sub,Complex.conj_ofReal,Complex.conj_conj,
    Algebra.algebraMap_self, RingHom.id_apply]
  have hcC : (A 1 0 : ℂ)≠0:=Complex.ofReal_ne_zero.mpr hc
  have hd : (A 1 0 : ℂ)*(z : ℂ)+(A 1 1 : ℂ)≠0:=by
    intro he
    have hi:=congrArg Complex.im he
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero,Complex.zero_im] at hi
    exact hc ((mul_eq_zero.mp hi).resolve_right z.im_ne_zero)
  have hz : (z : ℂ)-((-A 1 1/A 1 0 : ℝ) : ℂ)≠0:=by
    intro he
    have hi:=congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    exact z.im_ne_zero hi
  have hdet : (A 0 0 : ℂ)*(A 1 1 : ℂ)-(A 0 1 : ℂ)*(A 1 0 : ℂ)=1:=by
    exact_mod_cast (show A 0 0*A 1 1-A 0 1*A 1 0=1 by simpa only [Matrix.det_fin_two] using A.det_coe)
  have habs : ((|A 1 0| : ℝ) : ℂ)^2=(A 1 0 : ℂ)^2:=by exact_mod_cast sq_abs (A 1 0)
  push_cast
  field_simp [hcC,hd,sub_neg_eq_add,mul_comm,
    show ((|A 1 0| : ℝ) : ℂ)≠0 by exact_mod_cast (abs_pos.mpr hc).ne']
  rw [habs]
  field_simp [hd,mul_comm]
  simp only [sub_neg_eq_add]
  field_simp [show (z : ℂ)*(A 1 0 : ℂ)+(A 1 1 : ℂ)≠0 by simpa only [mul_comm] using hd]
  linear_combination -hdet

/-- The genuine reflection factorization with its second complete mirror through the center. -/
def IsHNormalizedReflectionFactor (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ξ : Mobius.ExtendedComplex) (L M : HalfPlaneLine) : Prop :=
  (A • · : ℍ→ℍ)=M.reflection ∘ L.reflection ∧ ξ∈M.extendedCircle.val

theorem HalfPlaneLine.infty_mem_extendedCircle_iff (L : HalfPlaneLine) :
    (∞ : Mobius.ExtendedComplex)∈L.extendedCircle.val ↔ ∃x : ℝ,L=.vertical x := by
  cases L <;> simp [HalfPlaneLine.extendedCircle]

/-- Infinity-normalization really uses the classical isometric circle and a vertical second mirror. -/
theorem realSL_ford_normalized_factor (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) :
    IsHNormalizedReflectionFactor A ∞ (Fuchsian.fordCircleMirror A hc) (fordVerticalMirror A hc) := by
  refine ⟨realSL_ford_reflection_factor A hc,?_⟩
  exact (HalfPlaneLine.infty_mem_extendedCircle_iff _).mpr ⟨_,rfl⟩

/-- The actual interior-center normalization exists and has the genuine inverse-image bisector as first mirror. -/
theorem exists_hNormalizedReflectionFactor_interior (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : ℍ) (hw : A • w≠w) :
    ∃L M : HalfPlaneLine,IsHNormalizedReflectionFactor A ((w : ℂ) : Mobius.ExtendedComplex) L M ∧
      L.carrier=HEquidistantLocus w (A⁻¹ • w) := by
  obtain ⟨L,⟨hcar,M,hwM,hfac⟩,_⟩:=existsUnique_hWIsometricCircle A w hw
  exact ⟨L,M,⟨hfac,(M.mem_extendedCircle w).mpr hwM⟩,hcar⟩

/-- Every normalized interior first mirror has exactly the original equidistance locus. -/
theorem IsHNormalizedReflectionFactor.interior_first_carrier
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {w : ℍ} (hw : A • w≠w)
    {L M : HalfPlaneLine} (h : IsHNormalizedReflectionFactor A ((w : ℂ) : Mobius.ExtendedComplex) L M) :
    L.carrier=HEquidistantLocus w (A⁻¹ • w) := by
  have hMw : M.reflection w=w:=(M.reflection_fixed_iff w).mpr ((M.mem_extendedCircle w).mp h.2)
  have hswap : L.reflection w=A⁻¹ • w:=by
    have hback:=congrFun h.1 (A⁻¹ • w)
    rw [smul_inv_smul,Function.comp_apply] at hback
    have hh:=congrArg M.reflection hback
    rw [hMw,M.reflection_involutive] at hh
    simpa only [L.reflection_involutive (A⁻¹ • w)] using congrArg L.reflection hh
  have hwv : w≠A⁻¹ • w:=by
    intro he
    have hh:=congrArg (fun z : ℍ=>A • z) he
    rw [smul_inv_smul] at hh
    exact hw hh
  exact L.carrier_eq_equidistant_of_reflection_swap w (A⁻¹ • w) hwv hswap

/-- Both genuine mirrors in the interior-center normalization are unique. -/
theorem hNormalizedReflectionFactor_interior_unique
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {w : ℍ} (hw : A • w≠w)
    {L M N K : HalfPlaneLine}
    (h : IsHNormalizedReflectionFactor A ((w : ℂ) : Mobius.ExtendedComplex) L M)
    (h' : IsHNormalizedReflectionFactor A ((w : ℂ) : Mobius.ExtendedComplex) N K) : L=N ∧ M=K := by
  have hLN : L=N:=HalfPlaneLine.carrier_injective
    ((h.interior_first_carrier hw).trans (h'.interior_first_carrier hw).symm)
  refine ⟨hLN,?_⟩
  subst N
  exact realSL_reflection_factor_unique A L M K h.1 h'.1

/-- A vertical normalized second factor has the uniquely prescribed real coordinate. -/
theorem realSL_vertical_factor_coordinate (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) (L : HalfPlaneLine) (x : ℝ)
    (hfac : (A • · : ℍ→ℍ)=(HalfPlaneLine.vertical x).reflection ∘ L.reflection) :
    x=(A 0 0-A 1 1)/(2*A 1 0) := by
  let C:=verticalReflectionMatrix x*Matrix.SpecialLinearGroup.mapGL ℝ A
  have hd : C.val.det<0:=by
    change Matrix.det ((verticalReflectionMatrix x).val*A.val)<0
    rw [Matrix.det_mul,verticalReflectionMatrix_det,A.det_coe]
    norm_num
  obtain ⟨z,_w,hz,_hw,_hzw⟩:=L.exists_two_points
  have hfix : C • z=z:=by
    dsimp only [C]
    rw [mul_smul]
    change verticalReflectionMatrix x • (A • z)=z
    rw [congrFun hfac z,Function.comp_apply]
    change (HalfPlaneLine.vertical x).reflection ((HalfPlaneLine.vertical x).reflection (L.reflection z))=z
    rw [(HalfPlaneLine.vertical x).reflection_involutive,(L.reflection_fixed_iff z).mpr hz]
  have ht : Matrix.trace C.val=0:=
    (UpperHalfPlane.exists_gl_smul_eq_self_iff_trace_eq_zero hd).mp ⟨z,hfix⟩
  change Matrix.trace ((verticalReflectionMatrix x).val*A.val)=0 at ht
  simp only [verticalReflectionMatrix,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two] at ht
  change -1*A 0 0+2*x*A 1 0+(0*A 0 1+1*A 1 1)=0 at ht
  apply (eq_div_iff (mul_ne_zero (by norm_num) hc)).mpr
  nlinarith

/-- The infinity-normalized genuine pair is unique, not just an arbitrary two-reflection factorization. -/
theorem hNormalizedReflectionFactor_infty_unique
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hc : A 1 0≠0)
    {L M : HalfPlaneLine} (h : IsHNormalizedReflectionFactor A ∞ L M) :
    L=Fuchsian.fordCircleMirror A hc ∧ M=fordVerticalMirror A hc := by
  obtain ⟨x,rfl⟩:=(HalfPlaneLine.infty_mem_extendedCircle_iff M).mp h.2
  have hx:=realSL_vertical_factor_coordinate A hc L x h.1
  have hM : HalfPlaneLine.vertical x=fordVerticalMirror A hc:=congrArg HalfPlaneLine.vertical hx
  refine ⟨?_,hM⟩
  apply HalfPlaneLine.reflection_injective
  funext z
  apply (HalfPlaneLine.vertical x).reflection_isometry.injective
  have hf:=realSL_ford_reflection_factor A hc
  rw [←hM] at hf
  exact (congrFun h.1 z).symm.trans (congrFun hf z)

/-- Actual existence and uniqueness of both infinity-normalized geodesic mirrors. -/
theorem existsUnique_hNormalizedReflectionFactor_infty
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hc : A 1 0≠0) :
    ∃!LM : HalfPlaneLine×HalfPlaneLine,IsHNormalizedReflectionFactor A ∞ LM.1 LM.2 := by
  refine ⟨⟨Fuchsian.fordCircleMirror A hc,fordVerticalMirror A hc⟩,realSL_ford_normalized_factor A hc,?_⟩
  intro LM hLM
  exact Prod.ext (hNormalizedReflectionFactor_infty_unique A hc hLM).1
    (hNormalizedReflectionFactor_infty_unique A hc hLM).2

/-- Actual existence and uniqueness of both mirrors at every moved interior center. -/
theorem existsUnique_hNormalizedReflectionFactor_interior
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℍ) (hw : A • w≠w) :
    ∃!LM : HalfPlaneLine×HalfPlaneLine,
      IsHNormalizedReflectionFactor A ((w : ℂ) : Mobius.ExtendedComplex) LM.1 LM.2 := by
  obtain ⟨L,M,h,_hcar⟩:=exists_hNormalizedReflectionFactor_interior A w hw
  refine ⟨⟨L,M⟩,h,?_⟩
  intro NK hNK
  exact Prod.ext (hNormalizedReflectionFactor_interior_unique hw hNK h).1
    (hNormalizedReflectionFactor_interior_unique hw hNK h).2

theorem geodesicRealGLMobius_mapSL (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    geodesicRealGLMobius (Matrix.SpecialLinearGroup.mapGL ℝ q)=realSLMobius q := by
  apply Subtype.ext
  simp only [geodesicRealGLMobius,realSLMobius,MonoidHom.comp_apply,
    Mobius.invariantDisc_specialLinear_action,realSLMobius_matrix]

/-- Both complete mirrors and the nonfixed center transport by the actual original real Mobius map. -/
theorem IsHNormalizedReflectionFactor.conjugation
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ξ : Mobius.ExtendedComplex} {L M : HalfPlaneLine}
    (h : IsHNormalizedReflectionFactor A ξ L M) (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsHNormalizedReflectionFactor (q*A*q⁻¹) ((realSLMobius q).val ξ)
      (L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q))
      (M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)) := by
  refine ⟨realSL_two_reflections_conjugate A q L M h.1,?_⟩
  have hg : 0<(Matrix.SpecialLinearGroup.mapGL ℝ q).val.det:=by
    change 0<q.val.det
    rw [q.det_coe]
    norm_num
  have he:=M.extendedCircle_image_realGL _ (Matrix.SpecialLinearGroup.mapGL ℝ q) hg
    (M.realGLMap_carrier _).symm
  rw [geodesicRealGLMobius_mapSL] at he
  rw [←he]
  exact ⟨ξ,h.2,rfl⟩

/-- Every nonfixed actual ideal center has a genuine normalized two-reflection factorization. -/
theorem exists_hNormalizedReflectionFactor_boundary
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ξ : Mobius.ExtendedComplex)
    (hξ : ξ∈halfPlaneIdealBoundary) (hmoved : (realSLMobius A).val ξ≠ξ) :
    ∃L M : HalfPlaneLine,IsHNormalizedReflectionFactor A ξ L M := by
  obtain ⟨q,hq⟩:=realSLMobius_exists_send_to_infty ξ hξ
  let B:=q*A*q⁻¹
  have hc : B 1 0≠0:=by
    intro hc
    have hb : (realSLMobius B).val ∞=∞:=(realSLMobius_fixed_infty_iff B).mpr hc
    rw [←hq] at hb
    exact hmoved ((realSLMobius_conjugate_fixed_iff A q ξ).mp hb)
  have h:=(realSL_ford_normalized_factor B hc).conjugation q⁻¹
  have hA : q⁻¹*B*(q⁻¹)⁻¹=A:=by dsimp only [B];group
  have hpoint : (realSLMobius q⁻¹).val ∞=ξ:=by
    rw [map_inv,←hq]
    exact (realSLMobius q).val.symm_apply_apply ξ
  rw [hA,hpoint] at h
  exact ⟨_,_,h⟩

/-- Both genuine mirrors at every actual ideal center are unique. -/
theorem hNormalizedReflectionFactor_boundary_unique
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ξ : Mobius.ExtendedComplex)
    (hξ : ξ∈halfPlaneIdealBoundary) (hmoved : (realSLMobius A).val ξ≠ξ)
    {L M N K : HalfPlaneLine}
    (h : IsHNormalizedReflectionFactor A ξ L M) (h' : IsHNormalizedReflectionFactor A ξ N K) :
    L=N ∧ M=K := by
  obtain ⟨q,hq⟩:=realSLMobius_exists_send_to_infty ξ hξ
  let B:=q*A*q⁻¹
  have hc : B 1 0≠0:=by
    intro hc
    have hb : (realSLMobius B).val ∞=∞:=(realSLMobius_fixed_infty_iff B).mpr hc
    rw [←hq] at hb
    exact hmoved ((realSLMobius_conjugate_fixed_iff A q ξ).mp hb)
  have h1:=h.conjugation q
  have h2:=h'.conjugation q
  rw [hq] at h1 h2
  have hh1:=hNormalizedReflectionFactor_infty_unique B hc h1
  have hh2:=hNormalizedReflectionFactor_infty_unique B hc h2
  exact ⟨HalfPlaneLine.realGLMap_injective _ (hh1.1.trans hh2.1.symm),
    HalfPlaneLine.realGLMap_injective _ (hh1.2.trans hh2.2.symm)⟩

/-- Every complete hyperbolic mirror is invariant under reflection in the real boundary. -/
theorem HalfPlaneLine.mem_extendedCircle_conjugation (L : HalfPlaneLine) (ξ : Mobius.ExtendedComplex) :
    Mobius.complexConjugation ξ∈L.extendedCircle.val ↔ ξ∈L.extendedCircle.val := by
  induction ξ using OnePoint.rec with
  | infty => rfl
  | coe z =>
    cases L with
    | vertical x => simp [HalfPlaneLine.extendedCircle,Complex.inner]
    | circle c r hr =>
      simp only [Mobius.complexConjugation_coe,HalfPlaneLine.extendedCircle,Mobius.complexCircle_coe]
      have he : ‖conj z-(c : ℂ)‖=‖z-(c : ℂ)‖:=by
        calc
          ‖conj z-(c : ℂ)‖=‖conj (z-(c : ℂ))‖:=by rw [map_sub,Complex.conj_ofReal]
          _=‖z-(c : ℂ)‖:=Complex.norm_conj _
      rw [he]

/-- Boundary reflection does not alter either actual normalized mirror. -/
theorem isHNormalizedReflectionFactor_conjugation_iff
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ξ : Mobius.ExtendedComplex) (L M : HalfPlaneLine) :
    IsHNormalizedReflectionFactor A (Mobius.complexConjugation ξ) L M ↔
      IsHNormalizedReflectionFactor A ξ L M := by
  unfold IsHNormalizedReflectionFactor
  rw [HalfPlaneLine.mem_extendedCircle_conjugation M ξ]

/-- The original real Mobius action commutes with reflection in the circle at infinity. -/
theorem realSLMobius_complexConjugation (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ξ : Mobius.ExtendedComplex) :
    (realSLMobius A).val (Mobius.complexConjugation ξ)=Mobius.complexConjugation ((realSLMobius A).val ξ) := by
  let g:=complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ A)
  have hg : g.map (starRingEnd ℂ)=g:=by
    apply Units.ext
    apply Matrix.ext
    intro i j
    change conj (A i j : ℂ)=(A i j : ℂ)
    exact Complex.conj_ofReal _
  have h:=Mobius.complexConjugation_fractionalLinear g
  rw [hg] at h
  have hA : (realSLMobius A).val=Mobius.fractionalLinear g:=by
    simp only [g,realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,realSLMobius_matrix]
  rw [hA]
  exact (congrFun (congrArg DFunLike.coe h) ξ).symm

/-- The conjugate center is moved exactly when the original center is moved. -/
theorem realSLMobius_conjugate_center_moved
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ξ : Mobius.ExtendedComplex)
    (hmoved : (realSLMobius A).val ξ≠ξ) :
    (realSLMobius A).val (Mobius.complexConjugation ξ)≠Mobius.complexConjugation ξ := by
  intro he
  apply hmoved
  apply Mobius.complexConjugation.injective
  rw [←realSLMobius_complexConjugation,he]

/-- Both actual mirrors exist at every nonfixed point of the entire extended plane. -/
theorem exists_hNormalizedReflectionFactor (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ξ : Mobius.ExtendedComplex) (hmoved : (realSLMobius A).val ξ≠ξ) :
    ∃L M : HalfPlaneLine,IsHNormalizedReflectionFactor A ξ L M := by
  by_cases hboundary : ξ∈halfPlaneIdealBoundary
  · exact exists_hNormalizedReflectionFactor_boundary A ξ hboundary hmoved
  have hinf : ξ≠∞:=by intro he;apply hboundary;rw [he];simp [halfPlaneIdealBoundary]
  obtain ⟨z,rfl⟩:=OnePoint.ne_infty_iff_exists.mp hinf
  by_cases hz : 0<z.im
  · let w : ℍ:=⟨z,hz⟩
    have hw : A • w≠w:=by
      intro he
      apply hmoved
      change (realSLMobius A).val ((w : ℂ) : Mobius.ExtendedComplex)=((w : ℂ) : Mobius.ExtendedComplex)
      rw [realSLMobius_action,he]
    obtain ⟨L,M,h,_⟩:=exists_hNormalizedReflectionFactor_interior A w hw
    exact ⟨L,M,h⟩
  · have him : z.im≠0:=fun he=>hboundary ((coe_mem_halfPlaneIdealBoundary z).mpr he)
    let w : ℍ:=⟨conj z,by
      simp only [Complex.conj_im]
      apply neg_pos.mpr
      exact lt_of_le_of_ne (le_of_not_gt hz) him⟩
    have hw : A • w≠w:=by
      intro he
      apply realSLMobius_conjugate_center_moved A (z : Mobius.ExtendedComplex) hmoved
      change (realSLMobius A).val ((w : ℂ) : Mobius.ExtendedComplex)=((w : ℂ) : Mobius.ExtendedComplex)
      rw [realSLMobius_action,he]
    obtain ⟨L,M,h,_⟩:=exists_hNormalizedReflectionFactor_interior A w hw
    exact ⟨L,M,(isHNormalizedReflectionFactor_conjugation_iff A (z : Mobius.ExtendedComplex) L M).mp h⟩

/-- Both actual mirrors are unique at every nonfixed point of the entire extended plane. -/
theorem hNormalizedReflectionFactor_unique (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ξ : Mobius.ExtendedComplex) (hmoved : (realSLMobius A).val ξ≠ξ)
    {L M N K : HalfPlaneLine}
    (h : IsHNormalizedReflectionFactor A ξ L M) (h' : IsHNormalizedReflectionFactor A ξ N K) :
    L=N ∧ M=K := by
  by_cases hboundary : ξ∈halfPlaneIdealBoundary
  · exact hNormalizedReflectionFactor_boundary_unique A ξ hboundary hmoved h h'
  have hinf : ξ≠∞:=by intro he;apply hboundary;rw [he];simp [halfPlaneIdealBoundary]
  obtain ⟨z,rfl⟩:=OnePoint.ne_infty_iff_exists.mp hinf
  by_cases hz : 0<z.im
  · let w : ℍ:=⟨z,hz⟩
    have hw : A • w≠w:=by
      intro he
      apply hmoved
      change (realSLMobius A).val ((w : ℂ) : Mobius.ExtendedComplex)=((w : ℂ) : Mobius.ExtendedComplex)
      rw [realSLMobius_action,he]
    exact hNormalizedReflectionFactor_interior_unique hw h h'
  · have him : z.im≠0:=fun he=>hboundary ((coe_mem_halfPlaneIdealBoundary z).mpr he)
    let w : ℍ:=⟨conj z,by
      simp only [Complex.conj_im]
      apply neg_pos.mpr
      exact lt_of_le_of_ne (le_of_not_gt hz) him⟩
    have hw : A • w≠w:=by
      intro he
      apply realSLMobius_conjugate_center_moved A (z : Mobius.ExtendedComplex) hmoved
      change (realSLMobius A).val ((w : ℂ) : Mobius.ExtendedComplex)=((w : ℂ) : Mobius.ExtendedComplex)
      rw [realSLMobius_action,he]
    exact hNormalizedReflectionFactor_interior_unique hw
      ((isHNormalizedReflectionFactor_conjugation_iff A (z : Mobius.ExtendedComplex) L M).mpr h)
      ((isHNormalizedReflectionFactor_conjugation_iff A (z : Mobius.ExtendedComplex) N K).mpr h')

/-- Full normalized-reflection existence and uniqueness, with no restriction to finite or ideal centers. -/
theorem existsUnique_hNormalizedReflectionFactor (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ξ : Mobius.ExtendedComplex) (hmoved : (realSLMobius A).val ξ≠ξ) :
    ∃!LM : HalfPlaneLine×HalfPlaneLine,IsHNormalizedReflectionFactor A ξ LM.1 LM.2 := by
  obtain ⟨L,M,h⟩:=exists_hNormalizedReflectionFactor A ξ hmoved
  exact ⟨⟨L,M⟩,h,fun NK hNK=>Prod.ext (hNormalizedReflectionFactor_unique A ξ hmoved hNK h).1
    (hNormalizedReflectionFactor_unique A ξ hmoved hNK h).2⟩

/-- Equality of genuine native reflection actions also gives equality on the entire extended sphere. -/
theorem realSL_reflection_factor_global (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (L M : HalfPlaneLine) (hfac : (A • · : ℍ→ℍ)=M.reflection ∘ L.reflection) :
    (realSLMobius A).val=Mobius.euclideanToComplexHom M.realReflection*Mobius.euclideanToComplexHom L.realReflection :=
      by
  have hword : ∀R∈[M.realReflection,L.realReflection],Inversive.IsReflection R:=by
    intro R hR
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
    rcases hR with rfl|rfl
    · exact M.realReflection_isReflection
    · exact L.realReflection_isReflection
  have hm : Mobius.euclideanToComplexHom (M.realReflection*L.realReflection)∈Mobius.complexMobiusGroup:=by
    rw [Mobius.complexMobiusGroup_eq_fractionalLinearGroup]
    have he:=(Mobius.reflectionWord_complex_fractional_iff_even [M.realReflection,L.realReflection] hword).mpr
      (by change Even (2 : ℕ);decide)
    simpa only [List.prod_cons,List.prod_nil,mul_one] using he
  let F : Mobius.complexMobiusGroup:=⟨Mobius.euclideanToComplexHom (M.realReflection*L.realReflection),hm⟩
  have he : realSLMobius A=F:=by
    apply Fuchsian.mobius_ext_on_halfPlane
    intro z
    change (realSLMobius A).val ((z : ℂ) : Mobius.ExtendedComplex)=
      Mobius.euclideanToComplexHom (M.realReflection*L.realReflection) ((z : ℂ) : Mobius.ExtendedComplex)
    rw [realSLMobius_action,map_mul]
    change (((A • z : ℍ) : ℂ) : Mobius.ExtendedComplex)=
      Mobius.euclideanToComplexHom M.realReflection (Mobius.euclideanToComplexHom L.realReflection ((z : ℂ) :
        Mobius.ExtendedComplex))
    rw [L.realReflection_coe,M.realReflection_coe,congrFun hfac z]
    rfl
  exact (congrArg Subtype.val he).trans (map_mul Mobius.euclideanToComplexHom M.realReflection L.realReflection)

/-- The first complete mirror avoids every nonfixed normalization center, so its containing half-plane is defined. -/
theorem IsHNormalizedReflectionFactor.first_mirror_avoids_center
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ξ : Mobius.ExtendedComplex} {L M : HalfPlaneLine}
    (h : IsHNormalizedReflectionFactor A ξ L M) (hmoved : (realSLMobius A).val ξ≠ξ) :
    ξ∉L.extendedCircle.val := by
  intro hξL
  have hL : Mobius.euclideanToComplexHom L.realReflection ξ=ξ:=by
    rw [←L.realReflection_fixedPoints] at hξL
    exact hξL
  have hM : Mobius.euclideanToComplexHom M.realReflection ξ=ξ:=by
    have hξM:=h.2
    rw [←M.realReflection_fixedPoints] at hξM
    exact hξM
  apply hmoved
  rw [realSL_reflection_factor_global A L M h.1]
  change Mobius.euclideanToComplexHom M.realReflection (Mobius.euclideanToComplexHom L.realReflection ξ)=ξ
  rw [hL,hM]

end
end LowDimensionalTopology.Geometry.Hyperbolic
