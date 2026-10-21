/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.EllipticReflectionPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Transversals
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Reflection in the genuine image line is actual conjugacy of native reflection actions. -/
theorem HalfPlaneLine.reflection_realGL_conjugation (L : HalfPlaneLine) (g : GL (Fin 2) ℝ) (z : ℍ) :
    g • L.reflection (g⁻¹ • z) = (L.realGLMap g).reflection z := by
  obtain ⟨M,hM,hact⟩ := L.reflection_conjugation_exists g
  have he : M = L.realGLMap g :=
    HalfPlaneLine.carrier_injective (hM.trans (L.realGLMap_carrier g).symm)
  simpa only [he] using hact z

/-- A two-reflection normal form transports to the original actual action and image lines. -/
theorem realSL_two_reflections_transport (f q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (L M : HalfPlaneLine)
    (he : ∀ z : ℍ, (q*f*q⁻¹) • z = M.reflection (L.reflection z)) :
    (f • · : ℍ → ℍ) =
      (M.realGLMap ((Matrix.SpecialLinearGroup.mapGL ℝ q)⁻¹)).reflection ∘
      (L.realGLMap ((Matrix.SpecialLinearGroup.mapGL ℝ q)⁻¹)).reflection := by
  funext z
  let g := Matrix.SpecialLinearGroup.mapGL ℝ q
  have hL := L.reflection_realGL_conjugation g⁻¹ z
  rw [inv_inv] at hL
  have hM := M.reflection_realGL_conjugation g⁻¹
    ((L.realGLMap g⁻¹).reflection z)
  rw [inv_inv,← hL,smul_inv_smul] at hM
  rw [hL] at hM
  have hnorm := congrArg (fun w : ℍ => q⁻¹ • w) (he (q • z))
  simp only [mul_smul,inv_smul_smul] at hnorm
  change f • z = g⁻¹ • M.reflection (L.reflection (g • z)) at hnorm
  exact hnorm.trans hM

/-- A geodesic has infinity as an actual ideal endpoint exactly when it is vertical. -/
theorem HalfPlaneLine.infty_idealEndpoint_iff (L : HalfPlaneLine) :
    (∞ : Mobius.ExtendedComplex) ∈ L.idealEndpoints ↔ ∃ x : ℝ, L = .vertical x := by
  cases L with
  | vertical x => simp [vertical_idealEndpoints]
  | circle c r hr => simp [circle_idealEndpoints]

/-- The translation factors through any prescribed vertical line. -/
theorem translation_reflection_factor (t x : ℝ) :
    (hTranslationSL t • · : ℍ → ℍ) =
      (HalfPlaneLine.vertical (x+t/2)).reflection ∘ (HalfPlaneLine.vertical x).reflection := by
  funext z
  apply UpperHalfPlane.ext
  change ((hTranslationSL t • z : ℍ) : ℂ) =
    (verticalReflection (x+t/2) (verticalReflection x z) : ℂ)
  rw [hTranslationSL_coe,verticalReflection_coe,verticalReflection_coe]
  simp only [map_sub,Complex.conj_ofReal,Complex.conj_conj]
  push_cast
  ring

/-- Opposite determinant-one real lifts give the same genuine native action. -/
theorem realSL_neg_smul (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) : (-f) • z = f • z := by
  have he := congrArg (fun F : Mobius.complexMobiusGroup => F.val ((z : ℂ) : Mobius.ExtendedComplex))
    (realSLMobius_neg f)
  rw [realSLMobius_action,realSLMobius_action] at he
  exact UpperHalfPlane.ext (OnePoint.coe_eq_coe.mp he)

/-- The genuine unique ideal fixed point of a nontrivial parabolic action. -/
def hParabolicIdealPoint (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusParabolic (realSLMobius f)) : Mobius.ExtendedComplex := hf.2.choose

theorem hParabolicIdealPoint_fixed (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusParabolic (realSLMobius f)) :
    (realSLMobius f).val (hParabolicIdealPoint f hf) = hParabolicIdealPoint f hf :=
  (hf.2.choose_spec _).mpr rfl

/-- Every line in the actual associated parabolic pencil becomes a vertical line
under the genuine real translation normalizer. -/
theorem realSL_parabolic_pencil_normalizer (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusParabolic (realSLMobius f)) (L : HalfPlaneLine)
    (hL : hParabolicIdealPoint f hf ∈ L.idealEndpoints) :
    ∃ (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t x : ℝ), t ≠ 0 ∧
      (∀ z : ℍ, (q*f*q⁻¹) • z = hTranslationSL t • z) ∧
      L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q) = .vertical x ∧
      (realSLMobius q).val (hParabolicIdealPoint f hf) = ∞ := by
  obtain ⟨q,t,ht,he⟩ := realSLMobius_parabolic_normal_form f hf
  have hact : ∀ z : ℍ, (q*f*q⁻¹) • z = hTranslationSL t • z := by
    intro z
    rcases he with he | he
    · rw [he]
    · rw [he,realSL_neg_smul]
  have hi : (realSLMobius (q*f*q⁻¹)).val ∞ = ∞ := by
    rcases he with he | he
    · rw [he]
      apply (realSLMobius_fixed_infty_iff _).mpr
      rfl
    · rw [he,realSLMobius_neg]
      apply (realSLMobius_fixed_infty_iff _).mpr
      rfl
  have hp : Mobius.MobiusParabolic (realSLMobius (q*f*q⁻¹)) := by
    rw [map_mul,map_mul,map_inv]
    exact (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨realSLMobius q,rfl⟩)).mp hf
  obtain ⟨w,hw⟩ := hp.2
  have hqp := (realSLMobius_conjugate_fixed_iff f q (hParabolicIdealPoint f hf)).mpr
    (hParabolicIdealPoint_fixed f hf)
  have hq : (realSLMobius q).val (hParabolicIdealPoint f hf) = ∞ :=
    ((hw _).mp hqp).trans ((hw _).mp hi).symm
  let g := Matrix.SpecialLinearGroup.mapGL ℝ q
  have hg : 0 < g.val.det := by change 0 < q.val.det; rw [q.det_coe]; norm_num
  have hE := L.idealEndpoints_realGL_image (L.realGLMap g) g hg (L.realGLMap_carrier g).symm
  have hInf : (∞ : Mobius.ExtendedComplex) ∈ (L.realGLMap g).idealEndpoints := by
    rw [hE]
    refine ⟨hParabolicIdealPoint f hf,hL,?_⟩
    simpa only [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,
      realSLMobius_matrix] using hq
  obtain ⟨x,hx⟩ := (HalfPlaneLine.infty_idealEndpoint_iff _).mp hInf
  exact ⟨q,t,x,ht,hact,hx,hq⟩

/-- Any geodesic ending at the genuine parabolic fixed point is an actual reflection factor. -/
theorem realSL_parabolic_reflection_factor (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusParabolic (realSLMobius f)) (L : HalfPlaneLine)
    (hL : hParabolicIdealPoint f hf ∈ L.idealEndpoints) :
    ∃ M : HalfPlaneLine, (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection := by
  obtain ⟨q,t,x,ht,hact,hx,hq⟩ := realSL_parabolic_pencil_normalizer f hf L hL
  let N := HalfPlaneLine.vertical (x+t/2)
  have he : ∀ z : ℍ, (q*f*q⁻¹) • z = N.reflection ((HalfPlaneLine.vertical x).reflection z) := by
    intro z
    rw [hact,congrFun (translation_reflection_factor t x) z]
    rfl
  have h := realSL_two_reflections_transport f q (.vertical x) N he
  rw [← hx,HalfPlaneLine.realGLMap_inv] at h
  exact ⟨N.realGLMap ((Matrix.SpecialLinearGroup.mapGL ℝ q)⁻¹),h⟩

/-- Equality of actual native actions determines the genuine projective Mobius map. -/
theorem realSLMobius_ext_action (f k : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (he : ∀ z : ℍ, f • z = k • z) : realSLMobius f = realSLMobius k := by
  let a := metricProbe 0 1 (by norm_num)
  let b := metricProbe 1 1 (by norm_num)
  let c := metricProbe 2 1 (by norm_num)
  have hd : Mobius.TripleDistinct ((a : ℂ) : Mobius.ExtendedComplex) ((b : ℂ) : Mobius.ExtendedComplex)
      ((c : ℂ) : Mobius.ExtendedComplex) := by
    constructor
    · intro h
      have hr := congrArg (fun z : ℂ => z.re) (OnePoint.coe_eq_coe.mp h)
      norm_num [a,b,metricProbe] at hr
    · constructor
      · intro h
        have hr := congrArg (fun z : ℂ => z.re) (OnePoint.coe_eq_coe.mp h)
        norm_num [a,c,metricProbe] at hr
      · intro h
        have hr := congrArg (fun z : ℂ => z.re) (OnePoint.coe_eq_coe.mp h)
        norm_num [b,c,metricProbe] at hr
  apply Mobius.mobius_eq_of_agree_triple _ _ _ _ _ hd
  all_goals rw [realSLMobius_action,realSLMobius_action,he]

/-- Conjugating a two-reflection action moves both actual factor lines. -/
theorem realSL_two_reflections_conjugate (f q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (L M : HalfPlaneLine)
    (he : (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection) :
    ((q*f*q⁻¹) • · : ℍ → ℍ) =
      (M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)).reflection ∘
      (L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)).reflection := by
  have heq : q⁻¹*(q*f*q⁻¹)*(q⁻¹)⁻¹=f := by group
  have h := realSL_two_reflections_transport (q*f*q⁻¹) q⁻¹ L M (by
    intro z
    rw [heq]
    exact congrFun he z)
  simpa only [map_inv,inv_inv] using h

/-- Any actual pair of parallel geodesics has a genuine real SL vertical normalizer. -/
theorem HalfPlaneLine.parallel_SL_normalizer (L M : HalfPlaneLine) (hp : L.Parallel M) :
    ∃ (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a b : ℝ), a ≠ b ∧
      L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q) = .vertical a ∧
      M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q) = .vertical b := by
  have hne := hp.1
  obtain ⟨p,hp⟩ := hp.2
  have hpLM : p ∈ L.idealEndpoints ∩ M.idealEndpoints := by rw [hp]; simp
  obtain ⟨q,hq⟩ := realSLMobius_exists_send_to_infty p hpLM.1.2
  let g := Matrix.SpecialLinearGroup.mapGL ℝ q
  have hg : 0 < g.val.det := by change 0 < q.val.det; rw [q.det_coe]; norm_num
  have hfraction : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) p = ∞ := by
    simpa only [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,
      realSLMobius_matrix] using hq
  have hInf (N : HalfPlaneLine) (hN : p ∈ N.idealEndpoints) :
      (∞ : Mobius.ExtendedComplex) ∈ (N.realGLMap g).idealEndpoints := by
    rw [N.idealEndpoints_realGL_image (N.realGLMap g) g hg (N.realGLMap_carrier g).symm]
    exact ⟨p,hN,hfraction⟩
  obtain ⟨a,ha⟩ := (HalfPlaneLine.infty_idealEndpoint_iff _).mp (hInf L hpLM.1)
  obtain ⟨b,hb⟩ := (HalfPlaneLine.infty_idealEndpoint_iff _).mp (hInf M hpLM.2)
  refine ⟨q,a,b,?_,ha,hb⟩
  intro hab
  apply hne
  exact (HalfPlaneLine.realGLMap_injective g) (ha.trans (hab ▸ hb.symm))

/-- Parallel genuine reflection factors characterize the actual parabolic type. -/
theorem realSL_parallel_reflections_parabolic (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (L M : HalfPlaneLine) (hp : L.Parallel M)
    (he : (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection) :
    Mobius.MobiusParabolic (realSLMobius f) := by
  obtain ⟨q,a,b,hab,hL,hM⟩ := L.parallel_SL_normalizer M hp
  let B := q*f*q⁻¹
  let t := 2*(b-a)
  have hconj := realSL_two_reflections_conjugate f q L M he
  rw [hL,hM] at hconj
  have hact : ∀ z : ℍ, B • z = hTranslationSL t • z := by
    intro z
    have ht := congrFun (translation_reflection_factor t a) z
    have hmid : a+t/2=b := by dsimp only [t]; ring
    rw [hmid] at ht
    exact (congrFun hconj z).trans ht.symm
  have heq := realSLMobius_ext_action B (hTranslationSL t) hact
  have hproj : realSLMobius B = realSLMobius q * realSLMobius f * (realSLMobius q)⁻¹ := by
    simp only [B,map_mul,map_inv]
  have hn : realSLMobius B ≠ 1 := by
    intro hh
    apply hf
    calc
      realSLMobius f = (realSLMobius q)⁻¹ *
          (realSLMobius q * realSLMobius f * (realSLMobius q)⁻¹) * realSLMobius q := by group
      _ = 1 := by rw [← hproj,hh]; simp
  have hTn : realSLMobius (hTranslationSL t) ≠ 1 := by rwa [← heq]
  have hP : Mobius.MobiusParabolic (realSLMobius B) := by
    rw [heq]
    apply (realSLMobius_parabolic_iff _ hTn).mpr
    norm_num [hTranslationSL,Matrix.trace_fin_two]
  apply (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨realSLMobius q,hproj.symm⟩)).mpr hP

/-- The unique parabolic ideal point stays an endpoint of the other actual factor. -/
theorem realSL_parabolic_reflection_factor_endpoint (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusParabolic (realSLMobius f)) (L : HalfPlaneLine)
    (hL : hParabolicIdealPoint f hf ∈ L.idealEndpoints) :
    ∃ M : HalfPlaneLine, hParabolicIdealPoint f hf ∈ M.idealEndpoints ∧
      (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection := by
  obtain ⟨q,t,x,ht,hact,hx,hq⟩ := realSL_parabolic_pencil_normalizer f hf L hL
  let g := Matrix.SpecialLinearGroup.mapGL ℝ q
  let N := HalfPlaneLine.vertical (x+t/2)
  let M := N.realGLMap g⁻¹
  have he : ∀ z : ℍ, (q*f*q⁻¹) • z = N.reflection ((HalfPlaneLine.vertical x).reflection z) := by
    intro z
    rw [hact,congrFun (translation_reflection_factor t x) z]
    rfl
  have h := realSL_two_reflections_transport f q (.vertical x) N he
  rw [← hx,HalfPlaneLine.realGLMap_inv] at h
  refine ⟨M,?_,h⟩
  have hg : 0 < (g⁻¹).val.det := by
    dsimp only [g]
    rw [← map_inv]
    change 0 < (q⁻¹).val.det
    rw [(q⁻¹).det_coe]
    norm_num
  rw [N.idealEndpoints_realGL_image M g⁻¹ hg (N.realGLMap_carrier g⁻¹).symm]
  refine ⟨∞,?_,?_⟩
  · simp [N,vertical_idealEndpoints]
  · have hqg : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (hParabolicIdealPoint f hf) = ∞ := by
      simpa only [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,
        realSLMobius_matrix] using hq
    rw [realMobiusMatrix_inv,← hqg,Mobius.fractionalLinear_inv_apply]

/-- A nonidentity parabolic native action has no interior fixed point. -/
theorem realSL_parabolic_no_fixed (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusParabolic (realSLMobius f)) (z : ℍ) : f • z ≠ z := by
  intro hz
  have hfix : (realSLMobius f).val ((z : ℂ) : Mobius.ExtendedComplex) = (z : ℂ) := by
    rw [realSLMobius_action,hz]
  have hi := (coe_mem_halfPlaneIdealBoundary (z : ℂ)).mp
    (realSLMobius_parabolic_fixed_boundary f hf _ hfix)
  exact z.im_ne_zero hi

/-- The freely chosen parabolic factor has a unique partner in its genuine pencil. -/
theorem realSL_parabolic_reflection_factor_unique (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusParabolic (realSLMobius f)) (L : HalfPlaneLine)
    (hL : hParabolicIdealPoint f hf ∈ L.idealEndpoints) :
    ∃! M : HalfPlaneLine, hParabolicIdealPoint f hf ∈ M.idealEndpoints ∧
      L.Parallel M ∧ (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection := by
  obtain ⟨M,hM,he⟩ := realSL_parabolic_reflection_factor_endpoint f hf L hL
  have hne : L ≠ M := by
    intro hLM
    subst M
    have hfix : f • UpperHalfPlane.I = UpperHalfPlane.I := by
      rw [congrFun he,Function.comp_apply,L.reflection_involutive]
    exact realSL_parabolic_no_fixed f hf _ hfix
  have hpar : L.Parallel M := by
    refine ⟨hne,hParabolicIdealPoint f hf,?_⟩
    ext p
    constructor
    · intro hp
      exact Set.mem_singleton_iff.mpr ((L.idealEndpoints_inter_subsingleton M hne) hp ⟨hL,hM⟩)
    · intro hp
      have hp' := Set.mem_singleton_iff.mp hp
      subst p
      exact ⟨hL,hM⟩
  exact ⟨M,⟨hM,hpar,he⟩,fun N hN => realSL_reflection_factor_unique f L N M hN.2.2 he⟩

/-- Every genuine ideal boundary point is the endpoint of an actual geodesic. -/
theorem exists_halfPlaneLine_ideal_endpoint (p : Mobius.ExtendedComplex) (hp : p ∈ halfPlaneIdealBoundary) :
    ∃ L : HalfPlaneLine, p ∈ L.idealEndpoints := by
  induction p using OnePoint.rec with
  | infty => exact ⟨.vertical 0,by simp [vertical_idealEndpoints]⟩
  | coe z =>
    have hi := (coe_mem_halfPlaneIdealBoundary z).mp hp
    have hz : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    exact ⟨.vertical z.re,by rw [hz]; simp [vertical_idealEndpoints]⟩

/-- The genuine parabolic classification is exactly the parallel-reflection criterion. -/
theorem realSL_parabolic_iff_parallel_reflections (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) :
    Mobius.MobiusParabolic (realSLMobius f) ↔ ∃ L M : HalfPlaneLine, L.Parallel M ∧
      (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection := by
  constructor
  · intro hP
    have hp := realSLMobius_parabolic_fixed_boundary f hP _ (hParabolicIdealPoint_fixed f hP)
    obtain ⟨L,hL⟩ := exists_halfPlaneLine_ideal_endpoint (hParabolicIdealPoint f hP) hp
    obtain ⟨M,hM,_⟩ := realSL_parabolic_reflection_factor_unique f hP L hL
    exact ⟨L,M,hM.2.1,hM.2.2⟩
  · rintro ⟨L,M,hp,he⟩
    exact realSL_parallel_reflections_parabolic f hf L M hp he

/-- The actual image of a vertical geodesic under the genuine translation. -/
theorem translation_vertical_line_image (t x : ℝ) :
    (hTranslationSL t • · : ℍ → ℍ) '' (HalfPlaneLine.vertical x).carrier =
      (HalfPlaneLine.vertical (x+t)).carrier := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change (hTranslationSL t • w).re=x+t
    have he := congrArg Complex.re (hTranslationSL_coe t w)
    change (hTranslationSL t • w).re=w.re+t at he
    exact he.trans (congrArg (fun r : ℝ => r+t) hw)
  · intro hz
    refine ⟨metricProbe x z.im z.im_pos,rfl,?_⟩
    apply UpperHalfPlane.ext
    rw [hTranslationSL_coe]
    apply Complex.ext
    · change x+t=z.re
      exact hz.symm
    · simp [metricProbe]

/-- The second reflection line is the entire genuine equidistance bisector of
an arbitrarily prescribed line and its actual parabolic image. -/
theorem realSL_parabolic_factor_bisector (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusParabolic (realSLMobius f)) (L : HalfPlaneLine)
    (hL : hParabolicIdealPoint f hf ∈ L.idealEndpoints) :
    ∃ M : HalfPlaneLine, (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection ∧
      L.bisectorSet (L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ f)) = M.carrier := by
  obtain ⟨q,t,x,ht,hact,hx,_⟩ := realSL_parabolic_pencil_normalizer f hf L hL
  let g := Matrix.SpecialLinearGroup.mapGL ℝ q
  let F := Matrix.SpecialLinearGroup.mapGL ℝ f
  let N := HalfPlaneLine.vertical (x+t/2)
  let M := N.realGLMap g⁻¹
  have he : ∀ z : ℍ, (q*f*q⁻¹) • z = N.reflection ((HalfPlaneLine.vertical x).reflection z) := by
    intro z
    rw [hact,congrFun (translation_reflection_factor t x) z]
    rfl
  have h := realSL_two_reflections_transport f q (.vertical x) N he
  rw [← hx,HalfPlaneLine.realGLMap_inv] at h
  refine ⟨M,h,?_⟩
  have himgL : (g • · : ℍ → ℍ) '' L.carrier = (HalfPlaneLine.vertical x).carrier := by
    rw [← L.realGLMap_carrier g,hx]
  have himgF : (g • · : ℍ → ℍ) '' (L.realGLMap F).carrier =
      (HalfPlaneLine.vertical (x+t)).carrier := by
    rw [L.realGLMap_carrier F,image_image]
    have hcomp : (fun w : ℍ => g • (F • w)) =
        (fun w : ℍ => (q*f*q⁻¹) • (q • w)) := by
      funext w
      change q • (f • w) = (q*f*q⁻¹) • (q • w)
      simp only [mul_smul,inv_smul_smul]
    rw [hcomp,← image_image]
    change (fun w : ℍ => (q*f*q⁻¹) • w) '' ((g • · : ℍ → ℍ) '' L.carrier) = _
    rw [himgL]
    have hfun : (fun w : ℍ => (q*f*q⁻¹) • w) = (hTranslationSL t • · : ℍ → ℍ) := funext hact
    rw [hfun,translation_vertical_line_image]
  have hxt : x ≠ x+t := by intro he; apply ht; linarith
  have hBis : (HalfPlaneLine.vertical x).bisectorSet (HalfPlaneLine.vertical (x+t))=N.carrier := by
    rw [vertical_bisectorSet x (x+t) hxt]
    have hmid : (x+(x+t))/2=x+t/2 := by ring
    rw [hmid]
  have hb := L.bisectorSet_image_isometry (L.realGLMap F) (.vertical x) (.vertical (x+t))
    (g • ·) (realGL_isometry g) himgL himgF
  rw [hBis] at hb
  have hback : M.realGLMap g=N := by
    simpa only [inv_inv] using N.realGLMap_inv g⁻¹
  apply (realGL_isometry g).injective.image_injective
  rw [hb,← M.realGLMap_carrier g,hback]

/-- Inversion preserves the actual parabolic class. -/
theorem realSL_parabolic_inv (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusParabolic (realSLMobius f)) : Mobius.MobiusParabolic (realSLMobius f⁻¹) := by
  rw [map_inv]
  refine ⟨inv_ne_one.mpr hf.1,hf.2.choose,?_⟩
  intro z
  have hi : ((realSLMobius f)⁻¹).val z = z ↔ (realSLMobius f).val z = z := by
    constructor
    · intro hz
      simpa only [inv_inv] using Mobius.mobius_inv_fixed hz
    · exact Mobius.mobius_inv_fixed
  rw [hi]
  exact hf.2.choose_spec z

/-- The inverse has the same genuine ideal fixed point. -/
theorem hParabolicIdealPoint_inv (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusParabolic (realSLMobius f)) :
    hParabolicIdealPoint f⁻¹ (realSL_parabolic_inv f hf) = hParabolicIdealPoint f hf := by
  have hi := hParabolicIdealPoint_fixed f⁻¹ (realSL_parabolic_inv f hf)
  rw [map_inv] at hi
  have hfix := Mobius.mobius_inv_fixed hi
  simp only [inv_inv] at hfix
  exact (hf.2.choose_spec _).mp hfix

/-- The second factor may also be prescribed freely in the genuine parabolic pencil. -/
theorem realSL_parabolic_reflection_factor_right (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusParabolic (realSLMobius f)) (L : HalfPlaneLine)
    (hL : hParabolicIdealPoint f hf ∈ L.idealEndpoints) :
    ∃! M : HalfPlaneLine, hParabolicIdealPoint f hf ∈ M.idealEndpoints ∧
      L.Parallel M ∧ (f • · : ℍ → ℍ) = L.reflection ∘ M.reflection := by
  obtain ⟨M,hM,_⟩ := realSL_parabolic_reflection_factor_unique f⁻¹ (realSL_parabolic_inv f hf) L
    (by rw [hParabolicIdealPoint_inv f hf];exact hL)
  rw [hParabolicIdealPoint_inv f hf] at hM
  have he : (f • · : ℍ → ℍ) = L.reflection ∘ M.reflection := by
    funext z
    have hr := congrFun hM.2.2 (f • z)
    simp only [Function.comp_apply,inv_smul_smul] at hr
    have h1 := congrArg M.reflection hr
    rw [M.reflection_involutive] at h1
    have h2 := congrArg L.reflection h1
    rw [L.reflection_involutive] at h2
    exact h2.symm
  refine ⟨M,⟨hM.1,hM.2.1,he⟩,?_⟩
  intro N hN
  apply HalfPlaneLine.reflection_injective
  funext z
  apply L.reflection_isometry.injective
  exact congrFun (hN.2.2.symm.trans he) z

end LowDimensionalTopology.Geometry.Hyperbolic
