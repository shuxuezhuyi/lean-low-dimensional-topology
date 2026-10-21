/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ParabolicReflectionPencils
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

/-- A positive-periodic boundary point of a true loxodromic transformation is fixed. -/
theorem loxodromic_positive_periodic_boundary_fixed (f : Mobius.complexMobiusGroup)
    (hf : Mobius.MobiusLoxodromic f) (z : Mobius.ExtendedComplex) (n : ℕ) (hn : 0 < n)
    (hz : (f^n).val z=z) : f.val z=z := by
  by_contra hfix
  have hinj := Mobius.mobius_loxodromic_orbit_injective f hf z hfix
  have he : (f^(n:ℤ)).val z=(f^(0:ℤ)).val z := by
    rw [zpow_natCast,zpow_zero]
    exact hz
  have hn0 : (n:ℤ)=0 := hinj he
  exact hn.ne' (Int.natCast_eq_zero.mp hn0)

/-- The actual axis is the unique genuine invariant geodesic of a hyperbolic action. -/
theorem hHyperbolicAxis_unique_invariant (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val)^2)
    (L : HalfPlaneLine) (hL : (f • · : ℍ → ℍ) '' L.carrier=L.carrier) :
    L=hHyperbolicAxis f hf ht := by
  let F := realSLMobius f
  have hH : Mobius.MobiusLoxodromic F := ((realSLMobius_hyperbolic_iff f hf).mpr ht).1
  let g := Matrix.SpecialLinearGroup.mapGL ℝ f
  have hg : 0 < g.val.det := by change 0 < f.val.det;rw [f.det_coe];norm_num
  have hI : F.val '' L.idealEndpoints=L.idealEndpoints := by
    have hh := L.idealEndpoints_realGL_image L g hg hL
    have hfraction : F.val=Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) := by
      change (realSLMobius f).val=Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)
      rw [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,realSLMobius_matrix]
    rw [← hfraction] at hh
    exact hh.symm
  obtain ⟨a,b,_,hab,_,_,hends,_⟩ := L.exists_idealEndpoints_pair
  have hmem (z : Mobius.ExtendedComplex) (hz : z ∈ L.idealEndpoints) : F.val z ∈ L.idealEndpoints := by
    rw [← hI]
    exact ⟨z,hz,rfl⟩
  have hperiod (z : Mobius.ExtendedComplex) (hz : z ∈ L.idealEndpoints) : (F^2).val z=z := by
    have hz1 := hmem z hz
    have hz2 := hmem (F.val z) hz1
    rw [hends] at hz hz1 hz2
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz hz1 hz2
    change F.val (F.val z)=z
    by_cases he : F.val z=z
    · rw [he,he]
    · have hn : F.val (F.val z) ≠ F.val z := F.val.injective.ne he
      rcases hz with hza | hzb
      · rcases hz1 with hfa | hfb
        · exact False.elim (he (hfa.trans hza.symm))
        · rcases hz2 with hffa | hffb
          · exact hffa.trans hza.symm
          · exact False.elim (hn (hffb.trans hfb.symm))
      · rcases hz1 with hfa | hfb
        · rcases hz2 with hffa | hffb
          · exact False.elim (hn (hffa.trans hfa.symm))
          · exact hffb.trans hzb.symm
        · exact False.elim (he (hfb.trans hzb.symm))
  have hsub : L.idealEndpoints ⊆ Function.fixedPoints F.val := by
    intro z hz
    exact loxodromic_positive_periodic_boundary_fixed F hH z 2 (by norm_num) (hperiod z hz)
  have hpair := realSLMobius_hyperbolic_fixed_pair f hf ht
  obtain ⟨c,d,hcd,_,_,hfix⟩ := hpair
  have ha : a ∈ Function.fixedPoints F.val := hsub (hends ▸ (by simp))
  have hb : b ∈ Function.fixedPoints F.val := hsub (hends ▸ (by simp))
  have he : L.idealEndpoints=Function.fixedPoints F.val := by
    rw [hends]
    change ({a,b} : Set Mobius.ExtendedComplex)=Function.fixedPoints (realSLMobius f).val
    have hfs : Function.fixedPoints (realSLMobius f).val={c,d} := by ext z;exact hfix z
    rw [hfs] at ha hb ⊢
    exact (pair_eq_of_two_mem_ne ha hb hab).symm
  exact hHyperbolicAxis_unique f hf ht L he

/-- Positive dilation factors through any actual concentric semicircle. -/
theorem dilation_reflection_factor (k r : ℝ) (hk : 0<k) (hr : 0<r) :
    (verticalDilationSL k hk • · : ℍ → ℍ) =
      (HalfPlaneLine.circle 0 (Real.sqrt k*r) (mul_pos (Real.sqrt_pos.mpr hk) hr)).reflection ∘
      (HalfPlaneLine.circle 0 r hr).reflection := by
  funext z
  apply UpperHalfPlane.ext
  change ((verticalDilationSL k hk • z : ℍ) : ℂ) =
    (circleReflection 0 (Real.sqrt k*r) _ (circleReflection 0 r hr z) : ℂ)
  rw [verticalDilationSL_coe,circleReflection_coe,circleReflection_coe]
  simp only [Complex.ofReal_zero,zero_add,sub_zero,map_div₀,map_pow,
    Complex.conj_ofReal,Complex.conj_conj]
  have hs : (Real.sqrt k : ℂ)^2=(k : ℂ) := by exact_mod_cast Real.sq_sqrt hk.le
  have hrC : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast
  field_simp [hrC,z.ne_zero]
  linear_combination -hs

/-- A real SL normalizer sends the whole actual hyperbolic axis to the imaginary axis. -/
theorem hHyperbolicAxis_realSL_image (f q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (ht : 4<(Matrix.trace f.val)^2)
    (haxis : (hHyperbolicAxis f hf ht).carrier={z : ℍ | (q•z).re=0}) :
    (hHyperbolicAxis f hf ht).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)=.vertical 0 := by
  apply HalfPlaneLine.carrier_injective
  rw [HalfPlaneLine.realGLMap_carrier]
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    rw [haxis] at hw
    change (q•w).re=0
    exact hw
  · intro hz
    change z.re=0 at hz
    refine ⟨q⁻¹•z,?_,?_⟩
    · rw [haxis]
      change (q•(q⁻¹•z)).re=0
      simpa only [smul_inv_smul] using hz
    · change q•(q⁻¹•z)=z
      exact smul_inv_smul q z

/-- The actual geodesics perpendicular to the imaginary axis are exactly its centered circles. -/
theorem HalfPlaneLine.orthogonal_vertical_zero (L : HalfPlaneLine)
    (hO : L.Orthogonal (.vertical 0)) :
    ∃ (r : ℝ) (hr : 0<r), L=.circle 0 r hr := by
  have hc := (L.orthogonal_iff_coefficients (.vertical 0)).mp hO
  cases L with
  | vertical x => exact hc.elim
  | circle c r hr =>
    change c=0 at hc
    subst c
    exact ⟨r,hr,rfl⟩

/-- Every actual perpendicular to the hyperbolic axis is a freely prescribed factor line. -/
theorem realSL_hyperbolic_reflection_factor (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (ht : 4<(Matrix.trace f.val)^2) (L : HalfPlaneLine)
    (hO : L.Orthogonal (hHyperbolicAxis f hf ht)) :
    ∃! M : HalfPlaneLine, M.Orthogonal (hHyperbolicAxis f hf ht) ∧
      (f•· : ℍ→ℍ)=M.reflection ∘ L.reflection := by
  obtain ⟨q,k,hk,hk1,haxis,hT,hact⟩ := hHyperbolicAxis_normalizer f hf ht
  let g := Matrix.SpecialLinearGroup.mapGL ℝ q
  let A := hHyperbolicAxis f hf ht
  have hA : A.realGLMap g=.vertical 0 := hHyperbolicAxis_realSL_image f q hf ht haxis
  have hOL := L.orthogonal_isometry_image A (L.realGLMap g) (A.realGLMap g)
    (g•·) (realGL_isometry g) (L.realGLMap_carrier g).symm (A.realGLMap_carrier g).symm hO
  rw [hA] at hOL
  obtain ⟨r,hr,hL⟩ := (L.realGLMap g).orthogonal_vertical_zero hOL
  let N := HalfPlaneLine.circle 0 (Real.sqrt k*r) (mul_pos (Real.sqrt_pos.mpr hk) hr)
  let M := N.realGLMap g⁻¹
  have he : ∀ z : ℍ, (q*f*q⁻¹)•z=N.reflection ((HalfPlaneLine.circle 0 r hr).reflection z) := by
    intro z
    rw [hact,congrFun (dilation_reflection_factor k r hk hr) z]
    rfl
  have h := realSL_two_reflections_transport f q (.circle 0 r hr) N he
  rw [←hL,HalfPlaneLine.realGLMap_inv] at h
  have hNO : N.Orthogonal (.vertical 0) := by
    apply (N.orthogonal_iff_coefficients (.vertical 0)).mpr
    rfl
  have hAi : (g⁻¹•· : ℍ→ℍ) '' (HalfPlaneLine.vertical 0).carrier=A.carrier :=
    realGL_inverse_image_eq g ((A.realGLMap_carrier g).symm.trans (congrArg HalfPlaneLine.carrier hA))
  have hMO := N.orthogonal_isometry_image (.vertical 0) M A (g⁻¹•·) (realGL_isometry g⁻¹)
    (N.realGLMap_carrier g⁻¹).symm hAi hNO
  exact ⟨M,⟨hMO,h⟩,fun P hP => realSL_reflection_factor_unique f L P M hP.2 h⟩

/-- A positive real invertible matrix has a genuine determinant-one lift of its exact native action. -/
theorem positive_realGL_exists_SL (g : GL (Fin 2) ℝ) (hg : 0<g.val.det) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ z : ℍ, q•z=g•z := by
  let u := 1/Real.sqrt g.val.det
  have hu : u≠0 := one_div_ne_zero (Real.sqrt_pos.mpr hg).ne'
  have hdet : Matrix.det (u • g.val)=1 := by
    rw [Matrix.det_smul]
    change u^2*g.val.det=1
    dsimp only [u]
    rw [div_pow,one_pow,Real.sq_sqrt hg.le,one_div_mul_cancel hg.ne']
  let q : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨u • g.val,hdet⟩
  refine ⟨q,?_⟩
  intro z
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,UpperHalfPlane.coe_smul_of_det_pos hg]
  simp only [Algebra.algebraMap_self_apply]
  change (((u*g 0 0 : ℝ) : ℂ)*z+((u*g 0 1 : ℝ) : ℂ)) /
    (((u*g 1 0 : ℝ) : ℂ)*z+((u*g 1 1 : ℝ) : ℂ)) =
      ((g 0 0 : ℂ)*z+(g 0 1 : ℂ))/((g 1 0 : ℂ)*z+(g 1 1 : ℂ))
  push_cast
  have hnum : (u:ℂ)*(g 0 0:ℂ)*z+(u:ℂ)*(g 0 1:ℂ)=
      (u:ℂ)*((g 0 0:ℂ)*z+(g 0 1:ℂ)) := by ring
  have hden : (u:ℂ)*(g 1 0:ℂ)*z+(u:ℂ)*(g 1 1:ℂ)=
      (u:ℂ)*((g 1 0:ℂ)*z+(g 1 1:ℂ)) := by ring
  rw [hnum,hden,mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hu)]

/-- An arbitrary genuine disjoint pair has a true determinant-one concentric normalizer. -/
theorem HalfPlaneLine.disjoint_SL_normalizer (L M : HalfPlaneLine) (hd : L.HDisjoint M) :
    ∃ (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (s t : ℝ) (hs : 0<s) (ht : 0<t), s≠t ∧
      L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)=.circle 0 s hs ∧
      M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)=.circle 0 t ht := by
  obtain ⟨g,s,t,hs,ht,hg,hst,hL,hM⟩ := L.exists_concentric_normalizer M hd
  obtain ⟨q,hq⟩ := positive_realGL_exists_SL g hg
  refine ⟨q,s,t,hs,ht,hst,?_,?_⟩
  · apply HalfPlaneLine.carrier_injective
    rw [L.realGLMap_carrier]
    change (q•· : ℍ→ℍ) '' L.carrier=_
    simpa only [hq] using hL
  · apply HalfPlaneLine.carrier_injective
    rw [M.realGLMap_carrier]
    change (q•· : ℍ→ℍ) '' M.carrier=_
    simpa only [hq] using hM

/-- The genuine nontrivial positive dilation has hyperbolic squared real trace. -/
theorem verticalDilationSL_trace_gt_four (k : ℝ) (hk : 0<k) (hk1 : k≠1) :
    4<(Matrix.trace (verticalDilationSL k hk).val)^2 := by
  have hs : (Real.sqrt k)^2=k := Real.sq_sqrt hk.le
  have hm : Real.sqrt k*(1/Real.sqrt k)=1 := mul_one_div_cancel (Real.sqrt_pos.mpr hk).ne'
  have hn : Real.sqrt k-1/Real.sqrt k≠0 := by
    intro he
    apply hk1
    have heq := sub_eq_zero.mp he
    have hh : (Real.sqrt k)^2=1 := by
      calc
        (Real.sqrt k)^2=Real.sqrt k*(1/Real.sqrt k) := by rw [←heq,pow_two]
        _=1 := hm
    exact hs.symm.trans hh
  rw [Matrix.trace_fin_two]
  change 4<(Real.sqrt k+1/Real.sqrt k)^2
  nlinarith [sq_pos_of_ne_zero hn]

/-- A genuine concentric reflection normal form forces the hyperbolic type. -/
theorem realSL_concentric_reflections_hyperbolic (f q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (L M : HalfPlaneLine)
    (he : (f•· : ℍ→ℍ)=M.reflection ∘ L.reflection)
    (s t : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (hL : L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)=.circle 0 s hs)
    (hM : M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)=.circle 0 t ht) :
    Mobius.MobiusHyperbolic (realSLMobius f) := by
  let k := (t/s)^2
  have hk : 0<k := sq_pos_of_pos (div_pos ht hs)
  have hk1 : k≠1 := by intro h;apply hst;dsimp only [k] at h;nlinarith [div_mul_cancel₀ t hs.ne',div_pos ht hs]
  have hroot : Real.sqrt k*s=t := by
    dsimp only [k]
    rw [Real.sqrt_sq (div_pos ht hs).le,div_mul_cancel₀ t hs.ne']
  let B := q*f*q⁻¹
  have hc := realSL_two_reflections_conjugate f q L M he
  rw [hL,hM] at hc
  have hact : ∀ z : ℍ, B•z=verticalDilationSL k hk•z := by
    intro z
    have hD := congrFun (dilation_reflection_factor k s hk hs) z
    simp only [hroot] at hD
    exact (congrFun hc z).trans hD.symm
  have hproj := realSLMobius_ext_action B (verticalDilationSL k hk) hact
  have htrace := congrArg Mobius.mobiusSquaredTrace hproj
  rw [realSLMobius_squaredTrace,realSLMobius_squaredTrace] at htrace
  have htr : (Matrix.trace B.val)^2=(Matrix.trace (verticalDilationSL k hk).val)^2 :=
    Complex.ofReal_injective htrace
  have hconj : realSLMobius B=realSLMobius q*realSLMobius f*(realSLMobius q)⁻¹ := by
    simp only [B,map_mul,map_inv]
  have hn : realSLMobius B≠1 := by
    intro hh
    apply hf
    calc
      realSLMobius f=(realSLMobius q)⁻¹*(realSLMobius q*realSLMobius f*(realSLMobius q)⁻¹)*realSLMobius q := by group
      _=1 := by rw [←hconj,hh];simp
  have hB : Mobius.MobiusHyperbolic (realSLMobius B) := by
    apply (realSLMobius_hyperbolic_iff B hn).mpr
    rw [htr]
    exact verticalDilationSL_trace_gt_four k hk hk1
  exact (Mobius.mobiusHyperbolic_isConj (isConj_iff.mpr ⟨realSLMobius q,hconj.symm⟩)).mpr hB

/-- Disjoint genuine factor lines give the actual hyperbolic type. -/
theorem realSL_disjoint_reflections_hyperbolic (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (L M : HalfPlaneLine) (hd : L.HDisjoint M)
    (he : (f•· : ℍ→ℍ)=M.reflection ∘ L.reflection) :
    Mobius.MobiusHyperbolic (realSLMobius f) := by
  obtain ⟨q,s,t,hs,ht,hst,hL,hM⟩ := L.disjoint_SL_normalizer M hd
  exact realSL_concentric_reflections_hyperbolic f q hf L M he s t hs ht hst hL hM

/-- Every genuine line has an exact determinant-one normalizer to the imaginary axis. -/
theorem HalfPlaneLine.exists_SL_normalizer (L : HalfPlaneLine) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)=.vertical 0 := by
  obtain ⟨g,hg,hL⟩ := L.exists_mobius_map (.vertical 0)
  obtain ⟨q,hq⟩ := positive_realGL_exists_SL g hg
  refine ⟨q,?_⟩
  apply HalfPlaneLine.carrier_injective
  rw [L.realGLMap_carrier]
  change (q•· : ℍ→ℍ) '' L.carrier=_
  simpa only [hq] using hL

/-- Two distinct genuine lines with a common perpendicular are a hyperbolic factor pencil. -/
theorem realSL_common_perpendicular_reflections_hyperbolic (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (L M N : HalfPlaneLine) (hne : L≠M)
    (hLN : L.Orthogonal N) (hMN : M.Orthogonal N)
    (he : (f•· : ℍ→ℍ)=M.reflection ∘ L.reflection) :
    Mobius.MobiusHyperbolic (realSLMobius f) := by
  obtain ⟨q,hN⟩ := N.exists_SL_normalizer
  let g := Matrix.SpecialLinearGroup.mapGL ℝ q
  have hLO := L.orthogonal_isometry_image N (L.realGLMap g) (N.realGLMap g)
    (g•·) (realGL_isometry g) (L.realGLMap_carrier g).symm (N.realGLMap_carrier g).symm hLN
  have hMO := M.orthogonal_isometry_image N (M.realGLMap g) (N.realGLMap g)
    (g•·) (realGL_isometry g) (M.realGLMap_carrier g).symm (N.realGLMap_carrier g).symm hMN
  rw [hN] at hLO hMO
  obtain ⟨s,hs,hL⟩ := (L.realGLMap g).orthogonal_vertical_zero hLO
  obtain ⟨t,ht,hM⟩ := (M.realGLMap g).orthogonal_vertical_zero hMO
  have hst : s≠t := by
    intro hst
    apply hne
    apply HalfPlaneLine.realGLMap_injective g
    subst t
    exact hL.trans hM.symm
  exact realSL_concentric_reflections_hyperbolic f q hf L M he s t hs ht hst hL hM

/-- Symmetry for actual native tangent orthogonality. -/
theorem HalfPlaneLine.orthogonal_symm (L M : HalfPlaneLine) (h : L.Orthogonal M) : M.Orthogonal L := by
  obtain ⟨z,hz⟩ := h
  exact ⟨z,hz.2.1,hz.1,(real_inner_comm _ _).trans hz.2.2⟩

/-- A genuine hyperbolic action has no fixed point in the native plane. -/
theorem realSL_hyperbolic_no_fixed (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : 4<(Matrix.trace f.val)^2) (z : ℍ) : f•z≠z := by
  intro hz
  have hfix : (realSLMobius f).val ((z:ℂ):Mobius.ExtendedComplex)=(z:ℂ) := by
    rw [realSLMobius_action,hz]
  exact z.im_ne_zero ((coe_mem_halfPlaneIdealBoundary (z:ℂ)).mp
    (realSLMobius_hyperbolic_fixed_boundary f ht _ hfix))

/-- The actual hyperbolic class is exactly the product of distinct genuine reflections
in one perpendicular pencil. -/
theorem realSL_hyperbolic_iff_perpendicular_reflections (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) :
    Mobius.MobiusHyperbolic (realSLMobius f) ↔ ∃ L M N : HalfPlaneLine,
      L≠M ∧ L.Orthogonal N ∧ M.Orthogonal N ∧
      (f•· : ℍ→ℍ)=M.reflection ∘ L.reflection := by
  constructor
  · intro hH
    have ht := (realSLMobius_hyperbolic_iff f hf).mp hH
    let N := hHyperbolicAxis f hf ht
    obtain ⟨L,hL,_⟩ := N.existsUnique_perpendicular UpperHalfPlane.I
    have hLN := N.orthogonal_symm L hL.2
    obtain ⟨M,hM,_⟩ := realSL_hyperbolic_reflection_factor f hf ht L hLN
    have hne : L≠M := by
      intro hLM
      subst M
      have hfix : f•UpperHalfPlane.I=UpperHalfPlane.I := by
        rw [congrFun hM.2,Function.comp_apply,L.reflection_involutive]
      exact realSL_hyperbolic_no_fixed f ht _ hfix
    exact ⟨L,M,N,hne,hLN,hM.1,hM.2⟩
  · rintro ⟨L,M,N,hne,hLN,hMN,he⟩
    exact realSL_common_perpendicular_reflections_hyperbolic f hf L M N hne hLN hMN he

/-- The second hyperbolic factor line may also be prescribed arbitrarily among all actual axis perpendiculars. -/
theorem realSL_hyperbolic_reflection_factor_right (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f≠1) (ht : 4<(Matrix.trace f.val)^2) (L : HalfPlaneLine)
    (hO : L.Orthogonal (hHyperbolicAxis f hf ht)) :
    ∃! M : HalfPlaneLine, M.Orthogonal (hHyperbolicAxis f hf ht) ∧
      (f•· : ℍ→ℍ)=L.reflection ∘ M.reflection := by
  obtain ⟨q,k,hk,hk1,haxis,hT,hact⟩ := hHyperbolicAxis_normalizer f hf ht
  let g := Matrix.SpecialLinearGroup.mapGL ℝ q
  let A := hHyperbolicAxis f hf ht
  have hA : A.realGLMap g=.vertical 0 := hHyperbolicAxis_realSL_image f q hf ht haxis
  have hOL := L.orthogonal_isometry_image A (L.realGLMap g) (A.realGLMap g)
    (g•·) (realGL_isometry g) (L.realGLMap_carrier g).symm (A.realGLMap_carrier g).symm hO
  rw [hA] at hOL
  obtain ⟨r,hr,hL⟩ := (L.realGLMap g).orthogonal_vertical_zero hOL
  have ha : 0<r/Real.sqrt k := div_pos hr (Real.sqrt_pos.mpr hk)
  let N := HalfPlaneLine.circle 0 (r/Real.sqrt k) ha
  let M := N.realGLMap g⁻¹
  have hrad : Real.sqrt k*(r/Real.sqrt k)=r := by field_simp [(Real.sqrt_pos.mpr hk).ne']
  have he : ∀ z : ℍ, (q*f*q⁻¹)•z=(HalfPlaneLine.circle 0 r hr).reflection (N.reflection z) := by
    intro z
    have hD := congrFun (dilation_reflection_factor k (r/Real.sqrt k) hk ha) z
    simp only [hrad] at hD
    exact (hact z).trans hD
  have h := realSL_two_reflections_transport f q N (.circle 0 r hr) he
  rw [←hL,HalfPlaneLine.realGLMap_inv] at h
  have hNO : N.Orthogonal (.vertical 0) := by
    apply (N.orthogonal_iff_coefficients (.vertical 0)).mpr
    rfl
  have hAi : (g⁻¹•· : ℍ→ℍ) '' (HalfPlaneLine.vertical 0).carrier=A.carrier :=
    realGL_inverse_image_eq g ((A.realGLMap_carrier g).symm.trans (congrArg HalfPlaneLine.carrier hA))
  have hMO := N.orthogonal_isometry_image (.vertical 0) M A (g⁻¹•·) (realGL_isometry g⁻¹)
    (N.realGLMap_carrier g⁻¹).symm hAi hNO
  refine ⟨M,⟨hMO,h⟩,?_⟩
  intro P hP
  apply HalfPlaneLine.reflection_injective
  funext z
  apply L.reflection_isometry.injective
  exact congrFun (hP.2.symm.trans h) z

end LowDimensionalTopology.Geometry.Hyperbolic
