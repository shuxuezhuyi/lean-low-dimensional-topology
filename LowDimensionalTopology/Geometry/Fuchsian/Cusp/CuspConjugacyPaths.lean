/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.CyclicClassConjugacy
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspNormalizationGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleCuspClassGeometry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem realSL_infinity_fixed_height (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞=∞) (z:ℍ) :
    (A•z:ℍ).im=z.im/(A 1 1)^2 := by
  have hc: A 1 0=0:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mp hA
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.sl2_im_smul]
  congr 1
  change Complex.normSq ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ))=_
  rw [hc]
  simp only [Complex.ofReal_zero,zero_mul,zero_add,Complex.normSq_ofReal,pow_two]

theorem realSL_infinity_fixed_height_tendsto {ι:Type*} {l:Filter ι}
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val
      ∞=∞)
    (z:ι→ℍ) (hz:Tendsto (fun i=>(z i).im) l atTop) :
    Tendsto (fun i=>(A•z i:ℍ).im) l atTop := by
  have hc:A 1 0=0:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mp hA
  have hdet:A 0 0*A 1 1=1:=by
    have h:=A.property
    rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at h
    exact h
  have hd:A 1 1≠0:=by intro h;rw [h,mul_zero] at hdet;norm_num at hdet
  simp only [realSL_infinity_fixed_height A hA]
  exact hz.atTop_div_const (sq_pos_of_ne_zero hd)



/-- The original chosen cusp coordinate has an explicit real vertical correction to a whole-disc native chart. -/
theorem cuspNormalization_explicit_upper_chart {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) {S:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset
      D.domain} {p:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S p) :
    ∃d:ℝ,∃u:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,u=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(d:ℂ)*Complex.I)*C.normalizer ∧
      u.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧u.val p=∞ := by
  obtain ⟨d,hd,_hheight⟩:=cuspNormalization_original_domain_upper D C
  let u:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(d:ℂ)*Complex.I)*C.normalizer
  refine ⟨d,u,rfl,?_,?_⟩
  · change (fun z=>(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(d:ℂ)*Complex.I)).val
    (C.normalizer.val z)) '' D.carrier=_
    rw [←image_image,hd]
    exact vertical_cusp_shift_image d
  · change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
    (-(d:ℂ)*Complex.I)).val (C.normalizer.val p)=∞
    rw [C.cusp_eq,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty]

/-- Two genuine cusp charts aligned by an original whole-disc Mobius conjugacy differ by a real special-linear infinity fixer after their actual vertical corrections. -/
theorem cuspNormalization_conjugacy_native_comparison {H K:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (E:FuchsianDisc K) {S:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset
      D.domain}
    {R:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset E.domain} {p
      w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S
      p) (B:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization R w)
    (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq:q.val '' D.carrier=E.carrier)
    (g:K) (hgp:g.val.val w=q.val p) :
    ∃d e:ℝ,∃u v:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃A:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      u=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(d:ℂ)*Complex.I)*C.normalizer ∧
      v=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(e:ℂ)*Complex.I)*B.normalizer ∧
      u.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧v.val '' E.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=v*g.val⁻¹*q*u⁻¹ ∧(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞=∞ := by
  obtain ⟨d,u,hu,huD,hup⟩:=cuspNormalization_explicit_upper_chart D C
  obtain ⟨e,v,hv,hvE,hvw⟩:=cuspNormalization_explicit_upper_chart E B
  let M:=v*g.val⁻¹*q*u⁻¹
  have huInv:u.val.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=D.carrier:=by
    rw [←huD]
    exact u.val.symm_image_image D.carrier
  have hM:M.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    change (fun z=>v.val (g.val.val.symm (q.val (u.val.symm
      z)))) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_
    calc
      _=v.val '' (g.val.val.symm '' (q.val '' (u.val.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet))):=by
        rw [image_image,image_image,image_image]
      _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
        have hg:g.val.val.symm '' E.carrier=E.carrier:=E.image_eq g⁻¹
        rw [huInv,hq,hg,hvE]
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL M hM
  refine ⟨d,e,u,v,A,hu,hv,huD,hvE,hA,?_⟩
  rw [hA]
  change v.val (g.val.val.symm (q.val (u.val.symm ∞)))=∞
  rw [show u.val.symm ∞=p from (congrArg u.val.symm hup).symm.trans (u.val.symm_apply_apply p),←hgp,
    Equiv.symm_apply_apply,hvw]



/-- In any original chosen cusp chart, divergent actual height forces convergence in the unchanged all-cusp completion. Initial points may lie outside the chosen cusp. -/
theorem fuchsianCuspCompletionOld_tendsto_of_height {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (c:FuchsianCyclicConjugacyClasses D .parabolic) (g:H)
    (p:ℕ→D.domain.carrier) (z:ℕ→ℂ)
    (hcoord:∀n,(fuchsianCuspChartNormalization D c).normalizer.val (g.val.val.symm (p n).val)=
      (z n:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) (hz:Tendsto (fun n=>(z n).im) atTop atTop) :
    Tendsto (fun n=>fuchsianCuspCompletionOld D (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection
      D.domain (p n))) atTop
      (𝓝 (fuchsianCuspCompletionPoint D c)) := by
  let C:=fuchsianCuspChartNormalization D c
  let v:ℕ→_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspHalfPlane C.height:=fun n=>if hn:C.height<(z
    n).im then ⟨z n,hn⟩ else
    ⟨⟨0,C.height+1⟩,by change C.height<C.height+1;linarith⟩
  have hevent:∀ᶠn in atTop,(v n).val=z n:=by
    filter_upwards [hz.eventually_gt_atTop C.height] with n hn
    dsimp only [v]
    rw [dite_eq_left hn]
  have hvlim:Tendsto (fun n=>(v n).val.im) atTop atTop:=by
    apply hz.congr'
    filter_upwards [hevent] with n hn
    exact congrArg Complex.im hn.symm
  have hh:=(fuchsianCuspCompletedChart_continuous D c
    g).tendsto (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspCompletionInfinity C.height)
  have hlim:=hh.comp (stableCuspCompletion_height_tendsto C.height v hvlim)
  rw [fuchsianCuspCompletedChart_infty] at hlim
  apply hlim.congr'
  filter_upwards [hevent] with n hn
  apply fuchsianCuspCompletedChart_some D c g (v n) (p n) ?_
  rw [hn]
  exact hcoord n

theorem cuspNormalization_upper_chart_inverse_coordinates {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain
      H} {S:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset
      D} {p:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S
      p) (d:ℝ) (u:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hu:u=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
      (-(d:ℂ)*Complex.I)*C.normalizer) (z:ℍ) :
    C.normalizer.val (u.val.symm (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z))=
      (((z:ℂ)+(d:ℂ)*Complex.I:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  have hprod:C.normalizer*u⁻¹=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation ((d:ℂ)*Complex.I):=by
    rw [hu,mul_inv_rev,mul_inv_cancel_left,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_neg]
    congr 1
    ring
  have he:=congrArg (fun f:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup=>f.val
    (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)) hprod
  exact he.trans (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe _ (z:ℂ))

/-- One actual old quotient path approaches an original cusp and an actual conjugate cusp in their respective unchanged completions. -/
theorem fuchsianCuspCompletion_conjugacy_matching_path {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (c:FuchsianCyclicConjugacyClasses D .parabolic) :
    ∃b:FuchsianCyclicConjugacyClasses (D.nielsenConjugate q) .parabolic,∃p:ℕ→D.domain.carrier,
      Tendsto (fun n=>fuchsianCuspCompletionOld D
        (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain (p n))) atTop
        (𝓝 (fuchsianCuspCompletionPoint D c)) ∧
      Tendsto (fun n=>fuchsianCuspCompletionOld (D.nielsenConjugate q)
        (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection (D.nielsenConjugate q).domain
          (D.domain.conjugateHomeomorph q (p n)))) atTop
        (𝓝 (fuchsianCuspCompletionPoint (D.nielsenConjugate q) b)) := by
  let E:=D.nielsenConjugate q
  let C:=fuchsianCuspChartNormalization D c
  let a:=fuchsianParabolicPointRepresentative D c
  obtain ⟨b,g,hgp⟩:=fuchsianParabolicPointRepresentative_orbit_cover E
    (fuchsianCyclicPointConjugacyEquiv D .parabolic q a)
  let B:=fuchsianCuspChartNormalization E b
  obtain ⟨d,e,u,v,A,hu,hv,huD,_hvE,hA,hAi⟩:=
    cuspNormalization_conjugacy_native_comparison D E C B q rfl g hgp
  let z:ℕ→ℍ:=fun n=>⟨⟨0,(n:ℝ)+1⟩,by change 0<(n:ℝ)+1;positivity⟩
  have hz:Tendsto (fun n=>(z n).im) atTop atTop:=by
    change Tendsto (fun n:ℕ=>(n:ℝ)+1) atTop atTop
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have huInv:u.val.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=D.carrier:=by
    rw [←huD]
    exact u.val.symm_image_image D.carrier
  let p:ℕ→D.domain.carrier:=fun n=>⟨u.val.symm (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (z n)),by
    change u.val.symm (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (z n))∈D.carrier
    rw [←huInv]
    exact mem_image_of_mem _ (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_mem (z n))⟩
  refine ⟨b,p,?_,?_⟩
  · apply fuchsianCuspCompletionOld_tendsto_of_height D c 1 p
      (fun n=>(z n:ℂ)+(d:ℂ)*Complex.I)
    · intro n
      change C.normalizer.val (p n).val=_
      exact cuspNormalization_upper_chart_inverse_coordinates C d u hu (z n)
    · simpa using (tendsto_atTop_add_const_right _ d hz)
  · apply fuchsianCuspCompletionOld_tendsto_of_height E b g
      (fun n=>D.domain.conjugateHomeomorph q (p n))
      (fun n=>((A•z n:ℍ):ℂ)+(e:ℂ)*Complex.I)
    · intro n
      have he:=congrArg (fun f:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup=>f.val
        (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (z n))) hA
      have hval:v.val (g.val.val.symm (q.val (p
        n).val))=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (A•z n):=
        he.symm.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A (z n))
      have hpre:g.val.val.symm (q.val (p n).val)=v.val.symm (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (A•z n)):=by
        simpa only [Equiv.symm_apply_apply] using congrArg v.val.symm hval
      change B.normalizer.val (g.val.val.symm (q.val (p n).val))=_
      rw [hpre]
      exact cuspNormalization_upper_chart_inverse_coordinates B e v hv (A•z n)
    · simpa using (tendsto_atTop_add_const_right _ e (realSL_infinity_fixed_height_tendsto A hAi z hz))

end LowDimensionalTopology.Geometry.Fuchsian
