/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.ParabolicAreaInfinity
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.ParabolicSideNormalizers
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped UpperHalfPlane OnePoint MatrixGroups Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance parabolicFiniteSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance parabolicFiniteSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- The actual full invariant-half-plane group conjugates with its genuine original disc data. -/
theorem parabolic_conjugate_halfPlaneData {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  let D:=P.asFuchsianDisc.nielsenConjugate q
  have he : D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    change q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    exact hq
  refine ⟨?_,D.discrete⟩
  intro g
  have hh:=D.image_eq g
  rwa [he] at hh

/-- Every original real determinant-one change of coordinates preserves genuine hyperbolic area. -/
theorem parabolic_realSL_map_volume (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Measure.map (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) (volume : Measure ℍ)=volume := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B).continuous.measurable hS]
  exact SMulInvariantMeasure.measure_preimage_smul (Matrix.SpecialLinearGroup.mapGL ℝ B) hS

/-- Native and original conjugate actions commute under the actual real matrix coordinate. -/
theorem parabolic_realSL_action_equivariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (Q : HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) H))
    (g : H) (z : ℍ) :
    letI:=P.nativeAction
    letI:=Q.nativeAction
    B•(g•z)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) H g • (B•z) := by
  let parabolicOriginalAction:=P.nativeAction
  let parabolicConjugateAction:=Q.nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  have hf (w : ℍ) : _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (B•w)=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        B).val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint
        w):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action B w).symm
  rw [hf,←P.nativeAction_boundary,←Q.nativeAction_boundary,hf]
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) • (g.val •
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B*g.val*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B)⁻¹) • ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) •
      _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)
  simp only [mul_smul,inv_smul_smul]

/-- Genuine real matrix changes of coordinates transport the full original fundamental-domain conditions and density area. -/
theorem parabolic_realSL_fundamental_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (Q : HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) H))
    (D : Set ℍ) :
    letI:=P.nativeAction
    letI:=Q.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume D →
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) H) ℍ volume ((B•·) '' D) := by
  let parabolicOriginalAction:=P.nativeAction
  let parabolicConjugateAction:=Q.nativeAction
  intro hD
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) H
  let f:ℍ≃ₜℍ:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B).toHomeomorph
  have he (g : H) (z : ℍ) : f (g•z)=e g • f z :=
    parabolic_realSL_action_equivariant P B Q g z
  have hb (g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) H) (z : ℍ) :
      f.symm (g•z)=e.symm g • f.symm z := by
    apply f.injective
    rw [he,e.apply_symm_apply,f.apply_symm_apply,f.apply_symm_apply]
  have hh:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e.symm f.symm hb hD
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain _ ℍ (Measure.map f
    volume) (f.symm ⁻¹' D) at hh
  have hm : Measure.map f (volume : Measure ℍ)=volume:=parabolic_realSL_map_volume B
  rw [hm] at hh
  have hs : f.symm ⁻¹' D=((B•·) '' D) := by
    exact f.toEquiv.image_eq_preimage_symm D |>.symm
  rwa [hs] at hh

/-- Every true fundamental domain of an elementary invariant-half-plane group with an arbitrary actual parabolic has infinite density area. -/
theorem elementary_parabolic_halfPlane_area_top (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈H) (hpar :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) (D : Set ℍ) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume D → volume D=⊤ := by
  let parabolicOriginalAction:=P.nativeAction
  intro hD
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL f (P.preserves ⟨f,hf⟩)
  have hparA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=hA.symm ▸ hpar
  obtain ⟨q,hq,hunit⟩:=realSL_parabolic_unit_normalizer A hparA
  obtain ⟨B,hB⟩:=mobius_preserves_halfPlane_exists_SL q hq
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) H
  let Q:=parabolic_conjugate_halfPlaneData P (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    B) (realSLMobius_image_openHalfPlane B)
  have hElem : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary K := (_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_finiteOrbit_conjugation H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)).mpr hH
  have hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*f*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)⁻¹∈K :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ H
      _).mpr ⟨f,hf,rfl⟩
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈K := by
    rw [←hB,hA] at hunit
    rcases hunit with he|he
    · exact he ▸ hmem
    · have hh : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹∈K:=he ▸ hmem
      simpa only [inv_inv] using K.inv_mem hh
  have hFD:=parabolic_realSL_fundamental_image P B Q D hD
  have hv:=elementary_unitTranslation_fundamental_area_top K Q hElem hT ((B•·) '' D) hFD
  have he:=measure_smul (volume : Measure ℍ) (Matrix.SpecialLinearGroup.mapGL ℝ B) D
  change volume ((B•·) '' D)=volume D at he
  rwa [he] at hv

/-- Genuine finite quotient area and an actual parabolic force a half-plane Fuchsian group to be non-elementary. -/
theorem parabolic_halfPlane_finite_area_nonElementary (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈H)
    (hpar : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) (D : Set ℍ) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume D → volume D≠⊤ → _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H := by
  let parabolicOriginalAction:=P.nativeAction
  intro hD hfinite he
  exact hfinite (elementary_parabolic_halfPlane_area_top H P he f hf hpar D hD)

/-- A proved whole-disc half-plane chart constructs the actual full conjugate Fuchsian group. -/
theorem parabolic_disc_halfPlaneData {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D
  : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  let E:=D.nielsenConjugate q
  have he : E.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=hq
  refine ⟨?_,E.discrete⟩
  intro g
  have hh:=E.image_eq g
  rwa [he] at hh

/-- The actual original whole-domain chart intertwines the full native and original group actions. -/
theorem parabolic_disc_chart_equivariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (Q : HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
      q H))
    (g : H) (x : (fuchsianGeometricDomain D).carrier) :
    letI:=Q.nativeAction
    geometricHalfPlaneChart D q hq (g•x)=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g • geometricHalfPlaneChart D q hq x := by
  let parabolicConjugateAction:=Q.nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  have hf (y : (fuchsianGeometricDomain D).carrier) :
      _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (geometricHalfPlaneChart D q hq
        y)=q.val y.val :=
    geometricHalfPlaneChart_extended D q hq y
  rw [hf,←Q.nativeAction_boundary,hf]
  change q • (g.val • x.val)=(q*g.val*q⁻¹) • (q • x.val)
  simp only [mul_smul,inv_smul_smul]

/-- The original density area is the actual half-plane volume under any proved full-model chart. -/
theorem parabolic_disc_chart_map_area {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D
  : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    Measure.map (geometricHalfPlaneChart D q hq) (geometricModelArea D)=(volume : Measure ℍ) := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (geometricHalfPlaneChart D q hq).continuous.measurable hS,
    geometricModelArea_eq_halfPlaneChart D q hq _
      (hS.preimage (geometricHalfPlaneChart D q hq).continuous.measurable),
    Set.image_preimage_eq _ (geometricHalfPlaneChart D q hq).surjective]

/-- All original fundamental-domain data transports through the proved actual whole-disc half-plane chart. -/
theorem parabolic_disc_chart_fundamental_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (Q : HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
      q H))
    (S : Set (fuchsianGeometricDomain D).carrier) :
    letI:=Q.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) S →
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) ℍ volume (geometricHalfPlaneChart D q hq '' S) := by
  let parabolicConjugateAction:=Q.nativeAction
  intro hS
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  let f:=geometricHalfPlaneChart D q hq
  have he (g : H) (x : (fuchsianGeometricDomain D).carrier) : f (g•x)=e g • f x :=
    parabolic_disc_chart_equivariant D q hq Q g x
  have hb (g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (z : ℍ) : f.symm (g•z)=e.symm g • f.symm z := by
    apply f.injective
    rw [he,e.apply_symm_apply,f.apply_symm_apply,f.apply_symm_apply]
  have hh:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e.symm f.symm hb hS
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain _ ℍ (Measure.map f
    (geometricModelArea D)) (f.symm ⁻¹' S) at hh
  rw [parabolic_disc_chart_map_area D q hq] at hh
  have hs : f.symm ⁻¹' S=f '' S:=(f.toEquiv.image_eq_preimage_symm S).symm
  rwa [hs] at hh

/-- Every actual fundamental domain of an original elementary Fuchsian group with a genuine parabolic has infinite genuine density area. -/
theorem elementary_parabolic_fundamental_area_top {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) (f :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f∈H) (hpar : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) (S : Set
      (fuchsianGeometricDomain D).carrier)
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) S) :
    geometricModelArea D S=⊤ := by
  let q:=D.halfPlaneNormalizer
  have hq : q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=D.halfPlaneNormalizer_image
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  let Q:=parabolic_disc_halfPlaneData D q hq
  have he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary K:=(_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_finiteOrbit_conjugation H q).mpr hH
  have hfK : q*f*q⁻¹∈K:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
    q H _).mpr ⟨f,hf,rfl⟩
  have hpK : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (q*f*q⁻¹) :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hpar
  have hFD:=parabolic_disc_chart_fundamental_image D q hq Q S hS
  have hv:=elementary_parabolic_halfPlane_area_top K Q he _ hfK hpK _ hFD
  rw [geometricModelArea_eq_halfPlaneChart D q hq S hS.isOpen.measurableSet]
  exact hv

/-- In the original arbitrary Fuchsian disc, finite actual quotient area and a genuine parabolic force non-elementarity. -/
theorem parabolic_finite_area_nonElementary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈H) (hpar :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (S : Set (fuchsianGeometricDomain D).carrier)
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) S)
    (hfinite : geometricModelArea D S≠⊤) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H :=
  fun he=>hfinite (elementary_parabolic_fundamental_area_top D he f hf hpar S hS)

end LowDimensionalTopology.Geometry.Fuchsian
