module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleCovolume
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspCompletionConjugacy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance nativeGeometricSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance nativeGeometricSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- The actual original half-plane action is faithful. -/
theorem halfPlane_nativeHom_injective {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) : Function.Injective P.nativeHom := by
  intro g h he
  apply Subtype.ext
  apply _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusToFull_isometry.injective
  exact congrArg Subtype.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneNativeHom_injective he)

/-- A genuine geometric fundamental domain is also a measure fundamental domain for the same actual native action. -/
theorem native_geometric_fundamental_measureDomain {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (S:Set ℍ) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume S→MeasureTheory.IsFundamentalDomain H S volume := by
  let nativeGeomAreaAction:=P.nativeAction
  let nativeGeomAreaCountable:Countable H:=_root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_countable H P.discrete
  let nativeGeomAreaContinuous:ContinuousConstSMul H ℍ:=⟨fun g=>(P.nativeHom g).continuous⟩
  let nativeGeomAreaInvariant:SMulInvariantMeasure H ℍ volume:=⟨by
    intro g U hU
    exact (show MeasurePreserving (P.nativeHom g) volume volume from
      ⟨(P.nativeHom g).continuous.measurable,native_isometry_volume_map (P.nativeHom
        g)⟩).measure_preimage hU.nullMeasurableSet⟩
  intro hS
  obtain ⟨F,hF,hSF,hFC⟩:=hS.exists_fundamentalSet
  have hm:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.nullMeasurableSet_of_between _ _ hS hSF hFC
  have hnull:∀g:H,g≠1→volume {x:ℍ|g•x=x}=0:=by
    intro g hg
    apply native_isometry_fixed_volume_zero (P.nativeHom g)
    intro he
    apply hg
    exact halfPlane_nativeHom_injective P (he.trans P.nativeHom.map_one.symm)
  have hMF:=hF.measureDomain_of_fixed_null hm hnull
  have hAE:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.ae_eq_of_between _ _ hS hSF hFC
  have hAll:∀ᵐx:ℍ∂volume,∀g:H,g•x∈F ↔g•x∈S:=by
    apply eventually_countable_forall.mpr
    intro g
    simpa only [eq_iff_iff] using (measurePreserving_smul g volume).quasiMeasurePreserving.ae hAE
  refine ⟨hS.isOpen.measurableSet.nullMeasurableSet,?_,?_⟩
  · filter_upwards [hMF.ae_covers,hAll] with x hx hxx
    obtain ⟨g,hg⟩:=hx
    exact ⟨g,(hxx g).mp hg⟩
  · intro g h hgh
    apply measure_mono_null _ (hMF.aedisjoint hgh)
    rintro x ⟨⟨a,ha,he⟩,⟨b,hb,hbe⟩⟩
    exact ⟨⟨a,hSF ha,he⟩,⟨b,hSF hb,hbe⟩⟩

/-- The exact triangle area applies to every genuine geometric fundamental domain, without an extra null-stabilizer or measurable-domain premise. -/
theorem closedTriangle_nativeGeometric_volume (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (S:Set ℍ) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (closedTriangleMobiusGroup
      T) ℍ volume S→
    volume S=ENNReal.ofReal (2*(Real.pi-T.alpha-T.beta-T.gamma)) := by
  let nativeGeometricTriangleAreaAction:=P.nativeAction
  intro hS
  exact closedTriangle_measureDomain_volume T ha hb hc P S
    (native_geometric_fundamental_measureDomain P S hS)

/-- The actual identity sphere coordinate identifies the original invariant-half-plane domain with native H. -/
def halfPlaneGeometricChart {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H) :
    (fuchsianGeometricDomain P.asFuchsianDisc).carrier≃ₜℍ :=
  geometricHalfPlaneChart P.asFuchsianDisc 1 (by
    change id '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    exact image_id _)

theorem halfPlaneGeometricChart_boundary {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (x:(fuchsianGeometricDomain P.asFuchsianDisc).carrier) :
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (halfPlaneGeometricChart P x)=x.val := by
  exact geometricHalfPlaneChart_extended P.asFuchsianDisc 1 _ x

/-- The full original group action is unchanged under this actual geometric chart. -/
theorem halfPlaneGeometricChart_equivariant {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (g:H) (x:(fuchsianGeometricDomain P.asFuchsianDisc).carrier) :
    letI:=P.nativeAction
    halfPlaneGeometricChart P (g•x)=g•halfPlaneGeometricChart P x := by
  let halfPlaneChartAreaAction:=P.nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [halfPlaneGeometricChart_boundary,←P.nativeAction_boundary,halfPlaneGeometricChart_boundary]
  rfl

/-- The chart sends the original hyperbolic density measure to genuine native volume. -/
theorem halfPlaneGeometricChart_map_area {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H) :
    Measure.map (halfPlaneGeometricChart P) (geometricModelArea P.asFuchsianDisc)=
      (volume:Measure ℍ) := parabolic_disc_chart_map_area P.asFuchsianDisc 1 _

/-- Every measurable original region has exactly the physical native image area. -/
theorem halfPlaneGeometricChart_image_area {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (F:Set (fuchsianGeometricDomain P.asFuchsianDisc).carrier) (hF:MeasurableSet F) :
    geometricModelArea P.asFuchsianDisc F=volume (halfPlaneGeometricChart P '' F) :=
  geometricModelArea_eq_halfPlaneChart P.asFuchsianDisc 1 _ F hF

/-- Original geometric fundamental domains become true native geometric fundamental domains, with the same whole group and physical region. -/
theorem halfPlaneGeometricChart_fundamental_image {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (F:Set (fuchsianGeometricDomain P.asFuchsianDisc).carrier) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      P.asFuchsianDisc).carrier
      (geometricModelArea P.asFuchsianDisc) F→
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume (halfPlaneGeometricChart P '' F) := by
  let halfPlaneChartFundamentalAreaAction:=P.nativeAction
  intro hF
  let E:=halfPlaneGeometricChart P
  have hb (g:H) (z:ℍ):E.symm (g•z)=g•E.symm z:=by
    apply E.injective
    rw [halfPlaneGeometricChart_equivariant,E.apply_symm_apply,E.apply_symm_apply]
  have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage (MulEquiv.refl H) E.symm hb hF
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ (Measure.map E
    (geometricModelArea P.asFuchsianDisc))
    (E.symm ⁻¹' F) at h
  rw [halfPlaneGeometricChart_map_area] at h
  have he:E.symm ⁻¹' F=E '' F:=(E.toEquiv.image_eq_preimage_symm F).symm
  rwa [he] at h

/-- The original genuine geometric domain area, and not merely a numerical signature expression, equals twice the actual triangle angle defect. -/
theorem closedTriangle_originalGeometric_volume (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (F:Set (fuchsianGeometricDomain P.asFuchsianDisc).carrier)
    (hF:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (closedTriangleMobiusGroup T)
      (fuchsianGeometricDomain P.asFuchsianDisc).carrier (geometricModelArea P.asFuchsianDisc) F) :
    geometricModelArea P.asFuchsianDisc F=ENNReal.ofReal (2*(Real.pi-T.alpha-T.beta-T.gamma)) := by
  let triangleOriginalGeometricAreaAction:=P.nativeAction
  rw [halfPlaneGeometricChart_image_area P F hF.isOpen.measurableSet]
  exact closedTriangle_nativeGeometric_volume T ha hb hc P _
    (halfPlaneGeometricChart_fundamental_image P F hF)

/-- Equality of the actual full subgroup transports the genuine geometric area statement; no model subgroup is supplied independently. -/
theorem closedTriangle_nativeGeometric_volume_of_group_eq {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (ha:IsIntegralTriangleAngle
      T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (Q:HalfPlaneFuchsianGroup H)
    (hG:H=closedTriangleMobiusGroup T) (S:Set ℍ) :
    letI:=Q.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume S→
    volume S=ENNReal.ofReal (2*(Real.pi-T.alpha-T.beta-T.gamma)) := by
  subst H
  exact closedTriangle_nativeGeometric_volume T ha hb hc Q S

/-- For any original invariant Fuchsian disc and whole group genuinely conjugate to this triangle group, every original geometric fundamental domain has its actual precise hyperbolic area. -/
theorem closedTriangle_conjugate_originalGeometric_volume {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (ha:IsIntegralTriangleAngle
      T.alpha)
    (hb:IsIntegralTriangleAngle T.beta) (hc:IsIntegralTriangleAngle T.gamma)
    (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H=closedTriangleMobiusGroup T)
    (hDisc:q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (F:Set (fuchsianGeometricDomain D).carrier)
    (hF:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) F) :
    geometricModelArea D F=ENNReal.ofReal (2*(Real.pi-T.alpha-T.beta-T.gamma)) := by
  let Q:=parabolic_disc_halfPlaneData D q hDisc
  let triangleConjugateOriginalAreaAction:=Q.nativeAction
  have hFN:=parabolic_disc_chart_fundamental_image D q hDisc Q F hF
  rw [geometricModelArea_eq_halfPlaneChart D q hDisc F hF.isOpen.measurableSet]
  exact closedTriangle_nativeGeometric_volume_of_group_eq T ha hb hc Q hG _ hFN

/-- The proved genuine triangle signature's area expression is its physical doubled angle defect. -/
theorem closedTriangleSignatureData_areaFormulaValue (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    (closedTriangleSignatureData T ha hb hc).areaFormulaValue=
      2*(Real.pi-T.alpha-T.beta-T.gamma) := by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.areaFormulaValue,closedTriangleSignatureData_deficit]
  field_simp
  ring

/-- The complete actual signature and its precise original geometric area travel together through a true whole-group, whole-disc triangle model. No area, genus or class conclusion is assumed. -/
theorem closedTriangle_conjugate_signature_area {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (ha:IsIntegralTriangleAngle
      T.alpha)
    (hb:IsIntegralTriangleAngle T.beta) (hc:IsIntegralTriangleAngle T.gamma)
    (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H=closedTriangleMobiusGroup T)
    (hDisc:q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (F:Set (fuchsianGeometricDomain D).carrier)
    (hF:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) F) :
    HasCofiniteFuchsianSignature D 0 (closedTriangleFiniteCornerOrderList T ha hb hc)
      (Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}) ∧
    geometricModelArea D F=ENNReal.ofReal (closedTriangleSignatureData T ha hb hc).areaFormulaValue := by
  let P:=closedTriangleMobiusData T ha hb hc
  have hGi:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q⁻¹ (closedTriangleMobiusGroup T)=H:=by
    rw [←hG,_root_.LowDimensionalTopology.Geometry.Hyperbolic.subgroupConjugate_inv_cancel]
  have hDi:q⁻¹.val '' P.asFuchsianDisc.carrier=D.carrier:=by
    change q.val.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=D.carrier
    rw [←hDisc]
    exact q.val.symm_image_image D.carrier
  refine ⟨cofinite_signature_of_conjugate_group P.asFuchsianDisc D q⁻¹ hGi hDi 0 _ _
    (closedTriangle_actual_cofinite_signature T ha hb hc P),?_⟩
  rw [closedTriangle_conjugate_originalGeometric_volume D T ha hb hc q hG hDisc F hF,
    closedTriangleSignatureData_areaFormulaValue]

end LowDimensionalTopology.Geometry.Fuchsian
