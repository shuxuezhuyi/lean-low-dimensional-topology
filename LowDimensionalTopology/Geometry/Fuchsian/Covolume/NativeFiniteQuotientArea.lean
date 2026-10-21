module
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.TriangleCovolume
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleMobiusQuotients
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaEllipticClasses
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.ParabolicFiniteArea
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaCuspCompactness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory Function
open scoped UpperHalfPlane OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance nativeFiniteQuotientSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance nativeFiniteQuotientSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- Finite actual native covolume supplies a genuine original geometric fundamental domain of finite density area. -/
theorem native_finite_measureDomain_geometric_domain {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (S:Set ℍ) :
    letI:=P.nativeAction
    MeasureTheory.IsFundamentalDomain H S volume→volume S≠⊤→
    ∃F:Set (fuchsianGeometricDomain P.asFuchsianDisc).carrier,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
        P.asFuchsianDisc).carrier
        (geometricModelArea P.asFuchsianDisc) F ∧geometricModelArea P.asFuchsianDisc F≠⊤ := by
  let nativeFiniteAreaAction:=P.nativeAction
  intro hS haS
  let D:=P.asFuchsianDisc
  let Q:=geometricDiscData D
  let q:=geometricDiscNormalizer D
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  let f:=geometricDiscHomeomorph D
  obtain ⟨w,hw⟩:=finite_area_exists_dirichlet_center Q
  let V:=dirichletDomain Q w
  have hV:IsFuchsianFundamentalDomain Q V:=dirichletDomain_fundamental Q w hw
  have hf (g:H) (x:(fuchsianGeometricDomain D).carrier) : f (g•x)=e g•f x :=
    geometricDiscHomeomorph_equivariant D g x
  have hμ:Measure.map f.symm Q.area=geometricModelArea D:=by
    rw [←finite_area_geometricDisc_map_area D,Measure.map_map f.symm.continuous.measurable f.continuous.measurable]
    rw [show f.symm ∘ f=id from funext f.symm_apply_apply,Measure.map_id]
  let F:=f ⁻¹' V
  have hF:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D).carrier (geometricModelArea D) F:=by
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e f hf hV
    rwa [hμ] at h
  have h1:(1:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup).val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    change id '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    exact image_id _
  let E:=geometricHalfPlaneChart D 1 h1
  have hE (x:(fuchsianGeometricDomain
    D).carrier) :_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (E x)=x.val:=
    geometricHalfPlaneChart_extended D 1 h1 x
  have hEg (g:H) (z:ℍ):E.symm (g•z)=g•E.symm z:=by
    apply Subtype.ext
    have hz:_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z=(E.symm z).val:=by
      have h:=hE (E.symm z)
      rwa [E.apply_symm_apply] at h
    have hgz:_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (g•z)=(E.symm (g•z)).val:=by
      have h:=hE (E.symm (g•z))
      rwa [E.apply_symm_apply] at h
    change (E.symm (g•z)).val=g.val.val (E.symm z).val
    rw [←hgz,←hz]
    exact (P.nativeAction_boundary g z).symm
  let U:=E '' F
  have hUo:IsOpen U:=E.isOpenMap F hF.isOpen
  have hpack:Pairwise (Disjoint on fun g:H=>g•U):=by
    intro g h hne
    apply disjoint_left.mpr
    rintro x ⟨a,ha,rfl⟩ ⟨b,hb,heq⟩
    obtain ⟨a',ha',rfl⟩:=ha
    obtain ⟨b',hb',rfl⟩:=hb
    have hne':e (g⁻¹*h)≠1:=by
      intro he
      have hm:g⁻¹*h=1:=e.injective (he.trans e.map_one.symm)
      exact hne (inv_mul_eq_one.mp hm)
    have hgEq:(g⁻¹*h)•b'=a':=by
      have hh:=congrArg E.symm heq
      rw [hEg,hEg,E.symm_apply_apply,E.symm_apply_apply] at hh
      have ht:=congrArg (fun x:(fuchsianGeometricDomain D).carrier=>g⁻¹•x) hh
      simpa only [mul_smul,inv_smul_smul] using ht
    have hi:e (g⁻¹*h)•f b'=f a':=by rw [←hf,hgEq]
    exact (disjoint_left.mp (hV.disjoint_image hne'))
      ⟨f b',hb',hi⟩ ha'
  have hbound:volume U≤volume S:=native_aeFundamental_packing_volume_le P hS
    hUo.measurableSet.nullMeasurableSet hpack
  refine ⟨F,hF,?_⟩
  rw [geometricModelArea_eq_halfPlaneChart D 1 h1 F hF.isOpen.measurableSet]
  exact ne_top_of_le_ne_top haS hbound


/-- Native finite measurable covolume gives finiteness of both actual maximal cyclic class spaces. -/
theorem native_finite_measureDomain_cyclic_classes_finite {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (S:Set ℍ) :
    letI:=P.nativeAction
    MeasureTheory.IsFundamentalDomain H S volume→volume S≠⊤→
    ∀kind,Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc kind) := by
  let nativeFiniteClassesAction:=P.nativeAction
  intro hS ha kind
  obtain ⟨F,hF,harea⟩:=native_finite_measureDomain_geometric_domain P S hS ha
  exact finite_area_cyclic_classes_finite P.asFuchsianDisc F hF harea kind

/-- The whole original triangle group has a genuine finite-area geometric fundamental domain. -/
theorem closedTriangle_geometric_finite_domain (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    ∃F:Set (fuchsianGeometricDomain P.asFuchsianDisc).carrier,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (closedTriangleMobiusGroup T)
        (fuchsianGeometricDomain P.asFuchsianDisc).carrier (geometricModelArea P.asFuchsianDisc) F ∧
        geometricModelArea P.asFuchsianDisc F≠⊤ := by
  let nativeTriangleFiniteAreaAction:=P.nativeAction
  obtain ⟨S,hS,harea⟩:=triangleConformalMobius_finite_measureDomain T ha hb hc P
  exact native_finite_measureDomain_geometric_domain P S hS harea

/-- Finite actual triangle covolume proves finiteness of the original elliptic and parabolic class spaces. -/
theorem closedTriangle_cyclic_classes_finite (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (kind:FuchsianCyclicKind) : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc kind) := by
  obtain ⟨F,hF,harea⟩:=closedTriangle_geometric_finite_domain T ha hb hc P
  exact finite_area_cyclic_classes_finite P.asFuchsianDisc F hF harea kind

/-- The unique original all-cusp completion of a genuine integral triangle group is actually compact. -/
theorem closedTriangle_cusp_completion_compact (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    CompactSpace (FuchsianCuspCompletion P.asFuchsianDisc) := by
  obtain ⟨F,hF,harea⟩:=closedTriangle_geometric_finite_domain T ha hb hc P
  exact finite_area_fuchsianCuspCompletion_compact P.asFuchsianDisc F hF harea

end LowDimensionalTopology.Geometry.Fuchsian
