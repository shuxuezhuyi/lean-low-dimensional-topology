/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.FiniteAreaIdealBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FinitePolygonParabolicClasses
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletCenters
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Area
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeometricFuchsianModels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Complex.UnitDisc OnePoint Topology UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance finiteAreaBoundarySphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance finiteAreaBoundarySphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- An original finite-area convex fundamental polygon has finitely many literal complex ideal closure points. -/
theorem finite_area_polygon_idealBoundary_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    (fuchsianPolygonIdealBoundary P D).Finite := by
  have ho:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have ho' : IsOpen (P.finiteCoordinate '' D):=P.finiteCoordinate.isOpenMap D ho
  have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (P.finiteCoordinate '' D)≠⊤ := by
    rwa [←P.area_apply D ho.measurableSet]
  have hf:=hD.convex.complexIdealBoundary_finite ho' ha
  simpa only [fuchsianPolygonIdealBoundary,image_image,Function.comp_def] using hf

/-- The true circle-valued ideal boundary is finite; no finite-sidedness assumption is used. -/
theorem finite_area_polygon_idealCircle_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    (fuchsianPolygonIdealCircle P D).Finite :=
  (finite_area_polygon_idealBoundary_finite hD harea).preimage Subtype.val_injective.injOn

/-- A genuine positive-arc free side cannot occur on a finite-area convex fundamental polygon. -/
theorem finite_area_polygon_no_freeSide {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) (F : Set Circle) :
    ¬IsFuchsianFreeSide P D F := by
  rintro ⟨⟨u,_hu,rfl⟩,hpos⟩
  have hf:=(finite_area_polygon_idealCircle_finite hD harea).subset
    (connectedComponentIn_subset (fuchsianPolygonIdealCircle P D) u)
  exact hpos.ne' (hf.measure_zero _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure)

/-- The source's improper ideal vertices require a positive-arc free side and hence are absent at finite area. -/
theorem finite_area_polygon_no_improper_vertex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) (u : Circle) :
    ¬IsImproperFuchsianInfiniteVertex P D u := by
  rintro ⟨_hu,S,F,_hS,_huS,hF,_huF⟩
  exact finite_area_polygon_no_freeSide hD harea F hF

/-- Every actual infinite vertex of a finite-area convex fundamental polygon is proper. -/
theorem finite_area_polygon_infinite_vertex_iff_proper {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) (u : Circle) :
    IsFuchsianInfiniteVertex P D u↔IsProperFuchsianInfiniteVertex P D u := by
  exact or_iff_left (finite_area_polygon_no_improper_vertex hD harea u)

/-- Actual infinite vertices form a finite set, without a finite-edge hypothesis. -/
theorem finite_area_polygon_infinite_vertices_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    {u : Circle | IsFuchsianInfiniteVertex P D u}.Finite := by
  apply (finite_area_polygon_idealCircle_finite hD harea).subset
  intro u hu
  exact ((finite_area_polygon_infinite_vertex_iff_proper hD harea u).mp hu).1

/-- Finite genuine polygon area gives finitely many actual maximal parabolic cyclic subgroup conjugacy classes. No finite-generation or finite-sidedness premise is inserted. -/
theorem finite_area_polygon_parabolic_classes_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) := by
  let X:=fuchsianCyclicFixedPoints P.asFuchsianDisc .parabolic
  let V:=fuchsianPolygonIdealCircle P D
  let S : Set X:={p | p.val∈(fun u : Circle=>((u:ℂ):OnePoint ℂ)) '' V}
  have hV : V.Finite:=finite_area_polygon_idealCircle_finite hD harea
  have hS : S.Finite:=(hV.image (fun u : Circle=>((u:ℂ):OnePoint ℂ))).preimage
    Subtype.val_injective.injOn
  have hrep (p : X) : ∃g : H,g•p∈S := by
    obtain ⟨f,hfH,hf,hfix⟩:=p.property.2
    let F : H:=⟨f,hfH⟩
    obtain ⟨g,η,hgη,hη⟩:=hD.locallyFinite.parabolic_fixedPoint_orbit_mem_idealBoundary F hf p.val hfix
    let u : Circle:=⟨η,mem_sphere_zero_iff_norm.mpr ((mem_fuchsianPolygonIdealBoundary P D η).mp hη).2⟩
    refine ⟨g,u,hη,?_⟩
    exact hgη.symm
  have : Finite (MulAction.orbitRel.Quotient H X):=
    finite_orbitQuotient_of_finite_representatives S hS hrep
  exact Finite.of_equiv _ (fuchsianCyclicConjugacyClassesEquiv P.asFuchsianDisc .parabolic).symm

/-- A free Dirichlet centre exists for the original full action, by countability of its actual elliptic fixed points. -/
theorem finite_area_exists_dirichlet_center {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : ∃w : P.domain.carrier,IsDirichletCenter P w := by
  have : Uncountable ℍ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_isometry.injective.uncountable
  have : Uncountable P.domain.carrier:=P.halfPlaneCoordinate.symm.injective.uncountable
  by_contra hn
  push Not at hn
  have he : fuchsianEllipticPoints P=univ:=eq_univ_of_forall hn
  exact Set.not_countable_univ (he ▸ fuchsianEllipticPoints_countable P)

/-- Any genuine finite-area fundamental domain supplies finiteness of the actual parabolic class space; convexity, local finiteness, and a free centre are constructed rather than assumed. -/
theorem finite_area_fundamentalDomain_parabolic_classes_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (harea : P.area D≠⊤) :
    Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) := by
  obtain ⟨w,hw⟩:=finite_area_exists_dirichlet_center P
  have hpoly:=dirichletDomain_isConvexFuchsianPolygon P w hw
  have he:=fuchsianFundamentalDomain_area_eq hpoly.locallyFinite.fundamental hD
  have ha : P.area (dirichletDomain P w)≠⊤:=by rwa [he]
  exact finite_area_polygon_parabolic_classes_finite hpoly ha

/-- The existing whole original-model density area maps to the actual standard-disc density area. -/
theorem finite_area_geometricDisc_map_area {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) :
    Measure.map (geometricDiscHomeomorph D) (geometricModelArea D)=(geometricDiscData D).area := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (geometricDiscHomeomorph D).continuous.measurable hS,
    geometricModelArea_apply D _ (hS.preimage (geometricDiscHomeomorph D).continuous.measurable),
    image_preimage_eq _ (geometricDiscHomeomorph D).surjective,
    (geometricDiscData D).area_apply S hS]

/-- A genuine fundamental domain in the original arbitrary invariant disc transports to the actual full standard-disc group. -/
theorem finite_area_geometricDisc_fundamental_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (S : Set (fuchsianGeometricDomain D).carrier)
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) S) :
    IsFuchsianFundamentalDomain (geometricDiscData D) (geometricDiscHomeomorph D '' S) := by
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence (geometricDiscNormalizer D) H
  let F:=geometricDiscHomeomorph D
  have hb (g : geometricDiscGroup D) (x : (geometricDiscData D).domain.carrier) :
      F.symm (g•x)=e.symm g • F.symm x := by
    apply F.injective
    rw [geometricDiscHomeomorph_equivariant,e.apply_symm_apply,F.apply_symm_apply,F.apply_symm_apply]
  have hh:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e.symm F.symm hb hS
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain _ _ (Measure.map F
    (geometricModelArea D)) (F.symm ⁻¹' S) at hh
  rw [finite_area_geometricDisc_map_area] at hh
  have he : F.symm ⁻¹' S=F '' S:=(F.toEquiv.image_eq_preimage_symm S).symm
  rwa [he] at hh

/-- Actual original finite quotient area constructs a free normalized Dirichlet centre with the same finite actual area. -/
theorem finite_area_geometricDisc_dirichlet {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (S : Set (fuchsianGeometricDomain D).carrier)
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) S)
    (harea : geometricModelArea D S≠⊤) :
    ∃w : (geometricDiscData D).domain.carrier,IsDirichletCenter (geometricDiscData D) w ∧
      (geometricDiscData D).area (dirichletDomain (geometricDiscData D) w)≠⊤ := by
  obtain ⟨w,hw⟩:=finite_area_exists_dirichlet_center (geometricDiscData D)
  refine ⟨w,hw,?_⟩
  have he:=fuchsianFundamentalDomain_area_eq (dirichletDomain_fundamental _ w hw)
    (finite_area_geometricDisc_fundamental_image D S hS)
  rw [he,(geometricDiscData D).area_apply _
    ((geometricDiscHomeomorph D).measurableEmbedding.measurableSet_image.mpr hS.isOpen.measurableSet),
    ←geometricModelArea_apply D S hS.isOpen.measurableSet]
  exact harea

/-- Finite genuine quotient area in the original arbitrary Fuchsian disc forces finitely many actual maximal parabolic cyclic subgroup conjugacy classes. All normalizers, free centres, convex polygons and representatives are constructed. -/
theorem finite_area_parabolic_classes_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (S : Set (fuchsianGeometricDomain D).carrier)
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) S)
    (harea : geometricModelArea D S≠⊤) :
    Finite (FuchsianCyclicConjugacyClasses D .parabolic) := by
  obtain ⟨w,hw,hareaW⟩:=finite_area_geometricDisc_dirichlet D S hS harea
  let P:=geometricDiscData D
  let q:=geometricDiscNormalizer D
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have hpoly:=dirichletDomain_isConvexFuchsianPolygon P w hw
  let X:=fuchsianCyclicFixedPoints D .parabolic
  let V:=fuchsianPolygonIdealCircle P (dirichletDomain P w)
  let R : Set X:={p | q.val p.val∈(fun u : Circle=>((u:ℂ):OnePoint ℂ)) '' V}
  have hV : V.Finite:=finite_area_polygon_idealCircle_finite hpoly hareaW
  have hR : R.Finite:=(hV.image (fun u : Circle=>((u:ℂ):OnePoint ℂ))).preimage
    (q.val.injective.comp Subtype.val_injective).injOn
  have hrep (p : X) : ∃g : H,g•p∈R := by
    obtain ⟨f,hfH,hf,hfix⟩:=p.property.2
    let F:=e ⟨f,hfH⟩
    have hf' : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic F.val:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
    have hfix' : F.val.val (q.val p.val)=q.val p.val := by
      change (q*f*q⁻¹).val (q.val p.val)=q.val p.val
      rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobius_conjugate_boundary_fixed_iff,q.val.symm_apply_apply]
      exact hfix
    obtain ⟨g,η,hgη,hη⟩:=hpoly.locallyFinite.parabolic_fixedPoint_orbit_mem_idealBoundary F hf' _ hfix'
    let u : Circle:=⟨η,mem_sphere_zero_iff_norm.mpr ((mem_fuchsianPolygonIdealBoundary _ _ _).mp hη).2⟩
    have hgEq : g.val=q*(e.symm g).val*q⁻¹:=
      (congrArg Subtype.val (e.apply_symm_apply g)).symm
    have hc : q.val ((e.symm g).val.val p.val)=((η:ℂ):OnePoint ℂ) := by
      calc
        q.val ((e.symm g).val.val p.val)=
            (q*(e.symm g).val*q⁻¹).val (q.val p.val) := by
          change q•((e.symm g).val•p.val)=(q*(e.symm g).val*q⁻¹)•(q•p.val)
          simp only [mul_smul,inv_smul_smul]
        _=((η:ℂ):OnePoint ℂ) := by rw [←hgEq];exact hgη
    exact ⟨e.symm g,u,hη,hc.symm⟩
  have : Finite (MulAction.orbitRel.Quotient H X):=
    finite_orbitQuotient_of_finite_representatives R hR hrep
  exact Finite.of_equiv _ (fuchsianCyclicConjugacyClassesEquiv D .parabolic).symm

end LowDimensionalTopology.Geometry.Fuchsian
