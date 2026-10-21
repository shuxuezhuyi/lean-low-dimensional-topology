/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaVertexCycles
public import LowDimensionalTopology.Geometry.Fuchsian.GeometricFiniteness.FiniteSidedGeneration
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Complex.UnitDisc Topology UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance finiteSidesSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance finiteSidesSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- A genuine least point of a real set is a genuine extreme point. -/
theorem real_isLeast_mem_extreme {A : Set ℝ} {m : ℝ} (hm : IsLeast A m) :
    m∈A.extremePoints ℝ := by
  refine ⟨hm.1,?_⟩
  intro y hy z hz hseg
  obtain ⟨a,b,ha,hb,hab,he⟩:=hseg
  have hyb:=hm.2 hy
  have hzb:=hm.2 hz
  change a*y+b*z=m at he
  have hmul:=mul_nonneg hb.le (sub_nonneg.mpr hzb)
  have hbal : a*m+b*m=m:=by nlinarith [congrArg (fun t : ℝ=>t*m) hab]
  apply le_antisymm ?_ hyb
  by_contra hn
  have hstrict:=mul_pos ha (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith

/-- A genuine greatest point of a real set is a genuine extreme point. -/
theorem real_isGreatest_mem_extreme {A : Set ℝ} {m : ℝ} (hm : IsGreatest A m) :
    m∈A.extremePoints ℝ := by
  refine ⟨hm.1,?_⟩
  intro y hy z hz hseg
  obtain ⟨a,b,ha,hb,hab,he⟩:=hseg
  have hyb:=hm.2 hy
  have hzb:=hm.2 hz
  change a*y+b*z=m at he
  have hmul:=mul_nonneg hb.le (sub_nonneg.mpr hzb)
  have hbal : a*m+b*m=m:=by nlinarith [congrArg (fun t : ℝ=>t*m) hab]
  apply le_antisymm hyb
  by_contra hn
  have hstrict:=mul_pos ha (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith

/-- Every nonempty proper closed convex subset of the real parameter line has a genuine extreme point. -/
theorem closed_convex_real_extreme_nonempty {A : Set ℝ} (hc : IsClosed A)
    (hconv : Convex ℝ A) (hn : A.Nonempty) (hproper : A≠univ) :
    (A.extremePoints ℝ).Nonempty := by
  have hnall : ¬∀t : ℝ,t∈A:=by intro h;exact hproper (eq_univ_of_forall h)
  obtain ⟨t,ht⟩:=not_forall.mp hnall
  obtain ⟨a,ha⟩:=hn
  have hne : a≠t:=by intro he;exact ht (he ▸ ha)
  rcases lt_or_gt_of_ne hne with hat | hta
  · have hbound : BddAbove A:=by
      refine ⟨t,?_⟩
      intro b hb
      by_contra hnb
      have htb : t<b:=lt_of_not_ge hnb
      exact ht ((convex_iff_ordConnected.mp hconv).out ha hb ⟨hat.le,htb.le⟩)
    exact ⟨sSup A,real_isGreatest_mem_extreme (hc.isGreatest_csSup ⟨a,ha⟩ hbound)⟩
  · have hbound : BddBelow A:=by
      refine ⟨t,?_⟩
      intro b hb
      by_contra hnb
      have hbt : b<t:=lt_of_not_ge hnb
      exact ht ((convex_iff_ordConnected.mp hconv).out hb ha ⟨hbt.le,hta.le⟩)
    exact ⟨sInf A,real_isLeast_mem_extreme (hc.isLeast_csInf ⟨a,ha⟩ hbound)⟩

/-- Removing a true nonvertex point from its actual side destroys geodesic convexity. -/
theorem polygon_side_remove_nonvertex_not_convex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D S : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hS : IsFuchsianPolygonSide P D S)
    {x : P.domain.carrier} (hxS : x∈S) (hnv : ¬IsFuchsianPolygonVertex P D x) :
    ¬_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' (S\{x})) := by
  intro hrem
  have hxfront:=hS.subset_frontier hD.locallyFinite.fundamental hxS
  obtain ⟨T,hT,a,ha,b,hb,hab,hxab⟩:=hD.nonvertex_is_side_interior hxfront hnv
  let F:=normalizedPolygonKleinCoordinate P x
  have hFinj : Function.Injective F:=(normalizedPolygonKleinCoordinate_isOpenEmbedding P x).injective
  have hxT : x∈T:=by
    have hm:=(hT.normalizedKlein_convex x).segment_subset ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
      (openSegment_subset_segment ℝ _ _ hxab)
    obtain ⟨y,hy,he⟩:=hm
    exact hFinj he ▸ hy
  have hST : S=T:=by
    by_contra hne
    exact hnv (hD.distinct_sides_meet_vertex hS hT hne ⟨hxS,hxT⟩)
  have hnormal : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (polygonPointCoordinate P x '' (S\{x})):=by
    have he : polygonPointCoordinate P x '' (S\{x})=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate x) '' (P.finiteCoordinate '' (S\{x})):=by
      rw [image_image]
      rfl
    rw [he]
    exact hrem.isometry_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry _)
  have hconv : Convex ℝ (F '' (S\{x})):=by
    have he : F '' (S\{x})=_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' (S\{x})):=by
      rw [image_image]
      rfl
    rw [he]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp hnormal
  have hax : a≠x:=by
    intro h
    have hh : F a∈openSegment ℝ (F a) (F b):=
      Eq.mpr (congrArg (fun z : ℂ=>z∈openSegment ℝ (F a) (F b)) (congrArg F h)) hxab
    exact hab (hFinj (left_mem_openSegment_iff.mp hh))
  have hbx : b≠x:=by
    intro h
    have hh : F b∈openSegment ℝ (F a) (F b):=
      Eq.mpr (congrArg (fun z : ℂ=>z∈openSegment ℝ (F a) (F b)) (congrArg F h)) hxab
    exact hab (hFinj (right_mem_openSegment_iff.mp hh))
  have haS : a∈S:=hST ▸ ha
  have hbS : b∈S:=hST ▸ hb
  have hz:=hconv.segment_subset (mem_image_of_mem F ⟨haS,hax⟩)
    (mem_image_of_mem F ⟨hbS,hbx⟩) (openSegment_subset_segment ℝ _ _ hxab)
  obtain ⟨y,hy,he⟩:=hz
  exact hy.2 (hFinj he)

/-- An actual side containing no actual vertex is a whole genuine geodesic line, rather than a proper segment or ray. -/
theorem polygon_side_without_vertex_is_whole_line {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D S : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hS : IsFuchsianPolygonSide P D S)
    (hnv : ∀x∈S,¬IsFuchsianPolygonVertex P D x) :
    ∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine,P.finiteCoordinate '' S=L.carrier := by
  let :=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  obtain ⟨L,hSL⟩:=hS.2.1.2
  obtain ⟨a,ha,b,hb,hab⟩:=hS.2.2
  have haL : P.finiteCoordinate a∈L.carrier:=hSL (mem_image_of_mem _ ha)
  have hbL : P.finiteCoordinate b∈L.carrier:=hSL (mem_image_of_mem _ hb)
  obtain ⟨δ,u,v,hδ,huv,hδu,hδv,hrange⟩:=L.exists_ordered_param
    (fun he=>hab (P.finiteCoordinate.injective he)) haL hbL
  let γ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ∘ δ
  have hγ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsNativeDiscGeodesicParam γ:=hδ.toNativeDisc
  have hγinj : Function.Injective γ:=hγ.1.injective
  let Γ (t : ℝ):=P.finiteCoordinate.symm (γ t)
  have hΓinj : Function.Injective Γ:=P.finiteCoordinate.symm.injective.comp hγinj
  have hpre (T : Set P.domain.carrier) : γ ⁻¹' (P.finiteCoordinate '' T)=Γ ⁻¹' T := by
    ext t
    constructor
    · rintro ⟨x,hx,hxe⟩
      have he : x=Γ t:=P.finiteCoordinate.injective
        (hxe.trans (P.finiteCoordinate.apply_symm_apply (γ t)).symm)
      change Γ t∈T
      exact he ▸ hx
    · intro ht
      exact ⟨Γ t,ht,P.finiteCoordinate.apply_symm_apply (γ t)⟩
  let A:=Γ ⁻¹' S
  have hSclosed : IsClosed S:=by
    obtain ⟨g,hg,he⟩:=hS.1
    rw [he]
    exact isClosed_closure.inter (fuchsianDomainTile_closed P D g)
  have hΓcont : Continuous Γ:=P.finiteCoordinate.symm.continuous.comp hγ.1.continuous
  have hAclosed : IsClosed A:=hSclosed.preimage hΓcont
  have hArange : P.finiteCoordinate '' S⊆range γ:=by rwa [hrange]
  have hAconv : Convex ℝ A:=by
    have hh:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_convex_parameter hγ hArange).mp hS.2.1.1
    rwa [hpre] at hh
  have hAnonempty : A.Nonempty:=by
    refine ⟨u,?_⟩
    change P.finiteCoordinate.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (δ u))∈S
    rw [hδu,P.finiteCoordinate.symm_apply_apply]
    exact ha
  have hAu : A=univ:=by
    by_contra hproper
    obtain ⟨m,hm⟩:=closed_convex_real_extreme_nonempty hAclosed hAconv hAnonempty hproper
    have hconv : Convex ℝ (A\{m}):=(hAconv.mem_extremePoints_iff_convex_sdiff.mp hm).2
    have hArange' : P.finiteCoordinate '' (S\{Γ m})⊆range γ:=
      (image_mono sdiff_subset).trans hArange
    have hpre' : γ ⁻¹' (P.finiteCoordinate '' (S\{Γ m}))=A\{m}:=by
      rw [hpre]
      ext t
      simp only [mem_preimage,mem_sdiff,mem_singleton_iff,hΓinj.eq_iff]
      rfl
    have hrem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' (S\{Γ m})):=by
      apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_convex_parameter hγ hArange').mpr
      rwa [hpre']
    exact polygon_side_remove_nonvertex_not_convex hD hS hm.1 (hnv _ hm.1) hrem
  refine ⟨L,subset_antisymm hSL ?_⟩
  intro z hz
  obtain ⟨t,ht⟩:=hrange ▸ hz
  refine ⟨Γ t,?_,?_⟩
  · show t∈A
    rw [hAu]
    trivial
  · exact (P.finiteCoordinate.apply_symm_apply (γ t)).trans ht

/-- Any actual complete line contained in the closed original polygon has its two genuine ideal endpoints in the original literal ideal boundary. -/
theorem polygon_whole_line_idealEndpoints_subset {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (L :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine)
    (hL : L.carrier⊆P.finiteCoordinate '' closure D) :
    L.idealEndpoints⊆((↑) : ℂ→OnePoint ℂ) '' fuchsianPolygonIdealBoundary P D := by
  let S:=P.finiteCoordinate '' D
  have hLS : L.carrier⊆closure S:=by rwa [P.finiteCoordinate.image_closure] at hL
  have hsub : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscPoint '' L.carrier⊆closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscPoint '' S):=by
    rintro p ⟨z,hz,rfl⟩
    have hf : Continuous _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscPoint:=OnePoint.continuous_coe.comp Complex.UnitDisc.continuous_coe
    exact mem_closure_image hf.continuousAt (hLS hz)
  intro p hp
  have hpcl : p∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscPoint ''
    S):=closure_minimal hsub isClosed_closure hp.1
  cases p with
  | infty =>
    have hh : (OnePoint.infty : OnePoint
      ℂ)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscIdealBoundary:=hp.2
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscIdealBoundary] at hh
  | coe z =>
    have hnorm : ‖z‖=1:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary z).mp hp.2
    have hzcl : z∈closure (((↑) : 𝔻→ℂ) '' S):=by
      rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]
      rw [image_image]
      exact hpcl
    refine ⟨z,?_,rfl⟩
    change z∈closure ((fun x=>(P.finiteCoordinate x:ℂ)) '' D)∩Metric.sphere (0:ℂ) 1
    refine ⟨?_,?_⟩
    · simpa only [S,image_image,Function.comp_def] using hzcl
    · simpa only [Metric.mem_sphere,dist_zero_right] using hnorm

/-- Finite area permits only finitely many entire geodesic lines in the actual closed polygon, because their true endpoint pairs lie in its finite genuine ideal boundary. -/
theorem finite_area_polygon_whole_lines_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    {L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine | L.carrier⊆P.finiteCoordinate '' closure D}.Finite := by
  let E:=((↑) : ℂ→OnePoint ℂ) '' fuchsianPolygonIdealBoundary P D
  have hE : E.Finite:=(finite_area_polygon_idealBoundary_finite hD harea).image _
  apply (hE.powerset.preimage
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.idealEndpoints_injective.injOn).subset
  intro L hL
  exact polygon_whole_line_idealEndpoints_subset P D L hL

/-- Only finitely many actual sides can contain any one true finite vertex. -/
theorem polygon_vertex_incident_sides_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier)
    (hx : IsFuchsianPolygonVertex P D x) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧ x∈S}.Finite := by
  obtain ⟨S,T,hS,hT,hST,hxS,hxT,hall,hendS,hendT⟩:=hD.vertex_exactly_two_sides hx
  apply (Set.toFinite ({S,T} : Set (Set P.domain.carrier))).subset
  intro U hU
  exact (hall U).mp hU

/-- Finite area gives finitely many actual sides that contain a true finite vertex. -/
theorem finite_area_polygon_vertex_sides_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧
      ∃x∈S,IsFuchsianPolygonVertex P D x}.Finite := by
  have hf : (⋃x∈{x | IsFuchsianPolygonVertex P D x},
      {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧ x∈S}).Finite:=
    (finite_area_polygon_vertices_finite hD harea).biUnion
      (fun x hx=>polygon_vertex_incident_sides_finite hD x hx)
  apply hf.subset
  rintro S ⟨hS,x,hxS,hx⟩
  exact mem_iUnion₂.mpr ⟨x,hx,hS,hxS⟩

/-- Finite area also gives finitely many actual sides with no true finite vertex; these have been proved to be whole geodesic lines. -/
theorem finite_area_polygon_nonvertex_sides_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧
      ∀x∈S,¬IsFuchsianPolygonVertex P D x}.Finite := by
  have hf:=(finite_area_polygon_whole_lines_finite hD harea).image
    (fun L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine=>P.finiteCoordinate.symm '' L.carrier)
  apply hf.subset
  rintro S ⟨hS,hnv⟩
  obtain ⟨L,hSL⟩:=polygon_side_without_vertex_is_whole_line hD hS hnv
  have hL : L.carrier⊆P.finiteCoordinate '' closure D:=by
    rw [←hSL]
    exact image_mono (fun x hx=>(hS.subset_frontier hD.locallyFinite.fundamental hx).1)
  refine ⟨L,hL,?_⟩
  change P.finiteCoordinate.symm '' L.carrier=S
  rw [←hSL,image_image]
  simp only [Homeomorph.symm_apply_apply,image_id']

/-- Genuine finite hyperbolic area forces the actual original locally finite convex fundamental polygon to have finitely many literal sides. No finite-generation or supplied finite-polygon hypothesis occurs. -/
theorem finite_area_polygon_sides_finite {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite := by
  apply ((finite_area_polygon_vertex_sides_finite hD harea).union
    (finite_area_polygon_nonvertex_sides_finite hD harea)).subset
  intro S hS
  by_cases hx : ∃x∈S,IsFuchsianPolygonVertex P D x
  · exact Or.inl ⟨hS,hx⟩
  · exact Or.inr ⟨hS,by simpa only [not_exists,not_and] using hx⟩

/-- The actual side subtype of a genuine finite-area fundamental polygon is finite. -/
theorem finite_area_polygon_finite_sides {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    Finite (FuchsianPolygonSides P D) := (finite_area_polygon_sides_finite hD harea).to_subtype

/-- All actual elliptic centers in a genuine finite-area closed polygon form a finite set, including order-two centers in self-paired side interiors. -/
theorem finite_area_polygon_elliptic_centers_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    (closure D∩fuchsianEllipticPoints P).Finite :=
  finite_sided_polygon_elliptic_centers_finite hD (finite_area_polygon_finite_sides hD harea)

/-- Genuine finite polygon area forces finitely many actual maximal elliptic cyclic subgroup conjugacy classes. -/
theorem finite_area_polygon_elliptic_classes_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic) :=
  finite_sided_polygon_elliptic_classes_finite hD (finite_area_polygon_finite_sides hD harea)

/-- Genuine finite polygon area forces finite generation of the original whole group by its actual finite side pairings. -/
theorem finite_area_polygon_group_finitelyGenerated {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) : H.FG :=
  finite_sided_fuchsianPolygon_finitelyGenerated hD (finite_area_polygon_finite_sides hD harea)

/-- Every genuine finite-area fundamental domain of the original whole action supplies an actual finite-sided Dirichlet polygon; no convexity or local finiteness is imposed on the given domain. -/
theorem finite_area_fundamentalDomain_finite_dirichlet {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (harea : P.area D≠⊤) :
    ∃w : P.domain.carrier,IsDirichletCenter P w ∧
      IsConvexFuchsianPolygon P (dirichletDomain P w) ∧
      P.area (dirichletDomain P w)≠⊤ ∧ Finite (FuchsianPolygonSides P (dirichletDomain P w)) := by
  obtain ⟨w,hw⟩:=finite_area_exists_dirichlet_center P
  have hpoly:=dirichletDomain_isConvexFuchsianPolygon P w hw
  have he:=fuchsianFundamentalDomain_area_eq hpoly.locallyFinite.fundamental hD
  have ha : P.area (dirichletDomain P w)≠⊤:=by rwa [he]
  exact ⟨w,hw,hpoly,ha,finite_area_polygon_finite_sides hpoly ha⟩

/-- A genuine finite-area fundamental domain in any original Fuchsian disc forces finite generation of the original entire group. -/
theorem finite_area_group_finitelyGenerated {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (S : Set (fuchsianGeometricDomain D).carrier)
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) S)
    (harea : geometricModelArea D S≠⊤) : H.FG := by
  obtain ⟨w,hw,hareaW⟩:=finite_area_geometricDisc_dirichlet D S hS harea
  have hpoly:=dirichletDomain_isConvexFuchsianPolygon (geometricDiscData D) w hw
  have hQ:=finite_area_polygon_group_finitelyGenerated hpoly hareaW
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence (geometricDiscNormalizer D) H
  have : Group.FG (geometricDiscGroup D):=(Group.fg_iff_subgroup_fg _).mpr hQ
  have : Group.FG H:=Group.fg_of_surjective (f:=e.symm.toMonoidHom) e.symm.surjective
  exact (Group.fg_iff_subgroup_fg H).mp inferInstance

end LowDimensionalTopology.Geometry.Fuchsian
