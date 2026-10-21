/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Polygon.Convexity.FiniteHullSupports
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteConvexBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaPolygonSides
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletHorocycles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Topology
open scoped OnePoint UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance idealVerticesSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance idealVerticesSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- A true endpoint of a segment covered by finitely many actual sets belongs to the closure of one set restricted to the genuine open segment. -/
theorem finite_cover_segment_endpoint {ι : Type*} [Finite ι] (F : ι→Set ℂ) (a b : ℂ)
    (hc : openSegment ℝ a b⊆⋃i,F i) :
    ∃i,a∈closure (F i∩openSegment ℝ a b) := by
  have hs : openSegment ℝ a b⊆⋃i,F i∩openSegment ℝ a b:=by
    intro z hz
    obtain ⟨i,hi⟩:=mem_iUnion.mp (hc hz)
    exact mem_iUnion.mpr ⟨i,hi,hz⟩
  have ha : a∈closure (openSegment ℝ a b):=segment_subset_closure_openSegment (left_mem_segment ℝ a b)
  have hh:=closure_mono hs ha
  rw [closure_iUnion_of_finite] at hh
  exact mem_iUnion.mp hh

/-- The actual Klein image of an original side lies on a genuine nonzero affine line. -/
theorem actual_polygon_side_klein_equation {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D S : Set P.domain.carrier}
    (hS : IsFuchsianPolygonSide P D S) :
    ∃m : ℂ,∃t : ℝ,m≠0∧∀x∈S,inner ℝ m (P.kleinCoordinate x)=t := by
  obtain ⟨L,hL⟩:=hS.2.1.2
  obtain ⟨m,t,hm,he⟩:=L.exists_klein_linear_equation
  refine ⟨m,t,hm,?_⟩
  intro x hx
  exact (he (P.finiteCoordinate x)).mp (hL (mem_image_of_mem _ hx))

/-- At a genuine ideal endpoint of a supporting edge, one actual original side reaches that same ideal point and lies on that precise supporting line. Original sides are retained. -/
theorem finite_area_support_edge_actual_side {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤)
    {n : ℕ} (S : _root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hregion : S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P D)
    (i : Fin n) (u : Circle)
    (hu : (u:ℂ)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)∨
      (u:ℂ)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))) :
    ∃s : FuchsianPolygonSides P D,IsFuchsianSideIdealEndpoint P s.val u∧
      ∀x∈s.val,inner ℝ (S.normals i) (P.kleinCoordinate x)=S.offsets i := by
  classical
  let :=finite_area_polygon_finite_sides hD harea
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))
  have hab : a≠b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (S.vertices_injective.ne
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonSupport_next_ne_self S.three_le i).symm)
  have ha : a∈Metric.closedBall (0:ℂ) 1:=by
    simpa only [Metric.mem_closedBall,dist_zero_right,a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate] using (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein (S.vertices i)).norm_le_one
  have hb : b∈Metric.closedBall (0:ℂ) 1:=by
    simpa only [Metric.mem_closedBall,dist_zero_right,b,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate] using
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein (S.vertices (finRotate n i))).norm_le_one
  let F : FuchsianPolygonSides P D→Set ℂ:=fun s=>P.kleinCoordinate '' s.val
  have hcover : openSegment ℝ a b⊆⋃s,F s:=by
    intro z hz
    have hzball:=openSegment_subset_ball_of_ne ha hb hab hz
    have hzface:=S.toCenteredData.segment_subset_face i (openSegment_subset_segment ℝ a b hz)
    have hzK : z∈fuchsianPolygonCompactKlein P D:=hregion ▸ hzface.1
    have hzfinite : z∈P.kleinCoordinate '' closure D:=by
      rw [fuchsianPolygonCompactKlein_finite_part]
      exact ⟨hzK,hzball⟩
    obtain ⟨x,hxcl,hxz⟩:=hzfinite
    have hxn : x∉D:=by
      intro hx
      have ho:=P.kleinCoordinate_isOpenEmbedding.isOpenMap D hD.locallyFinite.fundamental.isOpen
      have hzint : z∈interior (fuchsianPolygonCompactKlein P D):=by
        exact hxz ▸ interior_mono subset_closure (ho.interior_eq.symm ▸ mem_image_of_mem _ hx)
      rw [←hregion,S.toCenteredData.interior_kleinRegion] at hzint
      exact (ne_of_lt (hzint i)) hzface.2
    have hxf : x∈frontier D:=by
      rw [hD.locallyFinite.fundamental.isOpen.frontier_eq]
      exact ⟨hxcl,hxn⟩
    obtain ⟨A,hA,hxA⟩:=hD.boundary_mem_side hxf
    exact mem_iUnion.mpr ⟨⟨A,hA⟩,x,hxA,hxz⟩
  have hucl : ∃s,(u:ℂ)∈closure (F s∩openSegment ℝ a b):=by
    rcases hu with hu|hu
    · exact hu ▸ finite_cover_segment_endpoint F a b hcover
    · have hrev : openSegment ℝ b a⊆⋃s,F s:=by simpa only [openSegment_symm] using hcover
      obtain ⟨s,hs⟩:=finite_cover_segment_endpoint F b a hrev
      refine ⟨s,?_⟩
      rw [hu]
      simpa only [openSegment_symm] using hs
  obtain ⟨s,hs⟩:=hucl
  have huK : (u:ℂ)∈closure (P.kleinCoordinate '' s.val):=closure_mono inter_subset_left hs
  have hendpoint : IsFuchsianSideIdealEndpoint P s.val u:=by
    have hh:=(compactKlein_ideal_mem_iff P s.val (u:ℂ) (mem_sphere_zero_iff_norm.mp u.property)).mp huK
    exact hh.1
  obtain ⟨m,t,hm,hline⟩:=actual_polygon_side_klein_equation s.property
  have hsub : F s⊆{z : ℂ | inner ℝ m z=t}:=by
    rintro z ⟨x,hx,rfl⟩
    exact hline x hx
  have hum : inner ℝ m (u:ℂ)=t:=
    closure_minimal hsub (isClosed_eq (continuous_const.inner continuous_id) continuous_const) huK
  have hus : inner ℝ (S.normals i) (u:ℂ)=S.offsets i:=by
    rcases hu with he|he
    · rw [he];exact (S.incident i).1
    · rw [he];exact (S.incident i).2
  have hne : (F s∩openSegment ℝ a b).Nonempty:=closure_nonempty_iff.mp ⟨(u:ℂ),hs⟩
  obtain ⟨z,hzF,hzSeg⟩:=hne
  have hzm : inner ℝ m z=t:=hsub hzF
  have hzs : inner ℝ (S.normals i) z=S.offsets i:=
    (S.toCenteredData.segment_subset_face i (openSegment_subset_segment ℝ a b hzSeg)).2
  have huz : (u:ℂ)≠z:=by
    intro he
    have hh:=openSegment_subset_ball_of_ne ha hb hab hzSeg
    have hn : ‖(u:ℂ)‖=1:=mem_sphere_zero_iff_norm.mp u.property
    rw [←he,Metric.mem_ball,dist_zero_right,hn] at hh
    exact lt_irrefl 1 hh
  refine ⟨s,hendpoint,?_⟩
  intro x hx
  have hn : S.normals i≠0:=by intro he;have hh:=S.normal_norm i;rw [he,norm_zero] at hh;norm_num at hh
  exact (_root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points
    (x:=P.kleinCoordinate x) hn hm huz
    hus hzs hum hzm).mpr (hline x hx)

/-- At every genuine ideal vertex of the constructed convex model, two distinct original actual sides reach that very same original ideal point. -/
theorem finite_area_model_ideal_vertex_isProper {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤)
    {n : ℕ} (S : _root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hregion : S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P D)
    (i : Fin n) (u : Circle) (hu : (u:ℂ)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      (S.vertices i)) :
    IsProperFuchsianInfiniteVertex P D u := by
  classical
  let j:=(finRotate n).symm i
  have hji : finRotate n j=i:=Equiv.apply_symm_apply _ _
  obtain ⟨s,hus,hs⟩:=finite_area_support_edge_actual_side hD harea S hregion i u (Or.inl hu)
  obtain ⟨t,hut,ht⟩:=finite_area_support_edge_actual_side hD harea S hregion j u
    (Or.inr (by rw [hji];exact hu))
  have hst : s≠t:=by
    intro he
    have hstval : s.val=t.val:=congrArg Subtype.val he
    obtain ⟨x,hx,y,hy,hxy⟩:=s.property.2.2
    have hxT : x∈t.val:=hstval ▸ hx
    have hyT : y∈t.val:=hstval ▸ hy
    have hni : S.normals i≠0:=by intro hh;have hn:=S.normal_norm i;rw [hh,norm_zero] at hn;norm_num at hn
    have hnj : S.normals j≠0:=by intro hh;have hn:=S.normal_norm j;rw [hh,norm_zero] at hn;norm_num at hn
    have hline : inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      (S.vertices (finRotate n i)))=S.offsets i ↔
        inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
          (finRotate n i)))=S.offsets j:=
      _root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points hni hnj
        (P.kleinCoordinate_isOpenEmbedding.injective.ne hxy) (hs x hx) (hs y hy) (ht x hxT) (ht y hyT)
    have hnextj : finRotate n i≠j:=by
      intro hh
      have he:=congrArg (finRotate n) hh
      rw [hji] at he
      exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonSupport_next_next_ne_self S.three_le i he
    have hnextji : finRotate n i≠finRotate n j:=by
      rw [hji]
      exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonSupport_next_ne_self S.three_le i
    exact (ne_of_lt (S.nonincident j (finRotate n i) hnextj hnextji)) (hline.mp (S.incident i).2)
  have huK : (u:ℂ)∈fuchsianPolygonCompactKlein P D:=by
    rw [hu,←hregion]
    exact S.toCenteredData.vertex_mem_region i
  have huE : (u:ℂ)∈fuchsianPolygonIdealBoundary P D:=
    (compactKlein_ideal_mem_iff P D (u:ℂ) (mem_sphere_zero_iff_norm.mp u.property)).mp huK
  exact ⟨huE,s.val,t.val,s.property,t.property,fun hh=>hst (Subtype.ext hh),hus,hut⟩

/-- Every literal ideal closure point of an original finite-area convex fundamental polygon is an actual proper infinite vertex with two distinct original sides. This is proved from the original finite-area geometry, not assumed from the geometric model. -/
theorem finite_area_polygon_idealBoundary_isProper {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤)
    (u : Circle) (hu : (u:ℂ)∈fuchsianPolygonIdealBoundary P D) :
    IsProperFuchsianInfiniteVertex P D u := by
  obtain ⟨n,S,hregion,_hinterior⟩:=finite_area_polygon_actual_cyclic_model hD harea
  have huK : (u:ℂ)∈S.toCenteredData.kleinRegion:=by
    rw [hregion]
    exact (compactKlein_ideal_mem_iff P D (u:ℂ) (mem_sphere_zero_iff_norm.mp u.property)).mpr hu
  have huB : (u:ℂ)∈(Metric.closedBall (0:ℂ) 1).extremePoints ℝ:=by
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    exact u.property
  have huExt : (u:ℂ)∈S.toCenteredData.kleinRegion.extremePoints ℝ:=by
    refine ⟨huK,?_⟩
    intro a ha b hb hab
    exact huB.2 (S.region_subset_closedBall ha) (S.region_subset_closedBall hb) hab
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.cyclic_support_region_eq_convexHull] at huExt
  obtain ⟨i,hi⟩:=extremePoints_convexHull_subset huExt
  exact finite_area_model_ideal_vertex_isProper hD harea S hregion i u hi.symm

/-- The original invariant density is genuinely nonzero, as witnessed by an actual positive-area hyperbolic ball. -/
theorem fuchsian_original_area_ne_zero {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : P.area≠0 := by
  have hv : (volume : Measure ℍ)≠0:=by
    intro he
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_volume_closedBall UpperHalfPlane.I 1 zero_le_one
    rw [he,Measure.coe_zero,Pi.zero_apply] at hh
    have hp : 0<4*Real.pi*Real.sinh ((1:ℝ)/2)^2:=by
      have hs : 0<Real.sinh ((1:ℝ)/2):=Real.sinh_pos_iff.mpr (by norm_num)
      exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (sq_pos_of_pos hs)
    exact (ENNReal.ofReal_pos.mpr hp).ne' hh.symm
  intro hzero
  have hh:=P.area_eq_halfPlane_volume univ MeasurableSet.univ
  rw [hzero,Measure.coe_zero,Pi.zero_apply,image_univ,P.halfPlaneCoordinate.surjective.range_eq] at hh
  exact ((Measure.measure_univ_ne_zero).mpr hv) hh.symm

/-- Genuine good Dirichlet centres exist for the entire original group and original density; no generic-centre hypothesis is supplied. -/
theorem exists_actual_dirichlet_horocycle_good_center {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) :
    ∃w : P.domain.carrier,IsDirichletCenter P w∧w∉dirichletHorocycleBadCenters P := by
  have : NeZero P.area:=⟨fuchsian_original_area_ne_zero P⟩
  exact (dirichletHorocycle_ae_good P).exists

/-- Every literal ideal point of the true Dirichlet polygon at a constructed good centre is fixed by a genuine nonidentity original parabolic element. The polygon has the same finite actual area as the given original fundamental domain. -/
theorem finite_area_exists_dirichlet_all_ideal_parabolic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (harea : P.area D≠⊤) :
    ∃w : P.domain.carrier,IsDirichletCenter P w∧
      IsConvexFuchsianPolygon P (dirichletDomain P w)∧P.area (dirichletDomain P w)≠⊤∧
      ∀u : Circle,(u:ℂ)∈fuchsianPolygonIdealBoundary P (dirichletDomain P w)→
        ∃f : H,f≠1∧_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val∧f.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  obtain ⟨w,hw,hgood⟩:=exists_actual_dirichlet_horocycle_good_center P
  have hpoly:=dirichletDomain_isConvexFuchsianPolygon P w hw
  have harea' : P.area (dirichletDomain P w)≠⊤:=by
    rwa [fuchsianFundamentalDomain_area_eq hpoly.locallyFinite.fundamental hD]
  refine ⟨w,hw,hpoly,harea',?_⟩
  intro u hu
  exact dirichlet_good_proper_vertex_parabolic P w hw hgood u
    (finite_area_polygon_idealBoundary_isProper hpoly harea' u hu)

end LowDimensionalTopology.Geometry.Fuchsian
