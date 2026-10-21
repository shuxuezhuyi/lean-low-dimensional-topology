module
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Quotient.PolygonMultiplicityLocalConstancy
public import LowDimensionalTopology.Geometry.Hyperbolic.Topology.NativePuncturedConnectivity
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- Actual native discreteness gives countability by finite compact transporters and
the genuine countable exhaustion by hyperbolic metric balls. -/
theorem nativeDiscreteIsometrySubgroup_countable (H : Subgroup (ℍ≃ᵢℍ))
    [DiscreteTopology H] : Countable H := by
  let a : ℍ:=UpperHalfPlane.I
  have hf (n : ℕ) : {g : H | g • a∈Metric.closedBall a n}.Finite := by
    have hh:=(_root_.LowDimensionalTopology.Geometry.Fuchsian.nativeIsometrySubgroup_properlyDiscontinuous
      H).finite_disjoint_inter_image
      (isCompact_singleton : IsCompact ({a} : Set ℍ)) (isCompact_closedBall a (n : ℝ))
    apply hh.subset
    intro g hg
    exact ⟨g • a,⟨a,mem_singleton a,rfl⟩,hg⟩
  apply Set.countable_univ_iff.mp
  apply (Set.countable_iUnion (fun n=>(hf n).countable)).mono
  intro g _
  obtain ⟨n,hn⟩:=exists_nat_gt (dist (g • a) a)
  exact mem_iUnion.mpr ⟨n,by change dist (g • a) a≤(n : ℝ);exact hn.le⟩

/-- The genuine union of the translated original vertices is countable. -/
theorem NativeGeodesicPolygonGeometry.translated_vertices_countable
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] : (⋃g : H,g • V).Countable := by
  let : Countable H:=nativeDiscreteIsometrySubgroup_countable H
  have hv : V.Countable := by
    let : DiscreteTopology V:=G.vertex_discrete.to_subtype
    exact (TopologicalSpace.separableSpace_iff_countable).mp inferInstance
  exact Set.countable_iUnion (fun g=>hv.image (fun x=>g • x))

/-- Local constancy and the actual punctured-plane connectivity give equality of the
entire actual angular sums at all points away from translated original vertices. -/
theorem NativeGeodesicPolygonGeometry.angularMultiplicity_eq_away_vertices
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉V →S.OppositeSideNeighborhoods s x)
    (x y : ℍ) (hx : ∀g : S.Generated,x∉g • V) (hy : ∀g : S.Generated,y∉g • V) :
    nativePolygonAngularMultiplicityRadians S.Generated P.carrier x=
      nativePolygonAngularMultiplicityRadians S.Generated P.carrier y := by
  let U : Set ℍ:=(⋃g : S.Generated,g • V)ᶜ
  let f : U→ℝ:=fun z=>nativePolygonAngularMultiplicityRadians S.Generated P.carrier z.val
  have hu : IsPreconnected U:=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlane_countable_complement_pathConnected
      (G.translated_vertices_countable S.Generated)).isConnected.isPreconnected
  have hn (z : U) : ∀g : S.Generated,z.val∉g • V := by
    intro g hg
    exact z.property (mem_iUnion.mpr ⟨g,hg⟩)
  have hc : IsLocallyConstant f:=by
    apply (IsLocallyConstant.iff_eventually_eq f).mpr
    intro z
    exact (continuous_subtype_val.tendsto z).eventually
      (G.angularMultiplicity_locally_constant_away_vertices S hP hV hOpp z.val (hn z))
  let a : U:=⟨x,by simpa only [U,mem_compl_iff,mem_iUnion,not_exists] using hx⟩
  let b : U:=⟨y,by simpa only [U,mem_compl_iff,mem_iUnion,not_exists] using hy⟩
  have hconn : PreconnectedSpace U:=isPreconnected_iff_preconnectedSpace.mp hu
  let : PreconnectedSpace U:=hconn
  exact hc.apply_eq_of_isPreconnected isPreconnected_univ (x:=a) (y:=b) trivial trivial

/-- The actual union of all original translated sides is genuinely null for the
native reference volume, by countable native geodesic lines. No area invariance is assumed. -/
theorem NativeGeodesicPolygonGeometry.translated_boundary_volume_zero
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] : volume (⋃g : H,g • P.boundary)=0 := by
  let : Countable H:=nativeDiscreteIsometrySubgroup_countable H
  let : Countable P.Side:=G.countable_sides.to_subtype
  have hsub : (⋃g : H,g • P.boundary)⊆⋃(g : H) (s : P.Side),g • s.val := by
    intro z hz
    obtain ⟨g,p,hp,hpz⟩:=mem_iUnion.mp hz
    obtain ⟨s,hs,hps⟩:=mem_sUnion.mp hp
    exact mem_iUnion.mpr ⟨g,mem_iUnion.mpr ⟨⟨s,hs⟩,⟨p,hps,hpz⟩⟩⟩
  apply measure_mono_null hsub
  apply measure_iUnion_null
  intro g
  apply measure_iUnion_null
  intro s
  obtain ⟨L,hL⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine g.val.isometry (G.line
    s)
  apply measure_mono_null (t:=L.carrier) _ L.volume_zero
  rintro z ⟨p,hp,rfl⟩
  rw [←hL]
  exact mem_image_of_mem _ (G.side_subset_line s hp)

/-- Every countable actual native point set is null for the genuine hyperbolic
volume, by its literal positive-density integral in the complex upper half-plane. -/
theorem native_countable_volume_zero {T : Set ℍ} (hT : T.Countable) : volume T=0 := by
  have hh : (volume : Measure ℂ) (UpperHalfPlane.coe '' T)=0:=
    (hT.image UpperHalfPlane.coe).measure_zero volume
  rw [UpperHalfPlane.volume_eq_lintegral,Measure.restrict_eq_zero.mpr hh]
  exact lintegral_zero_measure _

/-- Every nonempty actual native open set has positive genuine hyperbolic volume. -/
theorem native_open_volume_pos {U : Set ℍ} (hU : IsOpen U) (hne : U.Nonempty) :
    0<volume U := by
  let f : ℂ→ℝ≥0∞:=fun z=>↑((1 / ‖z.im‖₊)^2 : NNReal)
  have hm : Measurable f:=by fun_prop
  have hs : Function.support f∩(UpperHalfPlane.coe '' U)=UpperHalfPlane.coe '' U := by
    apply inter_eq_right.mpr
    rintro z ⟨p,hp,rfl⟩
    change f p≠0
    have hn : 0<‖p.im‖₊:=nnnorm_pos.mpr p.im_ne_zero
    have hf : 0<f p:=by dsimp [f];positivity
    exact ne_of_gt hf
  rw [UpperHalfPlane.volume_eq_lintegral,setLIntegral_pos_iff hm,hs]
  exact (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hU).measure_pos volume
    (hne.image UpperHalfPlane.coe)

/-- An actual original interior point avoids every actual translated boundary and
vertex. Its existence follows from a nonempty open set and genuine null-set estimates. -/
theorem NativeGeodesicPolygonGeometry.exists_regular_interior_point
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    ∃x∈P.interior,(∀g : H,x∉g • P.boundary) ∧(∀g : H,x∉g • V) := by
  let B : Set ℍ:=⋃g : H,g • P.boundary
  let T : Set ℍ:=⋃g : H,g • V
  have hnull : volume (B∪T)=0:=measure_union_null
    (G.translated_boundary_volume_zero H) (native_countable_volume_zero (G.translated_vertices_countable H))
  have hp : 0<volume P.interior:=native_open_volume_pos G.interior_open P.interior_nonempty
  have hn : ¬P.interior⊆B∪T:=by
    intro hh
    exact ne_of_gt hp (measure_mono_null hh hnull)
  obtain ⟨x,hx,hxt⟩:=not_subset.mp hn
  refine ⟨x,hx,?_,?_⟩
  · intro g hg
    exact hxt (Or.inl (mem_iUnion.mpr ⟨g,hg⟩))
  · intro g hg
    exact hxt (Or.inr (mem_iUnion.mpr ⟨g,hg⟩))

/-- The true full angular sum is one fixed positive integral multiple of 2*pi at
all actual points away from translated vertices; no constant overlap is prescribed. -/
theorem NativeGeodesicPolygonGeometry.angularMultiplicity_positive_integer_away_vertices
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉V →S.OppositeSideNeighborhoods s x) :
    ∃k : ℕ,0<k ∧∀y : ℍ,(∀g : S.Generated,y∉g • V) →
      nativePolygonAngularMultiplicityRadians S.Generated P.carrier y=2*Real.pi*(k : ℝ) := by
  obtain ⟨a,ha,hBoundary,hVertex⟩:=G.exists_regular_interior_point S.Generated
  have hfrontier : ∀g : S.Generated,a∉frontier (g • P.carrier) := by
    intro g hg
    apply hBoundary g
    change a∈frontier (g.val.toHomeomorph '' P.carrier) at hg
    rw [←g.val.toHomeomorph.image_frontier] at hg
    obtain ⟨p,hp,hpa⟩:=hg
    refine ⟨p,?_,hpa⟩
    rw [G.carrier_closure] at hp
    rw [←G.frontier_boundary]
    exact frontier_closure_subset hp
  obtain ⟨k,hk⟩:=nativePolygonAngularMultiplicity_exists_nat_off_frontiers
    S.Generated P.carrier hP a hfrontier
  have hinside : a∈interior P.carrier:=by rw [G.carrier_closure,G.regular_open];exact ha
  have hone : (1 : ℝ≥0∞)≤nativePolygonAngularMultiplicity S.Generated P.carrier a := by
    have hh:=ENNReal.le_tsum (f:=fun g : S.Generated=>nativeLocalAngularFraction P.carrier (g⁻¹ • a))
      (1 : S.Generated)
    simpa only [inv_one,one_smul,nativeLocalAngularFraction_of_interior hinside,
      nativePolygonAngularMultiplicity] using hh
  have hkpos : 0<k := by
    rw [hk] at hone
    exact_mod_cast (lt_of_lt_of_le (show (0 : ℝ≥0∞)<1 by norm_num) hone)
  have hangle : nativePolygonAngularMultiplicityRadians S.Generated P.carrier a=2*Real.pi*(k : ℝ) := by
    rw [nativePolygonAngularMultiplicityRadians,hk,ENNReal.toReal_natCast]
  refine ⟨k,hkpos,?_⟩
  intro y hy
  exact (G.angularMultiplicity_eq_away_vertices S hP hV hOpp y a hy hVertex).trans hangle

/-- The original Jordan polygon and literal side intervals imply the positive integer
angular multiplicity on the entire actual punctured plane, including nonvertex side points. -/
theorem nativeJordan_angularMultiplicity_positive_integer_away_vertices
    {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices →S.OppositeSideNeighborhoods s x) :
    ∃k : ℕ,0<k ∧∀y : ℍ,(∀g : S.Generated,y∉g • D.vertices) →
      nativePolygonAngularMultiplicityRadians S.Generated P.carrier y=2*Real.pi*(k : ℝ) :=
  (nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary
    D).angularMultiplicity_positive_integer_away_vertices S hP (D.pairing_preserves_vertices S) hOpp

end LowDimensionalTopology.Geometry.Polygon
