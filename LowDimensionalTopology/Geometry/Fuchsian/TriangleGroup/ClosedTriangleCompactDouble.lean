/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Double.BoundaryDoubleOpen
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleOrbitDouble
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.FiniteTriangleOrbitDouble
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set
  Topology
open scoped UpperHalfPlane Complex.UnitDisc

/-- The actual compact physical closed triangle, retaining its genuine ideal endpoints. -/
abbrev closedTrianglePhysicalCompactRegion
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) := T.toDiscTriangle.complexClosedCarrier

/-- Two literal compactified physical triangles, glued only along their true sides. -/
abbrev closedTrianglePhysicalCompactDouble (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.BoundaryDouble (closedTrianglePhysicalCompactRegion T) {p|p.val∈frontier (closedTrianglePhysicalCompactRegion T)}

def closedTrianglePhysicalStandardHomeomorph (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    closedTrianglePhysicalCompactRegion T≃ₜ_root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle :=
  (T.toDiscTriangle.ambientCoordinateHomeomorph.image _).trans
    (Homeomorph.setCongr T.toDiscTriangle.ambient_image_closedCarrier)

theorem closedTrianglePhysicalStandardHomeomorph_boundary
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p : closedTrianglePhysicalCompactRegion T) :
    p.val∈frontier (closedTrianglePhysicalCompactRegion T) ↔
      (closedTrianglePhysicalStandardHomeomorph T p).val∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle := by
  change p.val∈frontier T.toDiscTriangle.complexClosedCarrier ↔
    T.toDiscTriangle.ambientCoordinateHomeomorph p.val∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle
  rw [←T.toDiscTriangle.ambient_image_closedCarrier,
    ←T.toDiscTriangle.ambientCoordinateHomeomorph.image_frontier,
    T.toDiscTriangle.ambientCoordinateHomeomorph.injective.mem_set_image]

/-- The genuine compact double is a sphere, before any identification with a cusp-filled quotient. -/
def closedTrianglePhysicalCompactDoubleSphereHomeomorph
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    closedTrianglePhysicalCompactDouble T≃ₜMetric.sphere (0:EuclideanSpace ℝ (Fin 3)) 1 := by
  let E:=(closedTrianglePhysicalStandardHomeomorph T).trans standardTriangleComplexHomeomorph
  have hB (p:closedTrianglePhysicalCompactRegion T) :
      p.val∈frontier (closedTrianglePhysicalCompactRegion T) ↔
        (E p).val∈frontier standardComplexClosedTriangle :=
    (closedTrianglePhysicalStandardHomeomorph_boundary T p).trans
      (standardTriangleComplexHomeomorph_boundary (closedTrianglePhysicalStandardHomeomorph T p))
  let h:=standardComplexClosedTriangle_properties
  exact (_root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleCongr E hB).trans
    (_root_.LowDimensionalTopology.Geometry.Surfaces.closedConvexRegionDoubleSphereHomeomorph h.1 h.2.1 h.2.2.1 h.2.2.2)

theorem closedTrianglePhysicalCompactDouble_hasTopologicalGenus_zero
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (closedTrianglePhysicalCompactDouble T) 0 :=
  ⟨(closedTrianglePhysicalCompactDoubleSphereHomeomorph T).trans _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleSurfaceZeroHomeomorph.symm⟩

/-- The original physical half-plane point in the genuine closed-disc model. -/
def closedTrianglePhysicalCayley (z:ℍ) :ℂ:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ)

theorem closedTrianglePhysicalCayley_isOpenEmbedding : IsOpenEmbedding closedTrianglePhysicalCayley :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_isOpenEmbedding_coe.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenEmbedding

theorem closedTrianglePhysicalCayley_preimage (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    closedTrianglePhysicalCayley ⁻¹' closedTrianglePhysicalCompactRegion T=
      (closedTrianglePoincarePolygon T).carrier := by
  rw [closedTrianglePoincarePolygon_carrier]
  change _ ⁻¹' T.toDiscTriangle.complexClosedCarrier=closure _
  rw [←T.toDiscTriangle.complexInterior_closure,
    closedTrianglePhysicalCayley_isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      closedTrianglePhysicalCayley_isOpenEmbedding.continuous]
  rfl

theorem closedTrianglePhysicalCayley_range : range closedTrianglePhysicalCayley=Metric.ball (0:ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    exact mem_ball_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x).norm_lt_one
  · intro hz
    let d:𝔻:=Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz)
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d,?_⟩
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d):ℂ)=z
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    rfl


/-- Exactly the physical part of the original closed triangle, with only actual ideal endpoints excluded. -/
def closedTrianglePhysicalOpenRegion (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : Set (closedTrianglePhysicalCompactRegion T):=
  {p|‖p.val‖<1}

def closedTrianglePhysicalRegionHomeomorph (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (closedTrianglePoincarePolygon T).Point≃ₜclosedTrianglePhysicalOpenRegion T where
  toFun p:=⟨⟨closedTrianglePhysicalCayley p.val,
    (congrArg (fun A:Set ℍ=>p.val∈A) (closedTrianglePhysicalCayley_preimage T)).mpr p.property⟩,
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc p.val).norm_lt_one⟩
  invFun p:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (Complex.UnitDisc.mk p.val.val p.property),by
    rw [←closedTrianglePhysicalCayley_preimage]
    change closedTrianglePhysicalCayley (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (Complex.UnitDisc.mk p.val.val p.property))∈closedTrianglePhysicalCompactRegion T
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (Complex.UnitDisc.mk p.val.val p.property)):ℂ)∈closedTrianglePhysicalCompactRegion T
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    exact p.val.property⟩
  left_inv p:=by
    apply Subtype.ext
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc p.val)=p.val
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc p.val
  right_inv p:=by
    apply Subtype.ext
    apply Subtype.ext
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (Complex.UnitDisc.mk p.val.val p.property)):ℂ)=p.val.val
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    rfl
  continuous_toFun:=by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact closedTrianglePhysicalCayley_isOpenEmbedding.continuous.comp continuous_subtype_val
  continuous_invFun:=by
    apply Continuous.subtype_mk
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_discToHalfPlane.comp
    apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun p:closedTrianglePhysicalOpenRegion T=>p.val.val)
    exact continuous_subtype_val.comp continuous_subtype_val


theorem closedTrianglePhysicalRegionHomeomorph_boundary
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p:(closedTrianglePoincarePolygon T).Point) :
    p.val∈(closedTrianglePoincarePolygon T).boundary ↔
      (closedTrianglePhysicalRegionHomeomorph T p).val.val∈frontier (closedTrianglePhysicalCompactRegion T) := by
  change p.val∈⋃₀(range T.nativeSide) ↔ closedTrianglePhysicalCayley p.val∈frontier _
  rw [T.nativeSide_boundary]
  have hF:closedTrianglePhysicalCayley ⁻¹' frontier (closedTrianglePhysicalCompactRegion T)=frontier T.interior:=by
    rw [closedTrianglePhysicalCayley_isOpenEmbedding.isOpenMap.preimage_frontier_eq_frontier_preimage
      closedTrianglePhysicalCayley_isOpenEmbedding.continuous,closedTrianglePhysicalCayley_preimage,
      closedTrianglePoincarePolygon_carrier]
    rw [frontier,closure_closure,closedTriangle_regular_open,T.interior_isOpen.frontier_eq]
  change p.val∈frontier T.interior ↔p.val∈closedTrianglePhysicalCayley ⁻¹' frontier (closedTrianglePhysicalCompactRegion T)
  rw [hF]

def closedTrianglePhysicalOpenDoubleHomeomorph (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (closedTrianglePoincarePairing T).ChamberDouble≃ₜ
      _root_.LowDimensionalTopology.Geometry.Surfaces.BoundaryDouble (closedTrianglePhysicalOpenRegion T)
        {p|p.val.val∈frontier (closedTrianglePhysicalCompactRegion T)} :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleCongr (closedTrianglePhysicalRegionHomeomorph T)
    (closedTrianglePhysicalRegionHomeomorph_boundary T)

/-- The actual old physical double is the open part of the actual compactified double. -/
def closedTrianglePhysicalDoubleInclusion (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (closedTrianglePoincarePairing T).ChamberDouble→closedTrianglePhysicalCompactDouble T :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleInclusion (closedTrianglePhysicalOpenRegion T) ∘
    closedTrianglePhysicalOpenDoubleHomeomorph T

theorem closedTrianglePhysicalDoubleInclusion_isOpenEmbedding
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    IsOpenEmbedding (closedTrianglePhysicalDoubleInclusion T) := by
  have hU:IsOpen (closedTrianglePhysicalOpenRegion T):=isOpen_lt continuous_subtype_val.norm continuous_const
  exact (_root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleInclusion_isOpenEmbedding hU).comp
    (closedTrianglePhysicalOpenDoubleHomeomorph T).isOpenEmbedding

theorem closedTrianglePhysicalDoubleInclusion_range
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    range (closedTrianglePhysicalDoubleInclusion T)=
      _root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleBase ⁻¹' closedTrianglePhysicalOpenRegion T := by
  rw [closedTrianglePhysicalDoubleInclusion,range_comp,
    (closedTrianglePhysicalOpenDoubleHomeomorph T).surjective.range_eq,image_univ,
    _root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleInclusion_range]


/-- The actual conformal orbit surface embeds openly in the true compact physical double. -/
def closedTriangleConformalOrbitCompactInclusion (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (triangleConformalGroup T) ℍ→closedTrianglePhysicalCompactDouble T :=
  closedTrianglePhysicalDoubleInclusion T ∘ (closedTriangleConformalOrbitDoubleHomeomorph T ha hb hc).symm

theorem closedTriangleConformalOrbitCompactInclusion_isOpenEmbedding
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    IsOpenEmbedding (closedTriangleConformalOrbitCompactInclusion T ha hb hc) :=
  (closedTrianglePhysicalDoubleInclusion_isOpenEmbedding T).comp
    (closedTriangleConformalOrbitDoubleHomeomorph T ha hb hc).symm.isOpenEmbedding

theorem closedTriangleConformalOrbitCompactInclusion_range
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    range (closedTriangleConformalOrbitCompactInclusion T ha hb hc)=
      _root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleBase ⁻¹' closedTrianglePhysicalOpenRegion T := by
  rw [closedTriangleConformalOrbitCompactInclusion,range_comp,
    (closedTriangleConformalOrbitDoubleHomeomorph T ha hb hc).symm.surjective.range_eq,
    image_univ,closedTrianglePhysicalDoubleInclusion_range]

end LowDimensionalTopology.Geometry.Fuchsian
