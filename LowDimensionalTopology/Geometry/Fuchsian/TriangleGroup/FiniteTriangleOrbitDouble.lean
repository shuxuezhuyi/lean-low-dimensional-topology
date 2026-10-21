/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.ReflectionChamberDouble
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleVertexTessellation
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleProperness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

def finiteTriangleConformalKernel (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    Subgroup (finiteTrianglePoincarePairing T).Generated:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup.subgroupOf (finiteTrianglePoincarePairing T).Generated

theorem finiteTriangleConformalKernel_index (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    (finiteTriangleConformalKernel T).index=2 := by
  unfold finiteTriangleConformalKernel
  rw [finiteTrianglePoincarePairing_generated]
  exact triangleConformalKernel_index_two T.toClosedHTriangle

theorem finiteTriangle_generators_odd (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (s : (finiteTrianglePoincarePolygon T).Side) :
    (finiteTrianglePoincarePairing T).generator s∉finiteTriangleConformalKernel T := by
  change finiteTrianglePoincareElement T s∉_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup
  exact halfPlaneLineReflectionIsometry_not_conformal _

theorem finiteTriangle_generators_fix_side (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (s : (finiteTrianglePoincarePolygon T).Side) (x : ℍ) (hx : x∈s.val) :
    (finiteTrianglePoincarePairing T).generator s • x=x :=
  finiteTrianglePoincareElement_fixed T s hx

/-- The original compact reciprocal-angle triangle's conformal-kernel orbit surface is the literal
boundary double of its actual closed physical triangle. No orbit, covering or FD premise is added. -/
def finiteTriangleKernelOrbitDoubleHomeomorph
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (n : Fin 3→ℕ)
    (hn : ∀i,2≤n i) (hangle : ∀i,finiteTriangleVertexAngle T i=Real.pi/(n i:ℝ)) :
    (finiteTrianglePoincarePairing T).ChamberDouble≃ₜ
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (finiteTriangleConformalKernel T) ℍ := by
  let S:=finiteTrianglePoincarePairing T
  let hA:=finiteTriangle_integral_local_tessellation T n hn hangle
  let hm:=finiteTrianglePoincare_metric_assumptions T
  let E:S.Development≃ₜℍ:=(hA.covering_homeomorph_of_compact S hm
    ((finiteTrianglePoincarePolygon_carrier T).symm ▸ subset_rfl)
    (finiteTrianglePoincarePolygon_isCompact T)).2.homeomorph
  let s:(finiteTrianglePoincarePolygon T).Side:=finiteTrianglePoincareSideEquiv T 0
  exact S.reflectionChamberOrbitHomeomorph (finiteTriangleConformalKernel T)
    (finiteTriangleConformalKernel_index T) (finiteTriangle_generators_odd T)
    (finiteTriangle_generators_fix_side T) (S.generator s)
    (finiteTriangle_generators_odd T s) E (fun _=>rfl)

/-- Changing only the nested subtype labels identifies the kernel with the original actual conformal group. -/
def finiteTriangleConformalKernelEquiv (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    finiteTriangleConformalKernel T≃*triangleConformalGroup T.toClosedHTriangle where
  toFun f:=⟨f.val.val,⟨by rw [←finiteTrianglePoincarePairing_generated];exact f.val.property,f.property⟩⟩
  invFun f:=⟨⟨f.val,by rw [finiteTrianglePoincarePairing_generated];exact f.property.1⟩,f.property.2⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_mul' _ _:=rfl

/-- The two genuine orbit relations coincide because the action-compatible actual groups differ only in subtype labels. -/
def finiteTriangleKernelOrbitHomeomorph (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (finiteTriangleConformalKernel T) ℍ≃ₜ
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (triangleConformalGroup T.toClosedHTriangle) ℍ :=
  Homeomorph.Quotient.congrRight (by
    intro x y
    constructor
    · rintro ⟨g,hg⟩
      exact ⟨finiteTriangleConformalKernelEquiv T g,hg⟩
    · rintro ⟨g,hg⟩
      exact ⟨(finiteTriangleConformalKernelEquiv T).symm g,hg⟩)

def finiteTriangleConformalOrbitDoubleHomeomorph
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (n : Fin 3→ℕ)
    (hn : ∀i,2≤n i) (hangle : ∀i,finiteTriangleVertexAngle T i=Real.pi/(n i:ℝ)) :
    (finiteTrianglePoincarePairing T).ChamberDouble≃ₜ
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (triangleConformalGroup T.toClosedHTriangle) ℍ :=
  (finiteTriangleKernelOrbitDoubleHomeomorph T n hn hangle).trans
    (finiteTriangleKernelOrbitHomeomorph T)

/-- Literal native closed triangle points have their actual barycentric closed triangular model. -/
def finiteTriangleStandardHomeomorph (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    (finiteTrianglePoincarePolygon T).Point≃ₜ_root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle :=
  (Homeomorph.setCongr (finiteTrianglePoincarePolygon_carrier T)).trans
    ((T.coordinate_isOpenEmbedding.isEmbedding.homeomorphImage (closure T.interior)).trans
      (Homeomorph.setCongr T.coordinate_image_closure))

theorem finiteTriangleStandardHomeomorph_boundary (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (p : (finiteTrianglePoincarePolygon T).Point) :
    p.val∈(finiteTrianglePoincarePolygon T).boundary ↔
      (finiteTriangleStandardHomeomorph T p).val∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle := by
  change p.val∈⋃₀(range (finiteTrianglePoincareSide T)) ↔ T.coordinate p.val∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle
  rw [finiteTrianglePoincareSide_boundary,←T.coordinate_image_frontier,
    T.coordinate_isOpenEmbedding.injective.mem_set_image]

/-- The fixed ordinary triangular subset of the complex plane, with its genuine boundary. -/
def standardComplexClosedTriangle : Set ℂ:=Complex.equivRealProdCLM.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle

def standardTriangleComplexHomeomorph : _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle≃ₜstandardComplexClosedTriangle:=
  Complex.equivRealProdCLM.symm.toHomeomorph.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle

theorem standardTriangleComplexHomeomorph_boundary
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle) :
    p.val∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle ↔
      (standardTriangleComplexHomeomorph p).val∈frontier standardComplexClosedTriangle := by
  change p.val∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle ↔
    Complex.equivRealProdCLM.symm.toHomeomorph p.val∈frontier
      (Complex.equivRealProdCLM.symm.toHomeomorph '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle)
  rw [←Complex.equivRealProdCLM.symm.toHomeomorph.image_frontier,
    Complex.equivRealProdCLM.symm.toHomeomorph.injective.mem_set_image]

theorem standardComplexClosedTriangle_properties : IsClosed standardComplexClosedTriangle ∧
    Convex ℝ standardComplexClosedTriangle ∧ (interior standardComplexClosedTriangle).Nonempty ∧
      Bornology.IsBounded standardComplexClosedTriangle := by
  have hc : IsCompact standardComplexClosedTriangle:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle_isCompact.image Complex.equivRealProdCLM.symm.continuous
  refine ⟨hc.isClosed,_root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle_convex.linear_image Complex.equivRealProdCLM.symm.toLinearMap,?_,hc.isBounded⟩
  change (interior (Complex.equivRealProdCLM.symm.toHomeomorph '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle)).Nonempty
  rw [←Complex.equivRealProdCLM.symm.toHomeomorph.image_interior,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardClosedTriangle_interior]
  exact Set.Nonempty.image _ ⟨(1/3,1/3),by norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.standardOpenTriangle]⟩

/-- The actual boundary double of the original compact physical triangle is genuinely the unit sphere. -/
def finiteTriangleDoubleSphereHomeomorph (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    (finiteTrianglePoincarePairing T).ChamberDouble≃ₜMetric.sphere (0:EuclideanSpace ℝ (Fin 3)) 1 := by
  let E:=(finiteTriangleStandardHomeomorph T).trans standardTriangleComplexHomeomorph
  have hB (p:(finiteTrianglePoincarePolygon T).Point) :
      p.val∈(finiteTrianglePoincarePolygon T).boundary ↔ (E p).val∈frontier standardComplexClosedTriangle:=
    (finiteTriangleStandardHomeomorph_boundary T p).trans
      (standardTriangleComplexHomeomorph_boundary (finiteTriangleStandardHomeomorph T p))
  let h:=standardComplexClosedTriangle_properties
  exact (_root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleCongr E hB).trans
    (_root_.LowDimensionalTopology.Geometry.Surfaces.closedConvexRegionDoubleSphereHomeomorph h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- Genus zero is realized by a genuine sphere homeomorphism of the original actual conformal group orbit space. -/
def finiteTriangleConformalOrbitSphereHomeomorph
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (n : Fin 3→ℕ)
    (hn : ∀i,2≤n i) (hangle : ∀i,finiteTriangleVertexAngle T i=Real.pi/(n i:ℝ)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (triangleConformalGroup T.toClosedHTriangle) ℍ≃ₜ
      Metric.sphere (0:EuclideanSpace ℝ (Fin 3)) 1 :=
  (finiteTriangleConformalOrbitDoubleHomeomorph T n hn hangle).symm.trans
    (finiteTriangleDoubleSphereHomeomorph T)

theorem finiteTriangleConformalOrbit_hasTopologicalGenus_zero
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (n : Fin 3→ℕ)
    (hn : ∀i,2≤n i) (hangle : ∀i,finiteTriangleVertexAngle T i=Real.pi/(n i:ℝ)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (triangleConformalGroup T.toClosedHTriangle) ℍ) 0 :=
  ⟨(finiteTriangleConformalOrbitSphereHomeomorph T n hn hangle).trans
    _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleSurfaceZeroHomeomorph.symm⟩

/-- Every original all-finite reciprocal-angle triangle has its actual conformal orbit surface homeomorphic to the sphere.
The finite model has exactly the same original triangle, rather than merely the same numerical signature. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformalOrbit_hasTopologicalGenus_zero_of_finite_integral
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (p q r : ℕ) (hp : 2≤p) (hq : 2≤q) (hr : 2≤r)
    (ha : T.alpha=Real.pi/(p:ℝ)) (hb : T.beta=Real.pi/(q:ℝ))
    (hc : T.gamma=Real.pi/(r:ℝ)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (triangleConformalGroup T) ℍ) 0 := by
  obtain ⟨U,hU⟩:=positive_angle_closedTriangle_has_finite_model T
    (by rw [ha];positivity) (by rw [hb];positivity) (by rw [hc];positivity)
  let n : Fin 3→ℕ:=![p,q,r]
  have hn : ∀i,2≤n i:=by intro i;fin_cases i <;> assumption
  have hu : ∀i,finiteTriangleVertexAngle U i=Real.pi/(n i:ℝ):=by
    intro i
    fin_cases i
    · exact (U.closed_angles.1.symm.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.alpha hU)).trans ha
    · exact (U.closed_angles.2.1.symm.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.beta hU)).trans hb
    · exact (U.closed_angles.2.2.symm.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.gamma hU)).trans hc
  have h:=finiteTriangleConformalOrbit_hasTopologicalGenus_zero U n hn hu
  rwa [hU] at h

end LowDimensionalTopology.Geometry.Fuchsian
