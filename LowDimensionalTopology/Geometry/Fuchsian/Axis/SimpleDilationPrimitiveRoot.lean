module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.PrimitiveAxisIntersection
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.AffineDiscreteGroups
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped OnePoint Pointwise UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine positive dilation has exactly its two original ideal fixed endpoints. -/
theorem stableAxisDilation_fixed_iff (l : ℝ) (hl : 0 < l) (z :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l).val z = z ↔ z = ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∨ z = ∞ := by
  let a : ℂˣ := Units.mk0 ((Real.exp l:ℝ):ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero l))
  have ha : (a:ℂ) ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    change Real.exp l = 1 at hre
    exact (Real.one_lt_exp_iff.mpr hl).ne' hre
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a).val z = z ↔ _
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxis_scaling_eq_standard a ha]
  exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_boundary_fixed_iff a ha z

/-- In the original discrete group the full stabilizers of either endpoint of a dilation coincide. -/
theorem HalfPlaneFuchsianGroup.dilation_endpoint_stabilizers_eq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H (0:ℂ) = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ∞ := by
  ext g
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer]
  constructor
  · rintro ⟨hg,hgz⟩
    exact ⟨hg,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_shared_loxodromic_endpoints H
      P.discrete g (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)
      hg hfH (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic l
        hl).1 (0:ℂ) ∞ (OnePoint.coe_ne_infty _)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero
        _) (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty _) hgz⟩
  · rintro ⟨hg,hgi⟩
    exact ⟨hg,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_shared_loxodromic_endpoints H
      P.discrete g (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)
      hg hfH (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic l
        hl).1 ∞ (0:ℂ) (OnePoint.coe_ne_infty _).symm
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty
        _) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero _) hgi⟩

/-- The full endpoint stabilizer, rather than a possibly proper dilation subgroup, has a positive generator. -/
theorem HalfPlaneFuchsianGroup.dilation_endpoint_positive_generator {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H) :
    ∃ t : ℝ, 0 < t ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H (0:ℂ) = Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation t) := by
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H (0:ℂ)
  have hKle : K ≤ H := by
    intro g hg
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H (0:ℂ) g).mp hg).1
  let dilationEndpointDiscrete : DiscreteTopology H := P.discrete
  have hKd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.subgroup_discrete hKle
  have hfn : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ≠ 1 := (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic l hl).1.1
  have hKne : K ≠ ⊥ := by
    intro he
    have hmem : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ K := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ _ _).mpr ⟨hfH,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero _⟩
    rw [he,Subgroup.mem_bot] at hmem
    exact hfn hmem
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxis_positive_generator K hKd hKne
  intro g hg
  have hg0 := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H (0:ℂ) g).mp hg
  have hgi : g.val ∞ = ∞ := by
    have hgm : g ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ∞ := by
      rw [←P.dilation_endpoint_stabilizers_eq l hl hfH]
      exact hg
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ g).mp hgm).2
  obtain ⟨a,ha⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_fix_zero_infty_eq_scaling g hg0.2 hgi
  obtain ⟨r,hr,har⟩ := scaling_preserves_halfPlane_positive a (ha ▸ P.preserves ⟨g,hg0.1⟩)
  exact ⟨r,hr,ha.trans (congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling har)⟩

/-- The positive generator of the full endpoint stabilizer is genuinely primitive in the whole original group. -/
theorem HalfPlaneFuchsianGroup.dilation_primitive_root_exists {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H) :
    ∃ t : ℝ, 0 < t ∧ IsPrimitive H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation t) := by
  obtain ⟨t,ht,hK⟩ := P.dilation_endpoint_positive_generator l hl hfH
  have htK : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation t ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H (0:ℂ) := by
    rw [hK]
    exact Subgroup.mem_zpowers _
  have htH := ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H (0:ℂ) _).mp htK).1
  refine ⟨t,ht,(primitive_iff_of_hyperbolic
    (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic t ht)).mpr ⟨htH,?_⟩⟩
  intro z hz
  rcases (stableAxisDilation_fixed_iff t ht z).mp hz with rfl | rfl
  · exact hK.symm
  · exact hK.symm.trans (P.dilation_endpoint_stabilizers_eq l hl hfH)

/-- All genuine positive dilations have the same actual three-dimensional geodesic axis. -/
theorem stableAxisDilation_geodesicAxis (l : ℝ) (hl : 0 < l) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusVerticalGeodesic := by
  let a : ℂˣ := Units.mk0 ((Real.exp l:ℝ):ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero l))
  have ha : (a:ℂ) ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    change Real.exp l = 1 at hre
    exact (Real.one_lt_exp_iff.mpr hl).ne' hre
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a) = _
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxis_scaling_eq_standard a
    ha,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis_standard a ha]

/-- Simplicity passes to the actual full-stabilizer primitive root through equality of genuine axes. -/
theorem HalfPlaneFuchsianGroup.simple_dilation_primitive_root_exists {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hs : IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    ∃ t : ℝ, 0 < t ∧ IsPrimitive H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation t) ∧ IsSimple H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation t) := by
  obtain ⟨t,ht,hp⟩ := P.dilation_primitive_root_exists l hl hs.1
  refine ⟨t,ht,hp,hp.mem,_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic t ht,?_⟩
  intro g hg
  rw [stableAxisDilation_geodesicAxis t ht,←stableAxisDilation_geodesicAxis l hl]
  exact hs.2.2 g hg

/-- The source full-axis construction works even when the originally given simple dilation is not primitive. -/
theorem HalfPlaneFuchsianGroup.simple_dilation_intersection_polygon {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hs : IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    letI := P.nativeAction
    ∃ t : ℝ, 0 < t ∧ ∃ D : Set ℍ,
      (D = dilationAxisAnnulus t ∨ D = dihedralAxisRightAnnulus t) ∧
      IsConvexFuchsianPolygon P.cayleyData
        (P.cayleyCoordinate '' (D ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier)) := by
  let nativeSimpleDilationRootPolygonAction := P.nativeAction
  obtain ⟨t,ht,hp,hst⟩ := P.simple_dilation_primitive_root_exists l hl hs
  obtain ⟨D,hcases,hpolygon⟩ := P.primitive_simple_dilation_intersection_polygon t ht hp hst
  exact ⟨t,ht,D,hcases,hpolygon⟩

end LowDimensionalTopology.Geometry.Fuchsian
