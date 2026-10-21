module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.NativeAxisStabilizerTransport
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.AxisCosetTileLocalFiniteness
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.AxisStabilizerLocalFiniteness
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

/-- Every actual positive dilation has its native geodesic equal to the genuine imaginary line. -/
theorem dilation_hyperbolic_axis_eq_vertical (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (l : ℝ) (he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 := by
  let L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht
  have hi : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ L.idealEndpoints := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints,he]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty _
  have hz : ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ L.idealEndpoints := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints,he]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero _
  obtain ⟨a,ha⟩ := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.infty_mem_idealEndpoints_iff_vertical L).mp hi
  have ha0 : a = 0 := by
    rw [ha,_root_.LowDimensionalTopology.Geometry.Hyperbolic.vertical_idealEndpoints] at hz
    rcases Set.mem_insert_iff.mp hz with hza | hzi
    · have hza' : (0:ℂ) = (a:ℂ) := OnePoint.coe_injective hza
      have hr := congrArg Complex.re hza'
      simpa only [Complex.zero_re,Complex.ofReal_re] using hr.symm
    · exact (OnePoint.coe_ne_infty (0:ℂ) hzi).elim
  exact ha.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical ha0)

/-- For a genuine primitive simple dilation, the full-group intersection polygon is constructed with no prior domain or normal-form hypothesis. -/
theorem HalfPlaneFuchsianGroup.primitive_simple_dilation_intersection_polygon
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (l : ℝ) (hl : 0 < l) (hp : IsPrimitive H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l))
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    letI := P.nativeAction
    ∃ D : Set ℍ, (D = dilationAxisAnnulus l ∨ D = dihedralAxisRightAnnulus l) ∧
      IsConvexFuchsianPolygon P.cayleyData
        (P.cayleyCoordinate '' (D ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier)) := by
  let nativePrimitiveSimpleDilationPolygonAction := P.nativeAction
  obtain ⟨A,hA⟩ := mobius_preserves_halfPlane_exists_SL (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) (P.preserves ⟨_,hp.mem⟩)
  have hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by rw [hA];exact _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic l hl
  have hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1 := hh.1.1
  have ht : 4 < (Matrix.trace A.val)^2 := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff
    A hf).mp hh
  have hL := dilation_hyperbolic_axis_eq_vertical A hf ht l hA
  have hsA : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by rw [hA];exact hs
  obtain ⟨D,hD,hconv,hcases,hfinite⟩ := P.primitive_dilation_axis_locallyFinite_fundamental l hl hp
  have hD' := P.nativeAxis_fundamental_relabel hD
  have hf' := P.nativeAxis_compact_hits_relabel D hfinite
  rw [P.nativeAxisStabilizer_eq,←hL] at hD' hf'
  refine ⟨D,hcases,?_⟩
  have hpD := P.simple_axis_intersection_polygon A hf ht hsA D hconv hD' hf'
  simpa only [hL] using hpD

end LowDimensionalTopology.Geometry.Fuchsian
