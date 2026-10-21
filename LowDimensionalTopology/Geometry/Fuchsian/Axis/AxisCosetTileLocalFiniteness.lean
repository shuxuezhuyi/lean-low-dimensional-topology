module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.TranslatedSubsets
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.SimpleAxisDirichletRegions
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CosetFundamentalDomains
public import Mathlib.Data.Set.Finite.Lattice
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Pointwise Topology UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Finitely many translates of `S` and locally finite stabilizer tiles give finitely many group labels. -/
theorem axis_coset_tiles_compact_hits_finite {G X : Type*} [Group G]
    [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
    (S D E B : Set X) (hB : IsCompact B)
    (hK : ∀ C : Set X, IsCompact C →
      {k : MulAction.stabilizer G S | (k • closure D ∩ C).Nonempty}.Finite)
    (haxes : ((fun g : G => g • S) '' {g : G | (g • closure (D ∩ E) ∩ B).Nonempty}).Finite) :
    {g : G | (g • closure (D ∩ E) ∩ B).Nonempty}.Finite := by
  apply Set.Finite.of_finite_fibers (fun g : G => g • S) haxes
  rintro T ⟨r,hr,rfl⟩
  have hC : IsCompact (r⁻¹ • B) := hB.image (continuous_const_smul r⁻¹)
  have hfin := (hK (r⁻¹ • B) hC).image (fun k : MulAction.stabilizer G S => r*k.val)
  apply hfin.subset
  rintro g ⟨hg,hgs⟩
  have he : g • S = r • S := hgs
  have hk : r⁻¹*g ∈ MulAction.stabilizer G S := by
    change (r⁻¹*g) • S = S
    rw [mul_smul,he,inv_smul_smul]
  let k : MulAction.stabilizer G S := ⟨r⁻¹*g,hk⟩
  refine ⟨k,?_,?_⟩
  · obtain ⟨x,⟨y,hy,hxy⟩,hxB⟩ := hg
    refine ⟨r⁻¹ • x,⟨y,closure_mono inter_subset_left hy,?_⟩,mem_smul_set.mpr ⟨x,hxB,rfl⟩⟩
    change g • y = x at hxy
    change (r⁻¹*g) • y = r⁻¹ • x
    rw [mul_smul,hxy]
  · change r*(r⁻¹*g) = g
    simp

/-- Nearest-axis comparisons bound the translates of `S` whose closed intersection tiles meet a compact set. -/
theorem axis_coset_tiles_axes_compact_finite {G X : Type*} [Group G]
    [MetricSpace X] [MulAction G X] [IsIsometricSMul G X]
    (S D E B : Set X) (hB : IsCompact B) (a : X)
    (haxes : ∀ R : ℝ, {T | T ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.translatedSubsetFamily (G :=
      G) S ∧ Metric.infDist a T ≤ R}.Finite)
    (hweak : ∀ x ∈ closure E, ∀ g : G, Metric.infDist x S ≤ Metric.infDist x (g • S)) :
    ((fun g : G => g • S) '' {g : G | (g • closure (D ∩ E) ∩ B).Nonempty}).Finite := by
  obtain ⟨R,hR⟩ := hB.bddAbove_image
    (((continuous_id.dist continuous_const).add
      (Metric.continuous_infDist_pt S)).continuousOn)
  apply (haxes R).subset
  rintro T ⟨g,⟨x,⟨y,hy,hxy⟩,hxB⟩,rfl⟩
  refine ⟨⟨g,rfl⟩,?_⟩
  have hw := hweak y (closure_mono inter_subset_right hy) g⁻¹
  have hleft : Metric.infDist (g • y) (g • S) = Metric.infDist y S :=
    Metric.infDist_image (isometry_smul X g)
  have hright : Metric.infDist (g • y) S = Metric.infDist y (g⁻¹ • S) := by
    have hh : g • (g⁻¹ • S) = S := smul_inv_smul g S
    calc
      Metric.infDist (g • y) S = Metric.infDist (g • y) (g • (g⁻¹ • S)) := congrArg (Metric.infDist (g • y)) hh.symm
      _ = Metric.infDist y (g⁻¹ • S) := Metric.infDist_image (isometry_smul X g)
  have hnear : Metric.infDist x (g • S) ≤ Metric.infDist x S := by
    rw [←hxy,hleft,hright]
    exact hw
  have hbase := Metric.infDist_le_infDist_add_dist (x := a) (y := x) (s := g • S)
  have hb := hR (mem_image_of_mem (fun x : X => dist x a+Metric.infDist x S) hxB)
  rw [dist_comm a x] at hbase
  linarith

/-- Compact-hit finiteness of intersection tiles follows from nearest-axis and stabilizer bounds. -/
theorem axis_coset_intersection_compact_hits_finite {G X : Type*} [Group G]
    [MetricSpace X] [MulAction G X] [IsIsometricSMul G X]
    (S D E B : Set X) (hB : IsCompact B) (a : X)
    (hK : ∀ C : Set X, IsCompact C →
      {k : MulAction.stabilizer G S | (k • closure D ∩ C).Nonempty}.Finite)
    (haxes : ∀ R : ℝ, {T | T ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.translatedSubsetFamily (G :=
      G) S ∧ Metric.infDist a T ≤ R}.Finite)
    (hweak : ∀ x ∈ closure E, ∀ g : G, Metric.infDist x S ≤ Metric.infDist x (g • S)) :
    {g : G | (g • closure (D ∩ E) ∩ B).Nonempty}.Finite :=
  axis_coset_tiles_compact_hits_finite S D E B hB hK
    (axis_coset_tiles_axes_compact_finite S D E B hB a haxes hweak)

/-- The intersection of a stabilizer tile and its axis Voronoi region has finitely many compact hits. -/
theorem HalfPlaneFuchsianGroup.simple_axis_intersection_compact_hits_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠
      1)
    (ht : 4 < (Matrix.trace A.val)^2) (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A))
    (D : Set ℍ)
    (hD : letI := P.nativeAction
      ∀ C : Set ℍ, IsCompact C →
        {k : MulAction.stabilizer H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier
          |
          (k • closure D ∩ C).Nonempty}.Finite)
    (B : Set ℍ) (hB : IsCompact B) :
    letI := P.nativeAction
    {g : H | (g • closure (D ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier) ∩ B).Nonempty}.Finite := by
  let nativeSimpleIntersectionHitsAction := P.nativeAction
  let nativeSimpleIntersectionIsometric : IsIsometricSMul H ℍ := ⟨fun g => (P.nativeHom g).isometry⟩
  apply axis_coset_intersection_compact_hits_finite _ D _ B hB UpperHalfPlane.I hD
    (P.hyperbolic_axis_translates_distance_finite A hs.1 hf ht UpperHalfPlane.I)
  intro x hx g
  rw [P.closure_simple_axisVoronoi A hf ht hs] at hx
  exact hx g

/-- Intersecting a full-axis-stabilizer polygon with its Voronoi region gives a convex Fuchsian polygon. -/
theorem HalfPlaneFuchsianGroup.simple_axis_intersection_polygon
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠
      1)
    (ht : 4 < (Matrix.trace A.val)^2) (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A))
    (D : Set ℍ) (hconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex D)
    (hD : letI := P.nativeAction
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (MulAction.stabilizer H
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier) ℍ volume D)
    (hDfinite : letI := P.nativeAction
      ∀ C : Set ℍ, IsCompact C →
        {k : MulAction.stabilizer H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier
          |
          (k • closure D ∩ C).Nonempty}.Finite) :
    letI := P.nativeAction
    IsConvexFuchsianPolygon P.cayleyData
      (P.cayleyCoordinate '' (D ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier)) := by
  let nativeSimpleIntersectionPolygonAction := P.nativeAction
  let nativeSimpleIntersectionPolygonContinuous : ContinuousConstSMul H ℍ :=
    ⟨fun g => (P.nativeHom g).continuous⟩
  let K := MulAction.stabilizer H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier
  let S := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G :=
    H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier
  have hlf : LocallyFinite (fun k : K => k • closure D) := by
    intro x
    obtain ⟨C,hC,hxC⟩ := exists_compact_mem_nhds x
    exact ⟨C,hxC,hDfinite C hC⟩
  have hcs : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S := P.simple_axisVoronoi_hConvex A hf ht hs
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (D ∩ S) := by
    intro x hx y hy z hz
    exact ⟨hconv x hx.1 y hy.1 hz,hcs x hx.2 y hy.2 hz⟩
  have hfD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume (D ∩ S) :=
    coset_intersection_fundamental K volume D S hD hlf
      (P.hyperbolic_axisVoronoi_isOpen A hs.1 hf ht)
      (P.simple_axisVoronoi_coset_stable A hf ht)
      (P.simple_axisVoronoi_closure_meetsEveryOrbit A hf ht hs)
      hc.isPreconnected (parabolicFord_hConvex_frontier_volume_zero hc)
  exact P.cayley_polygon hfD hc (P.simple_axis_intersection_compact_hits_finite A hf ht hs D hDfinite)

end LowDimensionalTopology.Geometry.Fuchsian
