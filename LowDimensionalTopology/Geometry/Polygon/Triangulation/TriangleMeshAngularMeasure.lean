module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.PlaneSeparation
public import LowDimensionalTopology.Geometry.Polygon.Area.PolygonMeshArea
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.FiniteIdealTriangleAdapters

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Polygon
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc ENNReal Classical
noncomputable section

/-- The genuine finite part of a compactified geodesic triangle. -/
def _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : Set 𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ⁻¹' T.closedCarrier

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier_eq_closure (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    T.finiteCarrier = closure T.interior := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier,
    T.closedCarrier_eq_closedModelClosure]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRelativeClosure_eq_preimage T.interior).symm

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier_isClosed (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    IsClosed T.finiteCarrier := by
  rw [T.finiteCarrier_eq_closure]
  exact isClosed_closure

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier_hConvex (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex T.finiteCarrier :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvexHull_convex {T.a,T.b,T.c}).disc_preimage

theorem DiscPolygon.meshTriangle_finiteCarrier_cover {n : ℕ} (P : DiscPolygon n) :
    (⋃ t : P.kleinTriangleMesh.Triangle, (P.meshTriangle t).finiteCarrier) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ⁻¹' P.closedCarrier := by
  ext z
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.finiteCarrier, Set.mem_iUnion,
    mem_preimage]
  rw [P.closedCarrier_eq_iUnion_meshTriangles]
  simp only [Set.mem_iUnion]

theorem DiscPolygon.meshTriangle_interior_pairwise_disjoint {n : ℕ} (P : DiscPolygon n) :
    Pairwise (fun t u : P.kleinTriangleMesh.Triangle =>
      Disjoint (P.meshTriangle t).interior (P.meshTriangle u).interior) := by
  intro t u htu
  apply Set.disjoint_left.mpr
  intro z hzt hzu
  apply Set.disjoint_left.mp (P.meshTriangle_halfPlaneInterior_pairwise_disjoint htu)
  · rw [← (P.meshTriangle t).discToHalfPlane_image_interior]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane hzt
  · rw [← (P.meshTriangle u).discToHalfPlane_image_interior]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane hzu

/-- All sufficiently close points avoid every nonincident face of the actual finite mesh. -/
theorem DiscPolygon.meshTriangle_nonincident_eventually {n : ℕ} (P : DiscPolygon n) (z : 𝔻) :
    ∀ᶠ w in 𝓝 z, ∀ t : P.kleinTriangleMesh.Triangle,
      z ∉ (P.meshTriangle t).finiteCarrier → w ∉ (P.meshTriangle t).finiteCarrier := by
  have hl : LocallyFinite (fun t : P.kleinTriangleMesh.Triangle =>
      (P.meshTriangle t).finiteCarrier) := locallyFinite_of_finite _
  filter_upwards [hl.iInter_compl_mem_nhds
    (fun t => (P.meshTriangle t).finiteCarrier_isClosed) z] with w hw t ht
  exact mem_iInter₂.mp hw t ht

/-- At every true polygon interior point the incident actual faces fill a neighborhood. -/
theorem DiscPolygon.meshTriangle_incident_cover_nhds {n : ℕ} (P : DiscPolygon n)
    {z : 𝔻} (hz : z ∈ P.interior) :
    (⋃ t ∈ {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier},
      (P.meshTriangle t).finiteCarrier) ∈ 𝓝 z := by
  filter_upwards [P.meshTriangle_nonincident_eventually z,
    P.interior_isOpen.mem_nhds hz] with w hw hwP
  have hwClosed : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w ∈ P.closedCarrier :=
    subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel hwP)
  change w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ⁻¹' P.closedCarrier at hwClosed
  rw [← P.meshTriangle_finiteCarrier_cover] at hwClosed
  obtain ⟨t, hwt⟩ := mem_iUnion.mp hwClosed
  have hzt : z ∈ (P.meshTriangle t).finiteCarrier := by
    by_contra hn
    exact hw t hn hwt
  exact mem_iUnion₂.mpr ⟨t, hzt, hwt⟩

/-- A local closed cover suffices to fill the unit tangent circle at its incident members. -/
theorem discRadialDirections_incident_cover_of_mem_nhds {ι : Type*}
    (S : ι → Set 𝔻) (hl : LocallyFinite S) (hc : ∀ i, IsClosed (S i))
    (hcov : (⋃ i, S i) ∈ 𝓝 (0 : 𝔻)) :
    (⋃ i ∈ {i | (0 : 𝔻) ∈ S i}, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (S i)) = univ := by
  apply eq_univ_of_forall
  intro u
  have hN := hl.iInter_compl_mem_nhds hc (0 : 𝔻)
  obtain ⟨n, hn, hp⟩ := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.tendsto_discRadialTestPoint u).eventually
    (inter_mem hN hcov)).exists
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  have h0 : (0 : 𝔻) ∈ S i := by
    by_contra hz
    exact (mem_iInter₂.mp hn i hz) hi
  exact mem_iUnion₂.mpr ⟨i, h0, ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialTestRadius n, hi⟩⟩

/-- True normalized triangle sectors overlap in only angular-null boundary directions. -/
theorem DiscPolygon.meshTriangle_directions_pairwise_null {n : ℕ} (P : DiscPolygon n)
    (z : 𝔻) {t u : P.kleinTriangleMesh.Triangle}
    (hzt : z ∈ (P.meshTriangle t).finiteCarrier)
    (hzu : z ∈ (P.meshTriangle u).finiteCarrier) (htu : t ≠ u) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z '' (P.meshTriangle t).finiteCarrier) ∩
       _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z '' (P.meshTriangle u).finiteCarrier)) = 0 := by
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z
  have hEq (v : P.kleinTriangleMesh.Triangle) :
      F '' (P.meshTriangle v).finiteCarrier = closure (F '' (P.meshTriangle v).interior) := by
    rw [(P.meshTriangle v).finiteCarrier_eq_closure, F.image_closure]
  rw [hEq t, hEq u]
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_discRadialDirections_common_closures
    ((P.meshTriangle t).interior_discHConvex.isometry_image
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z))
    (F.isOpenMap _ (P.meshTriangle t).interior_isOpen)
    ((P.meshTriangle t).interior_nonempty.image F)
    ((P.meshTriangle u).interior_discHConvex.isometry_image
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z))
    (F.isOpenMap _ (P.meshTriangle u).interior_isOpen)
    ((P.meshTriangle u).interior_nonempty.image F)
    ((P.meshTriangle_interior_pairwise_disjoint htu).image F.injective.injOn
      (subset_univ _) (subset_univ _)) ?_ ?_).measure_zero _
  · rw [← hEq t]
    exact ⟨z, hzt, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z⟩
  · rw [← hEq u]
    exact ⟨z, hzu, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z⟩

/-- The genuine incident triangle stars fill every direction at an actual polygon interior point. -/
theorem DiscPolygon.meshTriangle_directions_cover {n : ℕ} (P : DiscPolygon n)
    {z : 𝔻} (hz : z ∈ P.interior) :
    (⋃ t ∈ {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier},
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z '' (P.meshTriangle t).finiteCarrier)) = univ := by
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z
  have hc : ∀ t : P.kleinTriangleMesh.Triangle,
      IsClosed (F '' (P.meshTriangle t).finiteCarrier) :=
    fun t => F.isClosedMap _ (P.meshTriangle t).finiteCarrier_isClosed
  have hcov : (⋃ t : P.kleinTriangleMesh.Triangle,
      (P.meshTriangle t).finiteCarrier) ∈ 𝓝 z := by
    filter_upwards [P.interior_isOpen.mem_nhds hz] with w hw
    rw [P.meshTriangle_finiteCarrier_cover]
    exact subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel hw)
  have hFcov := F.isOpenMap.image_mem_nhds hcov
  change F '' (⋃ t : P.kleinTriangleMesh.Triangle, (P.meshTriangle t).finiteCarrier) ∈ 𝓝 (F z) at hFcov
  rw [show F z = 0 from _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z,
    image_iUnion] at hFcov
  have he (t : P.kleinTriangleMesh.Triangle) :
      (0 : 𝔻) ∈ F '' (P.meshTriangle t).finiteCarrier ↔
        z ∈ (P.meshTriangle t).finiteCarrier := by
    constructor
    · rintro ⟨w, hw, he⟩
      have hwz : w = z := F.injective (he.trans
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z).symm)
      exact hwz ▸ hw
    · exact fun hw => ⟨z, hw, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z⟩
  have hd := discRadialDirections_incident_cover_of_mem_nhds
    (fun t : P.kleinTriangleMesh.Triangle => F '' (P.meshTriangle t).finiteCarrier)
    (locallyFinite_of_finite _) hc hFcov
  simpa only [he, mem_ofPred_eq, F] using hd

/-- Exact actual angular probability additivity for all incident faces of the derived finite mesh. -/
theorem DiscPolygon.meshTriangle_angularFraction_sum {n : ℕ} (P : DiscPolygon n)
    {z : 𝔻} (hz : z ∈ P.interior) :
    ∑ t ∈ Finset.univ.filter (fun t : P.kleinTriangleMesh.Triangle =>
      z ∈ (P.meshTriangle t).finiteCarrier),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction (P.meshTriangle t).finiteCarrier z = 1 := by
  classical
  let s := Finset.univ.filter (fun t : P.kleinTriangleMesh.Triangle =>
      z ∈ (P.meshTriangle t).finiteCarrier)
  have hm := measure_biUnion_finset₀ (μ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure) (s
    := s)
    (f := fun t => _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z '' (P.meshTriangle t).finiteCarrier))
    (fun t ht u hu htu => P.meshTriangle_directions_pairwise_null z
      (by simpa [s] using ht) (by simpa [s] using hu) htu)
    (fun t ht => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.measurableSet_discRadialDirections
      ((P.meshTriangle t).finiteCarrier_hConvex.isometry_image
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z))
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z).isClosedMap _ (P.meshTriangle
        t).finiteCarrier_isClosed)
      ⟨z, by simpa [s] using ht, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z⟩).nullMeasurableSet)
  have hu : (⋃ t ∈ s,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z '' (P.meshTriangle t).finiteCarrier)) = univ := by
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, mem_ofPred_eq] using
      P.meshTriangle_directions_cover hz
  rw [hu, _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_univ] at hm
  exact hm.symm

end
end LowDimensionalTopology.Geometry.Polygon
