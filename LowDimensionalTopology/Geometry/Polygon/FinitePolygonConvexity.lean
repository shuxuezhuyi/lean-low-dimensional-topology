/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonBoundaryConvexity
/-! # Actual finite polygon convexity and the all-right case

For genuine native polygons, convexity reduces to local convexity at the actual
vertices. The angle criterion is proved here for all finite vertices, including
straight angles. In particular every actual all-right polygon is convex. Ideal
vertices in the general angle criterion remain separate.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set Filter
open scoped Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- Every true interior point has a genuine locally convex neighborhood in the actual closed polygon. -/
theorem DiscPolygon.closedCarrier_locallyConvex_at_interior {n : ℕ} (P : DiscPolygon n)
    (p : 𝕔𝔻) (hp : (p : ℂ) ∈ P.complexInterior) :
    ∃ U : Set 𝕔𝔻, IsOpen U ∧ p ∈ U ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscHConvex (P.closedCarrier ∩ U) := by
  have hpK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior := by
    rw [P.klein_image_interior]
    have h := mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph hp
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed] at h
  have hopen := P.klein_jordan_regions.1
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hpK)
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ⁻¹' Metric.ball
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) r,
    Metric.isOpen_ball.preimage _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.continuous,Metric.mem_ball_self hr,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvex_iff_klein_convex,image_inter_preimage]
  have hb : Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) r ⊆ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.closedCarrier := by
    rw [P.closedKlein_image_closedCarrier]
    exact hsub.trans subset_closure
  rw [inter_eq_right.mpr hb]
  exact convex_ball _ _

/-- For actual Jordan polygons every nonvertex case is automatically locally convex. -/
theorem DiscPolygon.isConvex_of_vertices_locallyConvex {n : ℕ} (P : DiscPolygon n)
    (hv : ∀ i : Fin n, ∃ U : Set 𝕔𝔻, IsOpen U ∧ P.vertices i ∈ U ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscHConvex (P.closedCarrier ∩ U)) : P.IsConvex := by
  apply P.isConvex_iff_closedCarrier_locallyConvex.mpr
  intro p hp
  have hpc := mem_image_of_mem ((↑) : 𝕔𝔻 → ℂ) hp
  rw [P.closedCarrier_complex_image,P.closure_complexInterior] at hpc
  rcases hpc with hpi | hpb
  · exact P.closedCarrier_locallyConvex_at_interior p hpi
  · obtain ⟨q,hq,he⟩ := hpb
    have heq : q = p := Complex.UnitClosedDisc.isEmbedding_coe.injective he
    subst q
    obtain ⟨i,hi⟩ := mem_iUnion.mp hq
    by_cases hleft : p = P.vertices i
    · rw [hleft]
      exact hv i
    by_cases hright : p = P.vertices (finRotate n i)
    · rw [hright]
      exact hv (finRotate n i)
    apply P.closedCarrier_locallyConvex_at_edge_interior i p
    apply mem_openSegment_of_ne_left_right
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (Ne.symm hleft))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (Ne.symm hright))
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hi

/-- Genuine finite polygons with actual interior angles at most pi are convex, with straight vertices allowed. -/
theorem DiscPolygon.isConvex_of_finite_angles_le_pi {n : ℕ} (P : DiscPolygon n)
    (hf : ∀ i : Fin n, ‖(P.vertices i : ℂ)‖ < 1) (ha : ∀ i : Fin n, P.angle i ≤ Real.pi) :
    P.IsConvex := by
  apply P.isConvex_of_vertices_locallyConvex
  intro i
  let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.vertices i) (hf i)
  have hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ _).symm
  exact P.closedCarrier_locallyConvex_at_finite_vertex i z hz (ha i)

/-- Every actual vertex of a genuine right-angled polygon is finite; ideal angles are genuinely zero. -/
theorem DiscPolygon.vertices_finite_of_right_angles {n : ℕ} (P : DiscPolygon n)
    (ha : ∀ i : Fin n, P.angle i = Real.pi/2) : ∀ i : Fin n, ‖(P.vertices i : ℂ)‖ < 1 := by
  intro i
  by_contra hn
  have hi : ‖(P.vertices i : ℂ)‖ = 1 := le_antisymm (P.vertices i).norm_le_one (le_of_not_gt hn)
  have h := P.angle_of_ideal i hi
  rw [ha i] at h
  linarith [Real.pi_pos]

/-- Any actual all-right native Jordan polygon is convex, without convexity or support assumptions. -/
theorem DiscPolygon.isConvex_of_right_angles {n : ℕ} (P : DiscPolygon n)
    (ha : ∀ i : Fin n, P.angle i = Real.pi/2) : P.IsConvex := by
  apply P.isConvex_of_finite_angles_le_pi (P.vertices_finite_of_right_angles ha)
  intro i
  rw [ha i]
  linarith [Real.pi_pos]

end
end LowDimensionalTopology.Geometry.Polygon
