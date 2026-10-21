module
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.JordanPolygonRegions
public import LowDimensionalTopology.Geometry.Polygon.DiscPolygonJordan
public import Mathlib.Analysis.Convex.GaugeRescale
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
/-- The actual Euclidean unit circle and the product-norm unit sphere are homeomorphic;
this only changes the source parametrization of an existing Jordan boundary. -/
def circleProdSphereHomeomorph : Circle ≃ₜ Metric.sphere (0 : ℝ×ℝ) 1 := by
  let e := Complex.equivRealProdCLM.toHomeomorph
  let S : Set ℂ := e ⁻¹' Metric.closedBall (0 : ℝ×ℝ) 1
  have hc : Convex ℝ S :=
    (convex_closedBall (0 : ℝ×ℝ) 1).linear_preimage Complex.equivRealProdCLM.toLinearMap
  have hI : interior S = e ⁻¹' Metric.ball (0 : ℝ×ℝ) 1 := by
    change interior (e ⁻¹' Metric.closedBall (0 : ℝ×ℝ) 1) = _
    rw [←e.preimage_interior, interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
  have hne : (interior S).Nonempty := by
    rw [hI]
    exact ⟨0, by simp [e]⟩
  have hb : Bornology.IsBounded S :=
    (e.isCompact_preimage.mpr (isCompact_closedBall (0 : ℝ×ℝ) 1)).isBounded
  let hex := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hb
  let h := Classical.choose hex
  have hF := (Classical.choose_spec hex).2.2
  have hE : e '' frontier S = Metric.sphere (0 : ℝ×ℝ) 1 := by
    change e '' frontier (e ⁻¹' Metric.closedBall (0 : ℝ×ℝ) 1) = _
    rw [←e.preimage_frontier, e.image_preimage,
      frontier_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
  let A : ↥(frontier S) ≃ₜ Metric.sphere (0 : ℂ) 1 :=
    (h.isEmbedding.homeomorphImage (frontier S)).trans (Homeomorph.setCongr hF)
  let B : ↥(frontier S) ≃ₜ Metric.sphere (0 : ℝ×ℝ) 1 :=
    (e.isEmbedding.homeomorphImage (frontier S)).trans (Homeomorph.setCongr hE)
  exact A.symm.trans B

/-- Unboundedness of the literal outside is transported through the actual Euclidean
linear isometry, rather than inferred from an arbitrary homeomorphism. -/
theorem complexJordanOutside_not_isBounded {C : Set ℂ} (hC : IsComplexJordanCurve C) :
    ¬ Bornology.IsBounded (complexJordanOutside C) := by
  intro hb
  have hi := Complex.orthonormalBasisOneI.repr.isometry.lipschitzWith.isBounded_image hb
  apply (Schoenflies.jordan_curve_theorem hC).not_isBounded_outside
  change Bornology.IsBounded
    (complexJordanPlaneHomeomorph '' (complexJordanPlaneHomeomorph ⁻¹'
      Schoenflies.outside (complexJordanPlaneHomeomorph '' C))) at hi
  rwa [complexJordanPlaneHomeomorph.image_preimage] at hi

/-- The original polygon boundary, including ideal vertices, is a genuine complex
Jordan curve for the unconditional separation theorem. -/
theorem discPolygon_isComplexJordanCurve {n : ℕ} (Q : DiscPolygon n) :
    IsComplexJordanCurve Q.complexBoundary := by
  obtain ⟨γ, hc, hi, hr⟩ := Q.exists_jordan_curve
  let e := circleProdSphereHomeomorph
  have hJ := isComplexJordanCurve_of_continuous_injective
    (hc.comp e.continuous) (hi.comp e.injective)
  have he : range (γ ∘ e) = range γ := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact mem_range_self _
    · rintro ⟨w, rfl⟩
      obtain ⟨u, rfl⟩ := e.surjective w
      exact ⟨u, rfl⟩
  rwa [he, hr] at hJ

/-- The polygon interior is the bounded complementary Jordan region, including ideal vertices. -/
theorem discPolygon_complexInterior_eq_jordanInside {n : ℕ} (Q : DiscPolygon n) :
    Q.complexInterior = complexJordanInside Q.complexBoundary := by
  have hJ := discPolygon_isComplexJordanCurve Q
  obtain ⟨hI, hO, hd, hu, _, hOc, _, _⟩ := complexJordan_regions hJ
  exact Q.interior_eq_of_jordan_regions hI hO hd hu hOc
    (complexJordanOutside_not_isBounded hJ)

/-- The polygon exterior is the unbounded complementary Jordan region of its boundary. -/
theorem discPolygon_complexOutside_eq_jordanOutside {n : ℕ} (Q : DiscPolygon n) :
    Q.complexOutside = complexJordanOutside Q.complexBoundary := by
  have hJ := discPolygon_isComplexJordanCurve Q
  obtain ⟨hI, hO, hd, hu, _, hOc, _, _⟩ := complexJordan_regions hJ
  exact Q.outside_eq_of_jordan_regions hI hO hd hu hOc
    (complexJordanOutside_not_isBounded hJ)

end LowDimensionalTopology.Geometry.Polygon
