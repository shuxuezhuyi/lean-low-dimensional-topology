module
public import LowDimensionalTopology.Geometry.Surfaces.Covering.StandardCoverClassification
@[expose] public section
noncomputable section
open Set Module
namespace LowDimensionalTopology.Geometry.Surfaces

/-- Every complex set containing the punctured plane is noncompact in the original topology. -/
theorem complex_superset_punctured_not_isCompact (S : Set ℂ) (hS : {z : ℂ | z ≠ 0} ⊆ S) :
    ¬IsCompact S := by
  intro hc
  obtain ⟨B, hB⟩ := hc.bddAbove_image continuous_norm.continuousOn
  let r : ℝ := max B 0 + 1
  have hr : 0 < r := by dsimp [r]; linarith [le_max_right B 0]
  have hz : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hb : ‖(r : ℂ)‖ ≤ B := hB ⟨(r : ℂ), hS hz, rfl⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hb
  dsimp [r] at hb
  linarith [le_max_left B 0]

theorem not_compactSpace_complexPlane : ¬CompactSpace ℂ := by
  intro hc
  let : CompactSpace ℂ := hc
  exact complex_superset_punctured_not_isCompact Set.univ (Set.subset_univ _) isCompact_univ

theorem not_compactSpace_puncturedPlane : ¬CompactSpace {z : ℂ // z ≠ 0} := by
  intro hc
  let : CompactSpace {z : ℂ // z ≠ 0} := hc
  have h : IsCompact ({z : ℂ | z ≠ 0}) := by
    have hr : Set.range (Subtype.val : {z : ℂ // z ≠ 0} → ℂ) = {z : ℂ | z ≠ 0} := by
      ext z
      constructor
      · rintro ⟨v, rfl⟩
        exact v.property
      · intro hz
        exact ⟨⟨z, hz⟩, rfl⟩
    rw [← hr]
    exact isCompact_range (continuous_subtype_val : Continuous (Subtype.val : {z : ℂ // z ≠ 0} → ℂ))
  exact complex_superset_punctured_not_isCompact _ Subset.rfl h

/-- A compact Riemann surface cannot be conformally the standard complex plane. -/
theorem RiemannConformallyEquivalent.not_plane_of_compact {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (R : RiemannSurface X) :
    ¬RiemannConformallyEquivalent R complexPlaneRiemannSurface := by
  rintro ⟨f, hf, hbij⟩
  exact not_compactSpace_complexPlane (Function.Surjective.compactSpace hf.continuous hbij.2)

/-- A compact Riemann surface cannot be conformally the punctured complex plane. -/
theorem RiemannConformallyEquivalent.not_puncturedPlane_of_compact {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (R : RiemannSurface X) :
    ¬RiemannConformallyEquivalent R puncturedPlaneRiemannSurface := by
  rintro ⟨f, hf, hbij⟩
  exact not_compactSpace_puncturedPlane (Function.Surjective.compactSpace hf.continuous hbij.2)

/-- The genuine topological torus carrier is compact. -/
theorem complexTorusCarrier_compact : CompactSpace ComplexTorusCarrier := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  infer_instance

/-- A compact surface with an actual analytic plane cover has a genuine flat complex-torus
model. This does not define or assume the genus. -/
theorem riemannSurface_compact_planeCover_torus {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (R : RiemannSurface X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas R.toRiemannAtlas p)
    (hs : Function.Surjective p) :
    ∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b, RiemannConformallyEquivalent R T.surface := by
  rcases riemannSurface_planeCover_conformal_classification R p hp ha hs with h | h | h
  · exact ((_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.not_plane_of_compact R) h).elim
  · exact ((_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.not_puncturedPlane_of_compact
    R) h).elim
  · exact h

/-- The plane alternative of the genuinely constructed universal cover is a flat complex
 torus for every compact base, independently of the still separate uniformization theorem. -/
theorem RiemannUniversalCover.compact_plane_model_torus {X : Type*}
    [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X} (C : RiemannUniversalCover R)
    (hc : @RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface complexPlaneRiemannSurface) :
    ∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b, RiemannConformallyEquivalent R T.surface := by
  rcases C.plane_model_conformal_classification hc with h | h | h
  · exact ((_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.not_plane_of_compact R) h).elim
  · exact ((_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.not_puncturedPlane_of_compact
    R) h).elim
  · exact h

/-- Among actual analytic plane-cover bases, compactness is exactly the flat complex-torus
alternative of the proved quotient classification. -/
theorem riemannSurface_planeCover_compact_iff_torus {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas R.toRiemannAtlas p)
    (hs : Function.Surjective p) :
    CompactSpace X ↔ ∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b,
      RiemannConformallyEquivalent R T.surface := by
  constructor
  · intro hX
    let : CompactSpace X := hX
    exact riemannSurface_compact_planeCover_torus R p hp ha hs
  · rintro ⟨b, T, f, hf, hbij⟩
    let : CompactSpace ComplexTorusCarrier := complexTorusCarrier_compact
    exact (hf.toHomeomorph hbij).symm.compactSpace

end LowDimensionalTopology.Geometry.Surfaces
