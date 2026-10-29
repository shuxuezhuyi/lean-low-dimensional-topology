module

public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.NormalizedTorusBasis
public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.NormalizedTorusLattice
public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.TorusAffineDescent

/-!
# Classification of actual normalized complex torus models

This combines actual analytic affine lift/descent with the complete arithmetic
classification of the integer spans of 1 and τ. The models carry their genuine
analytic plane coverings and exact fibres, as required by ComplexTorusModel.
No ordered topological marking is introduced.
-/

@[expose] public section
noncomputable section

namespace LowDimensionalTopology.Geometry.Surfaces

/-- For any actual native models of the normalized lattices, biholomorphic
equivalence is exactly the SL(2,Z) orbit of the upper-half-plane parameter. -/
theorem ComplexTorusModel.normalized_conformallyEquivalent_iff_modular
    (τ σ : UpperHalfPlane)
    (T : ComplexTorusModel (normalizedTorusBasis τ))
    (U : ComplexTorusModel (normalizedTorusBasis σ)) :
    RiemannConformallyEquivalent T.surface U.surface ↔
      ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℤ, M • τ = σ := by
  rw [T.conformallyEquivalent_iff_scales_period_lattice U]
  simpa only [normalizedPeriodLattice, normalizedTorusBasis_span] using
    normalizedPeriodLattice_scale_iff_modular τ σ

end LowDimensionalTopology.Geometry.Surfaces
