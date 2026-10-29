module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOnePeriodBeltramiDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneUnitAreaFlatQuadratic

/-!
# The actual period derivative and the original flat harmonic relation

The actual infinitesimal tensor has the conjugate-quadratic relation on the
original torus cover. Under the explicit dz-descent premise the quadratic is
an actual global holomorphic tensor, and the density comes from the original
native unit-area flat quadratic metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

/-- The actual infinitesimal tensor has the flat harmonic cover relation. -/
theorem torusCover_periodTangentBeltrami_flatHarmonic (τ : ℍ) (u z : ℂ) :
    torusCoverBeltramiValue τ
      (BeltramiDifferential.toTensor (u • periodTangentBeltrami τ)) z =
        conj (flatHarmonicQuadraticCoverCoefficient τ u) /
          ((normalizedTorusFlatDensity τ ^ 2 : ℝ) : ℂ) := by
  have hT : BeltramiDifferential.toTensor (u • periodTangentBeltrami τ) =
      u • BeltramiDifferential.toTensor (periodTangentBeltrami τ) := by
    apply BeltramiDifferential.ext
    intro e w
    rfl
  rw [hT, torusCoverBeltramiValue_smul,
    torusCoverBeltramiValue_periodTangentBeltrami]
  exact tangentBeltrami_eq_flatHarmonicCoverCoefficient τ u

/-- The flat harmonic expression uses a genuine global native quadratic and
the actual original flat metric density, with the existing descent premise. -/
theorem periodTangentBeltrami_descendedQuadratic_coverRelation (τ : ℍ)
    (hDz : Unproved.Teichmuller.NormalizedTorusDzDescent τ) (u : ℂ) :
    letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
    ∃ q : HolomorphicQuadraticDifferential
        (normalizedTorusModel τ).surface.toRiemannAtlas,
      ∀ z : ℂ,
        torusCoverBeltramiValue τ
          (BeltramiDifferential.toTensor (u • periodTangentBeltrami τ)) z =
          conj ((q : ComplexTorusCarrier → ℂ → ℂ)
            ((normalizedTorusModel τ).projection z)
            ((chartAt ℂ ((normalizedTorusModel τ).projection z))
              ((normalizedTorusModel τ).projection z)) *
            deriv ((chartAt ℂ ((normalizedTorusModel τ).projection z)) ∘
              (normalizedTorusModel τ).projection) z ^ 2) /
            ((descendedFlatCoverDensity τ hDz z : ℝ) : ℂ) := by
  let := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
  refine ⟨descendedFlatQuadratic τ hDz (flatHarmonicQuadraticCoverCoefficient τ u), ?_⟩
  intro z
  have hq := descendedFlatQuadratic_cover τ hDz
    (flatHarmonicQuadraticCoverCoefficient τ u)
    ((normalizedTorusModel τ).projection z) z
    (mem_chart_source ℂ ((normalizedTorusModel τ).projection z))
  rw [hq, descendedFlatCoverDensity_eq, ← normalizedTorusFlatDensity_sq]
  exact torusCover_periodTangentBeltrami_flatHarmonic τ u z

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
