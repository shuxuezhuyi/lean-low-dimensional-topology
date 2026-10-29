module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOnePeriodBeltramiDerivative

/-!
# The original torus integral of the actual period-family directions

The original atlas tensors are integrated against the same existing
normalized torus measure. Their actual cover representatives supply both
coefficient identifications internally.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne

/-- The actual infinitesimal marking tensors give the normalized Hermitian
coefficient in the original torus integral. -/
theorem torusAtlasBeltramiPairing_periodTangentBeltrami (τ : ℍ) (u v : ℂ) :
    torusAtlasBeltramiPairing τ
      (BeltramiDifferential.toTensor (u • periodTangentBeltrami τ))
      (BeltramiDifferential.toTensor (v • periodTangentBeltrami τ)) =
        ((1 / (4 * τ.im ^ 2) : ℝ) : ℂ) * u * conj v := by
  have hcover (a : ℂ) (z : ℂ) :
      torusCoverBeltramiValue τ
        (BeltramiDifferential.toTensor (a • periodTangentBeltrami τ)) z =
          a * tangentBeltrami τ := by
    have hT : BeltramiDifferential.toTensor (a • periodTangentBeltrami τ) =
        a • BeltramiDifferential.toTensor (periodTangentBeltrami τ) := by
      apply BeltramiDifferential.ext
      intro e w
      rfl
    rw [hT, torusCoverBeltramiValue_smul,
      torusCoverBeltramiValue_periodTangentBeltrami]
  exact torusAtlasBeltramiPairing_eq τ _ _ u v (hcover u) (hcover v)

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
