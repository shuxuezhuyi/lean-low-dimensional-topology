module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneSmoothPeriodMarking
public import LowDimensionalTopology.Geometry.Teichmuller.RealizedBeltrami
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-!
# The original marked-torus period coordinate

The actual period family is required to be a homeomorphism for the existing
coinduced topology of the original marked-surface quotient. This is a concrete
unproved period-classification and topology-compatibility statement.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller Geometry.Teichmuller.GenusOne

/-- The actual period family supplies the original quotient's global period
coordinate, with the specified native coinduced coefficient topology. -/
def OriginalGenusOnePeriodCoordinates (τ₀ : ℍ) : Prop :=
  ∃ E : @Homeomorph ℍ (TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀))
      inferInstance (TeichmullerSpace.beltramiTopology (normalizedClosedTorus τ₀)),
    ∀ σ : ℍ, E σ = normalizedFamilyPoint τ₀ σ

end LowDimensionalTopology.Unproved.Teichmuller
