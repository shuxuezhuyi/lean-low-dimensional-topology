module

public import LowDimensionalTopology.Geometry.Teichmuller.TeichmullerParameterTopology
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeImageTopology

/-!
# The actual quadratic-to-Fricke parameter map

The original book-L1 differential first determines its genuine marked target,
then its literal finite Fricke coordinates. Both injectivity and surjectivity
are retained for this map and the original Teichmuller parameter map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}

/-- The actual book composite from the entire original quadratic unit ball
to the Fricke image of the entire original native marked quotient. -/
def nativeFrickeParameterMap
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (φ : ↥(QuadraticL1.openUnitBall R)) : nativeFrickeImage hA :=
  ⟨finiteFrickeCoordinates hA (TeichmullerSpace.l1ParameterMap R hg hgenus φ),
    ⟨TeichmullerSpace.l1ParameterMap R hg hgenus φ, rfl⟩⟩

/-- The composite retains the literal coordinate vector of the actual marked target. -/
theorem nativeFrickeParameterMap_coe
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (φ : ↥(QuadraticL1.openUnitBall R)) :
    (nativeFrickeParameterMap R hg hgenus hA φ : Fin (6 * g - 6) → ℝ) =
      finiteFrickeCoordinates hA (TeichmullerSpace.l1ParameterMap R hg hgenus φ) := rfl

/-- The zero differential uses the original identity-marked base point. -/
theorem nativeFrickeParameterMap_zero
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (φ : ↥(QuadraticL1.openUnitBall R)) (hφ : φ.val = 0) :
    (nativeFrickeParameterMap R hg hgenus hA φ : Fin (6 * g - 6) → ℝ) =
      finiteFrickeCoordinates hA (TeichmullerSpace.basePoint R) := by
  change finiteFrickeCoordinates hA (TeichmullerSpace.l1ParameterMap R hg hgenus φ) = _
  rw [TeichmullerSpace.l1ParameterMap_zero R hg hgenus φ hφ]

/-- Both original parameter maps are injective, with the existing geometric
coordinate-separation obligations kept explicit. -/
theorem quadraticParameterMaps_injective
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    Function.Injective (TeichmullerSpace.l1ParameterMap R hg hgenus) ∧
      Function.Injective (nativeFrickeParameterMap R hg hgenus hA) := by
  have hT := (TeichmullerSpace.l1ParameterMap_topology R hg hgenus).2
  refine ⟨hT.1, ?_⟩
  intro φ ψ h
  apply hT.1
  apply finiteFrickeCoordinates_injective hA hAlt
  exact congrArg Subtype.val h

/-- Both original parameter maps are surjective onto their entire stated targets. -/
theorem quadraticParameterMaps_surjective
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e) :
    Function.Surjective (TeichmullerSpace.l1ParameterMap R hg hgenus) ∧
      Function.Surjective (nativeFrickeParameterMap R hg hgenus hA) := by
  have hT := (TeichmullerSpace.l1ParameterMap_topology R hg hgenus).2
  refine ⟨hT.2, ?_⟩
  intro v
  obtain ⟨p, hp⟩ := (mem_nativeFrickeImage_iff hA v.val).mp v.property
  obtain ⟨φ, hφ⟩ := hT.2 p
  refine ⟨φ, Subtype.ext ?_⟩
  change finiteFrickeCoordinates hA (TeichmullerSpace.l1ParameterMap R hg hgenus φ) = v.val
  exact (congrArg (finiteFrickeCoordinates hA) hφ).trans hp

end LowDimensionalTopology.Geometry.Teichmuller
