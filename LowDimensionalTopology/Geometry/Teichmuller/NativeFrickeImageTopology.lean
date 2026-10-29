module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalGlobalFricke
public import Mathlib.Topology.Homeomorph.Lemmas

/-! The book's Fricke image and coordinate-induced topology on the original
native marked quotient. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation
variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}

/-- The actual Fricke space is the image of the entire original marked quotient. -/
def nativeFrickeImage
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e) :
    Set (Fin (6 * g - 6) → ℝ) :=
  Set.range (finiteFrickeCoordinates hA)

/-- Membership retains exactly an original native marked class as its witness. -/
theorem mem_nativeFrickeImage_iff
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (v : Fin (6 * g - 6) → ℝ) :
    v ∈ nativeFrickeImage hA ↔
      ∃ p : TeichmullerSpace.{0, 0} R, finiteFrickeCoordinates hA p = v := Iff.rfl

/-- The book topology is literally induced by its actual finite coordinates.
This named topology is installed locally by its consumers. -/
@[instance_reducible]
def nativeFrickeTopology
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e) :
    TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
  TopologicalSpace.induced (finiteFrickeCoordinates hA) inferInstance

/-- The explicit open sets of the coordinate-induced topology. -/
theorem nativeFrickeTopology_isOpen_iff
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (U : Set (TeichmullerSpace.{0, 0} R)) :
    IsOpen[nativeFrickeTopology hA] U ↔
      ∃ V : Set (Fin (6 * g - 6) → ℝ),
        IsOpen V ∧ (finiteFrickeCoordinates hA) ⁻¹' V = U := Iff.rfl

/-- With the existing concrete axis obligations, the actual coordinates embed
the native quotient with precisely the named book topology. -/
theorem nativeFricke_isEmbedding
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    letI := nativeFrickeTopology hA
    IsEmbedding (finiteFrickeCoordinates hA) := by
  let := nativeFrickeTopology hA
  exact IsEmbedding.induced (finiteFrickeCoordinates_injective hA hAlt)

/-- The literal coordinates identify the original native quotient with the
Fricke image carrying its actual Euclidean subspace topology. -/
def nativeFrickeHomeomorph
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    letI := nativeFrickeTopology hA
    TeichmullerSpace.{0, 0} R ≃ₜ nativeFrickeImage hA := by
  letI := nativeFrickeTopology hA
  exact (nativeFricke_isEmbedding hA hAlt).toHomeomorph

/-- The homeomorphism uses the same literal finite coordinate vector. -/
theorem nativeFrickeHomeomorph_apply
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (p : TeichmullerSpace.{0, 0} R) :
    ((nativeFrickeHomeomorph hA hAlt p : nativeFrickeImage hA) :
      Fin (6 * g - 6) → ℝ) = finiteFrickeCoordinates hA p := rfl

end LowDimensionalTopology.Geometry.Teichmuller
