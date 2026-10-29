module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Teichmuller.EssentialMarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeImageTopology

/-! The marked length function on the literal finite Fricke image. The existing
normalized-model availability and axis-alternation premises remain explicit. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

/-- The geodesic length of a fixed original loop, on the entire literal Fricke
image, using exactly the inverse of the existing native Fricke homeomorphism. -/
def frickeGeodesicLength (α : LiZhongQC.Loop X) : nativeFrickeImage hA → ℝ :=
  letI := nativeFrickeTopology hA
  markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α ∘
    (nativeFrickeHomeomorph hA hAlt).symm

/-- At the original finite coordinate vector of an actual marked target, the
Fricke function is its original native marked-class length. -/
theorem frickeGeodesicLength_coordinates (α : LiZhongQC.Loop X)
    (m : MarkedRiemannSurface.{0, 0} R) :
    frickeGeodesicLength R hg hgenus hA hAlt α
      ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ =
      markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α (TeichmullerSpace.mk m) := by
  let := nativeFrickeTopology hA
  have hcoord : (⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩ : nativeFrickeImage hA) =
      nativeFrickeHomeomorph hA hAlt (TeichmullerSpace.mk m) := by
    apply Subtype.ext
    exact (nativeFrickeHomeomorph_apply hA hAlt (TeichmullerSpace.mk m)).symm
  change markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α
    ((nativeFrickeHomeomorph hA hAlt).symm _) = _
  rw [hcoord, Homeomorph.symm_apply_apply]

/-- At those same literal coordinates, any original geodesic in the transported
free class has exactly the Fricke function's full-period BV length. -/
theorem frickeGeodesicLength_coordinates_eq (α : LiZhongQC.Loop X)
    (m : MarkedRiemannSurface.{0, 0} R) (M : HyperbolicSurfaceModel m.surface.toRiemannSurface)
    (q : OriginalClosedGeodesic M)
    (hq : LiZhongQC.FreelyHomotopic
      ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩ q.toLoop) :
    frickeGeodesicLength R hg hgenus hA hAlt α
      ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ = q.length.toReal := by
  rw [frickeGeodesicLength_coordinates]
  exact markedGeodesicLength_mk_eq R (Nat.succ_le_of_lt hg) hgenus α m M q hq

/-- An essential original curve has positive length at every actual Fricke point. -/
theorem frickeGeodesicLength_pos (α : LiZhongQC.Loop X) (hα : ¬ IsNullHomotopicLoop α)
    (t : nativeFrickeImage hA) : 0 < frickeGeodesicLength R hg hgenus hA hAlt α t := by
  let := nativeFrickeTopology hA
  exact markedGeodesicLength_pos R (Nat.succ_le_of_lt hg) hgenus α hα
    ((nativeFrickeHomeomorph hA hAlt).symm t)

end LowDimensionalTopology.Geometry.Teichmuller
