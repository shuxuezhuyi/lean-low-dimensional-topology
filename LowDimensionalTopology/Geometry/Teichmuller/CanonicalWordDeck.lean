module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFuchsianModel
public import Mathlib.Algebra.Group.Action.End

/-! Every word in the given canonical matrices acts through the original true
deck group. Only the action descends; no surface-group homomorphism into SL is used. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m : MarkedRiemannSurface.{0, 0} R}

/-- Every actual canonical matrix word preserves the SAME original half-plane
cover, independently of the choice of an original source loop or based representative. -/
theorem canonicalWord_preserves_halfPlaneCover
    (P : NormalizedCanonicalFuchsianModel hg e m)
    (w : FreeGroup (StandardLabels g)) (z : ℍ) :
    P.model.halfPlaneCover
      ((FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w) • z) =
        P.model.halfPlaneCover z := by
  obtain ⟨ρ, hρ⟩ := P.exists_deckMarking
  let π : FreeGroup (StandardLabels g) →* LiZhongQC.surfaceGroup g :=
    PresentedGroup.mk {standardRelator g}
  let σ : FreeGroup (StandardLabels g) →* Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s))
  let aSL := MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin 2) ℝ) ℍ
  let aDeck := MulAction.toPermHom (deck P.model.halfPlaneCover) ℍ
  have ha : aSL.comp σ = aDeck.comp (ρ.toMonoidHom.comp π) := by
    apply FreeGroup.ext_hom
    intro s
    apply Equiv.ext
    intro u
    change σ (FreeGroup.of s) • u = ρ (π (FreeGroup.of s)) • u
    change (FreeGroup.lift (fun t => P.matrices ((edgeLabelEquiv g).symm t))
      (FreeGroup.of s)) • u = ρ (PresentedGroup.of s) • u
    rw [FreeGroup.lift_apply_of]
    simpa only [Equiv.apply_symm_apply] using hρ ((edgeLabelEquiv g).symm s) u
  have hw := congrArg
    (fun f : FreeGroup (StandardLabels g) →* Equiv.Perm ℍ => (f w) z) ha
  change σ w • z = ρ (π w) • z at hw
  change P.model.halfPlaneCover (σ w • z) = P.model.halfPlaneCover z
  rw [hw]
  exact deck.proj_smul (ρ (π w)) z

end LowDimensionalTopology.Geometry.Teichmuller
