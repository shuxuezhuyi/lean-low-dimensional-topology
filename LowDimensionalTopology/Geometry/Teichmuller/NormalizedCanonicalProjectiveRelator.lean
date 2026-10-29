module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFuchsianModel
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalReconstruction
public import Mathlib.Algebra.Group.Action.End

/-!
# The actual canonical surface relator in chosen real special-linear lifts

The surface presentation kills the ordered word in the true deck group.
Its native action therefore kills the same matrix word projectively. The
only conclusion about its chosen real special-linear lift is central sign.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation Hyperbolic

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m : MarkedRiemannSurface.{0, 0} R}

/-- The full ordered commutator product of the actual canonical matrices is
central, with both possible special-linear signs retained. -/
theorem NormalizedCanonicalFuchsianModel.commutatorSL_prod_eq_one_or_neg_one
    (P : NormalizedCanonicalFuchsianModel hg e m) :
    (List.ofFn fun j : Fin g => LiZhongQC.commutatorSL
      (P.matrices (j, 0)) (P.matrices (j, 1))).prod = 1 ∨
    (List.ofFn fun j : Fin g => LiZhongQC.commutatorSL
      (P.matrices (j, 0)) (P.matrices (j, 1))).prod = -1 := by
  obtain ⟨ρ, hρ⟩ := P.exists_deckMarking
  let π : FreeGroup (StandardLabels g) →* LiZhongQC.surfaceGroup g :=
    PresentedGroup.mk {standardRelator g}
  let σ : FreeGroup (StandardLabels g) →* Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s))
  let aSL := MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin 2) ℝ) ℍ
  let aDeck := MulAction.toPermHom (deck P.model.halfPlaneCover) ℍ
  have hπ : π (standardRelator g) = 1 := by
    change PresentedGroup.mk {standardRelator g} (standardRelator g) = 1
    exact PresentedGroup.one_of_mem (by simp)
  have ha : aSL.comp σ = aDeck.comp (ρ.toMonoidHom.comp π) := by
    apply FreeGroup.ext_hom
    intro s
    apply Equiv.ext
    intro z
    change σ (FreeGroup.of s) • z = ρ (π (FreeGroup.of s)) • z
    change (FreeGroup.lift (fun t => P.matrices ((edgeLabelEquiv g).symm t))
      (FreeGroup.of s)) • z = ρ (PresentedGroup.of s) • z
    rw [FreeGroup.lift_apply_of]
    simpa only [Equiv.apply_symm_apply] using hρ ((edgeLabelEquiv g).symm s) z
  have hword : σ (standardRelator g) =
      (List.ofFn fun j : Fin g => LiZhongQC.commutatorSL
        (P.matrices (j, 0)) (P.matrices (j, 1))).prod := by
    dsimp only [standardRelator]
    rw [map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext j
    simp only [σ, Function.comp_apply, map_mul, map_inv, FreeGroup.lift_apply_of]
    rfl
  have haction : aSL (σ (standardRelator g)) = 1 := by
    change (aSL.comp σ) (standardRelator g) = 1
    rw [ha]
    change aDeck (ρ (π (standardRelator g))) = 1
    rw [hπ, map_one, map_one]
  apply (realSLMobius_eq_iff_sign 1 _).mp
  symm
  apply realSLMobius_eq_of_native_action
  intro z
  have hz := congrArg (fun f : Equiv.Perm ℍ => f z) haction
  change σ (standardRelator g) • z = z at hz
  simpa only [hword, one_smul] using hz

end LowDimensionalTopology.Geometry.Teichmuller
