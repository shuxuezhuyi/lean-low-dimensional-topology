module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedPolygonMonodromy
public import Mathlib.GroupTheory.PresentedGroup

/-! A fixed word is chosen solely from the original source marking and source
fundamental class. No marked target or matrix choice enters that selection. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] {g : ℕ}

/-- Inverse original side classes, so that opposite endpoint monodromy later
produces the positive canonical matrix letters in their original word order. -/
def sourcePolygonWordHom (e : X ≃ₜ PolygonQuotient g) :
    FreeGroup (StandardLabels g) →* FundamentalGroup X (e.symm (boundaryBase g).val) :=
  FreeGroup.lift (fun s =>
    (pathClass (markedPolygonLoop e ((edgeLabelEquiv g).symm s)))⁻¹)

/-- Every fixed original based class has one finite word, chosen before any
marked target; the inverse cancels the inverse in true endpoint monodromy. -/
theorem fixedSourcePolygonWord_exists (hg : 0 < g) (e : X ≃ₜ PolygonQuotient g)
    (γ : FundamentalGroup X (e.symm (boundaryBase g).val)) :
    ∃ w : FreeGroup (StandardLabels g), sourcePolygonWordHom e w = γ⁻¹ := by
  let E := markedPolygonFundamentalEquiv hg e
  obtain ⟨c, hside⟩ := markedPolygonLoop_images_up_to_common_conjugation hg e
  let π : FreeGroup (StandardLabels g) →* LiZhongQC.surfaceGroup g :=
    PresentedGroup.mk {standardRelator g}
  have hword : E.toMonoidHom.comp (sourcePolygonWordHom e) =
      (MulAut.conj c).toMonoidHom.comp π := by
    apply FreeGroup.ext_hom
    intro s
    change E (sourcePolygonWordHom e (FreeGroup.of s)) = c * π (FreeGroup.of s) * c⁻¹
    rw [show sourcePolygonWordHom e (FreeGroup.of s) =
      (pathClass (markedPolygonLoop e ((edgeLabelEquiv g).symm s)))⁻¹ from
        FreeGroup.lift_apply_of, map_inv, hside]
    simp only [Equiv.apply_symm_apply, mul_inv_rev, inv_inv, mul_assoc]
    let t : LiZhongQC.surfaceGroup g := PresentedGroup.of s
    exact congrArg (fun k : LiZhongQC.surfaceGroup g => c * (k * c⁻¹)) (inv_inv t)
  obtain ⟨w, hw⟩ := PresentedGroup.mk_surjective ({standardRelator g} :
    Set (FreeGroup (StandardLabels g))) (c⁻¹ * E (γ⁻¹) * c)
  change π w = c⁻¹ * E (γ⁻¹) * c at hw
  refine ⟨w, E.injective ?_⟩
  calc
    E (sourcePolygonWordHom e w) = c * π w * c⁻¹ :=
      congrArg (fun f : FreeGroup (StandardLabels g) →* LiZhongQC.surfaceGroup g => f w) hword
    _ = E (γ⁻¹) := by
      rw [hw]
      simp [mul_assoc]

end LowDimensionalTopology.Geometry.Teichmuller
