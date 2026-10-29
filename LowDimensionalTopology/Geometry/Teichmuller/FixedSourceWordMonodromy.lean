module

public import LowDimensionalTopology.Geometry.Teichmuller.FixedSourcePolygonWord
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFuchsianModel
public import Mathlib.Algebra.Group.Action.End

/-! The same finite source word acts by the actual endpoint monodromy on every
canonical marked target. Opposite monodromy is retained until both inverses cancel. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}

/-- One word is chosen from the original based class, independently of every
marked target, and its actual matrix word has exactly the transported endpoint action. -/
theorem fixedSourceWord_actual_monodromy
    (γ : FundamentalGroup X (e.symm (boundaryBase g).val)) :
    ∃ w : FreeGroup (StandardLabels g),
      ∀ (m : MarkedRiemannSurface.{0, 0} R)
        (P : NormalizedCanonicalFuchsianModel hg e m) (z : ℍ),
        FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w • z =
          ((P.model.markedPolygonCoverEquiv (m.marking.toHomeomorph.symm.trans e)
            P.liftBase P.liftBase_proj)
              (FundamentalGroup.map m.markingMap (e.symm (boundaryBase g).val) γ)).unop • z := by
  obtain ⟨w, hw⟩ := fixedSourcePolygonWord_exists (zero_lt_one.trans hg) e γ
  refine ⟨w, ?_⟩
  intro m P z
  let b := e.symm (boundaryBase g).val
  let C : FundamentalGroup m.carrier (m.markingMap b) ≃*
      (deck P.model.halfPlaneCover)ᵐᵒᵖ :=
    P.model.markedPolygonCoverEquiv (m.marking.toHomeomorph.symm.trans e)
      P.liftBase P.liftBase_proj
  let T : FundamentalGroup X b →* (deck P.model.halfPlaneCover)ᵐᵒᵖ :=
    C.toMonoidHom.comp (FundamentalGroup.map m.markingMap b)
  let D : FundamentalGroup X b →* deck P.model.halfPlaneCover :=
    (MulEquiv.inv' (deck P.model.halfPlaneCover)).symm.toMonoidHom.comp T
  have hmap (d : Edge g) :
      FundamentalGroup.map m.markingMap b (pathClass (markedPolygonLoop e d)) =
        pathClass (markedPolygonLoop (m.marking.toHomeomorph.symm.trans e) d) := by
    have hpath : (markedPolygonLoop e d).map m.markingMap.continuous =
        markedPolygonLoop (m.marking.toHomeomorph.symm.trans e) d := by
      ext t
      rfl
    rw [pathClass_eq_fromPath, TauCeti.FundamentalGroup.map_fromPath, hpath,
      pathClass_eq_fromPath]
    rfl
  have hD (d : Edge g) :
      D ((pathClass (markedPolygonLoop e d))⁻¹) =
        P.model.markedPolygonEndpointDeck (m.marking.toHomeomorph.symm.trans e)
          P.liftBase P.liftBase_proj d := by
    change ((C (FundamentalGroup.map m.markingMap b
      ((pathClass (markedPolygonLoop e d))⁻¹))).unop)⁻¹ = _
    rw [map_inv, map_inv]
    change (((C (FundamentalGroup.map m.markingMap b
      (pathClass (markedPolygonLoop e d)))).unop)⁻¹)⁻¹ = _
    rw [inv_inv, hmap]
    rfl
  let σ : FreeGroup (StandardLabels g) →* Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s))
  let aSL := MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin 2) ℝ) ℍ
  let aDeck := MulAction.toPermHom (deck P.model.halfPlaneCover) ℍ
  have ha : aSL.comp σ = aDeck.comp (D.comp (sourcePolygonWordHom e)) := by
    apply FreeGroup.ext_hom
    intro s
    apply Equiv.ext
    intro u
    change σ (FreeGroup.of s) • u = D (sourcePolygonWordHom e (FreeGroup.of s)) • u
    rw [show σ (FreeGroup.of s) = P.matrices ((edgeLabelEquiv g).symm s) from
      FreeGroup.lift_apply_of]
    rw [show sourcePolygonWordHom e (FreeGroup.of s) =
      (pathClass (markedPolygonLoop e ((edgeLabelEquiv g).symm s)))⁻¹ from
        FreeGroup.lift_apply_of, hD]
    exact P.represents ((edgeLabelEquiv g).symm s) u
  have he := congrArg
    (fun f : FreeGroup (StandardLabels g) →* Equiv.Perm ℍ => (f w) z) ha
  change σ w • z = ((C (FundamentalGroup.map m.markingMap b
    (sourcePolygonWordHom e w))).unop)⁻¹ • z at he
  rw [hw, map_inv, map_inv, MulOpposite.unop_inv, inv_inv] at he
  change σ w • z = (C (FundamentalGroup.map m.markingMap b γ)).unop • z
  exact he

end LowDimensionalTopology.Geometry.Teichmuller
