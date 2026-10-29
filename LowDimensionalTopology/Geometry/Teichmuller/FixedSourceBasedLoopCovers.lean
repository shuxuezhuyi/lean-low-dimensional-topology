module

public import LowDimensionalTopology.Geometry.Teichmuller.FixedSourceWordMonodromy
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-! The fixed source word covers the actual marking image of the same based
source loop. The covering path and its endpoint are derived from the original cover. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}

/-- One finite original word covers the unchanged original based loop after
every actual marking, using that target's same canonical matrices and cover. -/
theorem fixedSourceBasedLoop_word_covers
    (β : Path (e.symm (boundaryBase g).val) (e.symm (boundaryBase g).val)) :
    ∃ w : FreeGroup (StandardLabels g),
      ∀ (m : MarkedRiemannSurface.{0, 0} R) (P : NormalizedCanonicalFuchsianModel hg e m),
        LiZhongQC.Covers P.model.halfPlaneCover
          (FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w)
          ⟨m.markingMap (e.symm (boundaryBase g).val), β.map m.markingMap.continuous⟩ := by
  obtain ⟨w, hw⟩ := fixedSourceWord_actual_monodromy (R := R) (hg := hg) (e := e)
    (pathClass β)
  refine ⟨w, ?_⟩
  intro m P
  let C : FundamentalGroup m.carrier (m.markingMap (e.symm (boundaryBase g).val)) ≃*
      (deck P.model.halfPlaneCover)ᵐᵒᵖ :=
    P.model.markedPolygonCoverEquiv (m.marking.toHomeomorph.symm.trans e)
      P.liftBase P.liftBase_proj
  let βm := β.map m.markingMap.continuous
  let L := P.model.halfPlaneCover_covering.liftPath βm P.liftBase
    (βm.source.trans P.liftBase_proj.symm)
  have hL (t : unitInterval) : P.model.halfPlaneCover (L t) = βm t :=
    congrFun (P.model.halfPlaneCover_covering.liftPath_lifts _ _ _) t
  have hL0 : L 0 = P.liftBase := P.model.halfPlaneCover_covering.liftPath_zero _ _ _
  have hL1 : L 1 =
      ((P.model.markedPolygonCoverEquiv (m.marking.toHomeomorph.symm.trans e)
        P.liftBase P.liftBase_proj) (pathClass βm)).unop • P.liftBase := by
    let q := covering_deck_isQuotientCoveringMap P.model.halfPlaneCover_covering
      P.model.halfPlaneCover_surjective
    exact (q.unop_fundamentalGroupToMulOpposite_smul
      (e := ⟨P.liftBase, P.liftBase_proj⟩) (γ := pathClass βm)).symm
  have hL1c : L 1 = (C (pathClass βm)).unop • P.liftBase := by
    change L 1 = (C (pathClass βm)).unop • P.liftBase at hL1
    exact hL1
  have hmap : FundamentalGroup.map m.markingMap (e.symm (boundaryBase g).val)
      (pathClass β) = pathClass βm := by
    rw [pathClass_eq_fromPath, TauCeti.FundamentalGroup.map_fromPath,
      pathClass_eq_fromPath]
  have hend : L 1 =
      FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w • L 0 := by
    rw [hL0, hL1c, ← hmap]
    have hword := hw m P P.liftBase
    change FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w • P.liftBase =
      (C (FundamentalGroup.map m.markingMap (e.symm (boundaryBase g).val)
        (pathClass β))).unop • P.liftBase at hword
    exact hword.symm
  refine ⟨fun t => L (Set.projIcc 0 1 zero_le_one t),
    (L.continuous.comp continuous_projIcc).continuousOn, fun t _ => ?_, ?_⟩
  · rw [hL]
    rfl
  · change L (Set.projIcc (0 : ℝ) 1 zero_le_one 1) =
      FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w •
        L (Set.projIcc (0 : ℝ) 1 zero_le_one 0)
    rw [Set.projIcc_right, Set.projIcc_left]
    exact hend

end LowDimensionalTopology.Geometry.Teichmuller
