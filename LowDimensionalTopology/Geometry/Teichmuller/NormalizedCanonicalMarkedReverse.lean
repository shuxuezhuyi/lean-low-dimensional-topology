module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFuchsianModel
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.GroupTheory.PresentedGroup

/-!
# Equal actual canonical systems recover the native marked surface

The full true deck presentations give equal covering fibres. The existing
holomorphic descent theorem descends the identity upstairs. The actual anchored
marking lift and the existing free-homotopy theorem recover the marking.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation Hyperbolic Mobius
variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}

namespace NormalizedCanonicalFuchsianModel
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m n : MarkedRiemannSurface.{0, 0} R}

/-- Equality of all prescribed projective generators gives actual native
marked equivalence, with the target map and marking homotopy both derived. -/
theorem equivalent_of_generators_eq (P : NormalizedCanonicalFuchsianModel hg e m)
    (Q : NormalizedCanonicalFuchsianModel hg e n)
    (hgen : ∀ d : Edge g, realSLMobius (P.matrices d) = realSLMobius (Q.matrices d)) :
    MarkedRiemannSurface.Equivalent m n := by
  let := m.surface.toRiemannAtlas.toChartedSpace
  let := n.surface.toRiemannAtlas.toChartedSpace
  let := m.surface.toRiemannAtlas.isManifold
  let := n.surface.toRiemannAtlas.isManifold
  let := m.surface.t2Space
  let := n.surface.t2Space
  let := m.surface.connectedSpace
  let := n.surface.connectedSpace
  obtain ⟨ΓP, _hΓP, hpP⟩ := P.model.exists_halfPlaneCover_uniformization
  obtain ⟨ΓQ, _hΓQ, hpQ⟩ := Q.model.exists_halfPlaneCover_uniformization
  obtain ⟨ρP, hρP⟩ := P.exists_deckMarking
  obtain ⟨ρQ, hρQ⟩ := Q.exists_deckMarking
  have hmat (d : Edge g) (z : ℍ) : P.matrices d • z = Q.matrices d • z := by
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    exact (realSLMobius_action (P.matrices d) z).symm.trans
      ((congrArg (fun q : complexMobiusGroup => q.val (z : ℂ)) (hgen d)).trans
        (realSLMobius_action (Q.matrices d) z))
  let πP : LiZhongQC.surfaceGroup g →* (ℍ ≃ₜ ℍ) :=
    (deck P.model.halfPlaneCover).subtype.comp ρP.toMonoidHom
  let πQ : LiZhongQC.surfaceGroup g →* (ℍ ≃ₜ ℍ) :=
    (deck Q.model.halfPlaneCover).subtype.comp ρQ.toMonoidHom
  have hπ : πP = πQ := by
    apply PresentedGroup.ext
    intro s
    obtain ⟨d, rfl⟩ := (edgeLabelEquiv g).surjective s
    apply Homeomorph.ext
    intro z
    change ρP (PresentedGroup.of (edgeLabelEquiv g d)) • z =
      ρQ (PresentedGroup.of (edgeLabelEquiv g d)) • z
    exact (hρP d z).symm.trans ((hmat d z).trans (hρQ d z))
  have hall (s : LiZhongQC.surfaceGroup g) (z : ℍ) : ρP s • z = ρQ s • z :=
    congrArg (fun π : LiZhongQC.surfaceGroup g →* (ℍ ≃ₜ ℍ) => π s z) hπ
  have h12 (z w : ℍ) (hzw : P.model.halfPlaneCover z = P.model.halfPlaneCover w) :
      Q.model.halfPlaneCover z = Q.model.halfPlaneCover w := by
    obtain ⟨D, hD⟩ := covering_exists_deck_map P.model.halfPlaneCover_covering z w hzw
    obtain ⟨s, rfl⟩ := ρP.surjective D
    exact (deck.proj_smul (ρQ s) z).symm.trans
      (congrArg Q.model.halfPlaneCover ((hall s z).symm.trans hD))
  have h21 (z w : ℍ) (hzw : Q.model.halfPlaneCover z = Q.model.halfPlaneCover w) :
      P.model.halfPlaneCover z = P.model.halfPlaneCover w := by
    obtain ⟨D, hD⟩ := covering_exists_deck_map Q.model.halfPlaneCover_covering z w hzw
    obtain ⟨s, rfl⟩ := ρQ.surjective D
    exact (deck.proj_smul (ρP s) z).symm.trans
      (congrArg P.model.halfPlaneCover ((hall s z).trans hD))
  obtain ⟨c, hc, hcp⟩ := LiZhongQC.s27l_descend_homeomorph hpP hpQ h12 h21
  let f := m.marking.toHomeomorph.symm.trans n.marking.toHomeomorph
  have hab : Q.model.halfPlaneCover Q.liftBase = f (P.model.halfPlaneCover P.liftBase) := by
    rw [P.liftBase_proj, Q.liftBase_proj]
    change n.marking.toHomeomorph (e.symm (boundaryBase g).val) =
      n.marking.toHomeomorph (m.marking.toHomeomorph.symm
        (m.marking.toHomeomorph (e.symm (boundaryBase g).val)))
    rw [m.marking.toHomeomorph.symm_apply_apply]
  obtain ⟨F, hF, hFab⟩ := LiZhongQC.exists_lift hpP hpQ f P.liftBase Q.liftBase hab
  have hconj : (MulAut.conj F).toMonoidHom.comp πP = πQ := by
    apply PresentedGroup.ext
    intro s
    obtain ⟨d, rfl⟩ := (edgeLabelEquiv g).surjective s
    apply Homeomorph.ext
    intro z
    change F (ρP (PresentedGroup.of (edgeLabelEquiv g d)) • F.symm z) =
      ρQ (PresentedGroup.of (edgeLabelEquiv g d)) • z
    calc
      _ = F (P.matrices d • F.symm z) := congrArg F (hρP d (F.symm z)).symm
      _ = F (P.model.markedPolygonEndpointDeck (m.marking.toHomeomorph.symm.trans e)
          P.liftBase P.liftBase_proj d • F.symm z) := congrArg F (P.represents d _)
      _ = Q.model.markedPolygonEndpointDeck (n.marking.toHomeomorph.symm.trans e)
          Q.liftBase Q.liftBase_proj d • F (F.symm z) :=
        (m.markedPolygonEndpointDeck_intertwines_lift n P.model Q.model e
          P.liftBase Q.liftBase P.liftBase_proj Q.liftBase_proj F hF hFab d (F.symm z)).symm
      _ = Q.matrices d • z := by rw [F.apply_symm_apply, ← Q.represents d z]
      _ = ρQ (PresentedGroup.of (edgeLabelEquiv g d)) • z := hρQ d z
  have hcomm (s : LiZhongQC.surfaceGroup g) (z : ℍ) :
      F (ρP s • F.symm z) = ρP s • z := by
    have h := congrArg (fun π : LiZhongQC.surfaceGroup g →* (ℍ ≃ₜ ℍ) => π s z) hconj
    change F (ρP s • F.symm z) = ρQ s • z at h
    exact h.trans (hall s z).symm
  have hId : LiZhongQC.IsLift P.model.halfPlaneCover Q.model.halfPlaneCover c
      (Homeomorph.refl ℍ) := fun z => (hcp z).symm
  have hhom : ContinuousMap.Homotopic (_root_.toContinuousMap c) (_root_.toContinuousMap f) := by
    apply (LiZhongQC.thm23_1_homotopy_iff hpP hpQ c f hId hF).mpr
    refine ⟨1, ΓQ.one_mem, ?_⟩
    intro A hA z
    simp only [inv_one, one_smul]
    change A • z = F (A • F.symm z)
    let D : deck P.model.halfPlaneCover :=
      ⟨{ toEquiv := (MulAction.toPerm A : Equiv.Perm ℍ)
         continuous_toFun := continuous_const_smul A
         continuous_invFun := continuous_const_smul (A⁻¹) },
        by funext w; exact LiZhongQC.s30a_p_smul hpP hA w⟩
    obtain ⟨s, hs⟩ := ρP.surjective D
    have h := hcomm s z
    rw [hs] at h
    exact h.symm
  have hmark := hhom.comp (ContinuousMap.Homotopic.refl m.markingMap)
  have hcancel : (_root_.toContinuousMap f).comp m.markingMap = n.markingMap := by
    ext x
    exact congrArg n.marking.toHomeomorph (m.marking.toHomeomorph.symm_apply_apply x)
  rw [hcancel] at hmark
  exact ⟨c, (analyticHomeomorph_iff_sourceBiholomorphic
    m.surface.toRiemannAtlas n.surface.toRiemannAtlas c).mpr hc, hmark⟩

end NormalizedCanonicalFuchsianModel
end LowDimensionalTopology.Geometry.Teichmuller
