/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0), through the
credited covering-lift and free-homotopy APIs; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFuchsianModel

/-!
# Small comparisons for the prescribed canonical systems

An actual quasiconformal comparison in the prescribed free marking class
has a lift with the same distortion bound. Its common deck correction is
derived from that homotopy, so every ordered original generator is
intertwined. No replacement marking or axis alternation is introduced.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m n : MarkedRiemannSurface.{0, 0} R}

/-- A comparison in the actual free marking class lifts with its given
distortion bound and intertwines the unchanged ordered canonical systems. -/
theorem NormalizedCanonicalFuchsianModel.exists_comparison_lift
    (P : NormalizedCanonicalFuchsianModel hg e m)
    (Q : NormalizedCanonicalFuchsianModel hg e n)
    (h : m.carrier ≃ₜ n.carrier) {K : ℝ} :
    let := m.surface.toRiemannAtlas.toChartedSpace
    let := n.surface.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsKQCRS h K →
      ContinuousMap.Homotopic
        ((_root_.toContinuousMap h).comp m.markingMap) n.markingMap →
      ∃ B : ℍ ≃ₜ ℍ,
        LiZhongQC.IsLift P.model.halfPlaneCover Q.model.halfPlaneCover h B ∧
        LiZhongQC.IsKQC (LiZhongQC.liftToC B) LiZhongQC.upperHalf K ∧
        ∀ (d : Edge g) (z : ℍ), B (P.matrices d • z) = Q.matrices d • B z := by
  let := m.surface.toRiemannAtlas.toChartedSpace
  let := n.surface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro hK hhom
  let := m.surface.toRiemannAtlas.isManifold
  let := n.surface.toRiemannAtlas.isManifold
  let := m.surface.t2Space
  let := n.surface.t2Space
  let := m.surface.connectedSpace
  let := n.surface.connectedSpace
  let f := m.marking.toHomeomorph.symm.trans n.marking.toHomeomorph
  obtain ⟨Γm, _hΓm, hpM⟩ := P.model.exists_halfPlaneCover_uniformization
  obtain ⟨Γn, _hΓn, hpN⟩ := Q.model.exists_halfPlaneCover_uniformization
  have hab : Q.model.halfPlaneCover Q.liftBase =
      f (P.model.halfPlaneCover P.liftBase) := by
    rw [P.liftBase_proj, Q.liftBase_proj]
    change n.marking.toHomeomorph (e.symm (boundaryBase g).val) =
      n.marking.toHomeomorph (m.marking.toHomeomorph.symm
        (m.marking.toHomeomorph (e.symm (boundaryBase g).val)))
    rw [m.marking.toHomeomorph.symm_apply_apply]
  obtain ⟨F, hF, hFab⟩ :=
    LiZhongQC.exists_lift hpM hpN f P.liftBase Q.liftBase hab
  obtain ⟨c, hc⟩ := Q.model.halfPlaneCover_surjective (h (P.model.halfPlaneCover P.liftBase))
  obtain ⟨C, hC, _hCac⟩ := LiZhongQC.exists_lift hpM hpN h P.liftBase c hc
  let invm := _root_.toContinuousMap m.marking.toHomeomorph.symm
  have hhom' : ContinuousMap.Homotopic (_root_.toContinuousMap h)
      (_root_.toContinuousMap f) := by
    have ht := hhom.comp (ContinuousMap.Homotopic.refl invm)
    have hl : ((_root_.toContinuousMap h).comp m.markingMap).comp invm =
        _root_.toContinuousMap h := by
      ext y
      exact congrArg h (m.marking.toHomeomorph.apply_symm_apply y)
    have hr : n.markingMap.comp invm = _root_.toContinuousMap f := by
      ext y
      rfl
    rw [hl, hr] at ht
    exact ht
  obtain ⟨δ, hδ, hrel⟩ :=
    (LiZhongQC.thm23_1_homotopy_iff hpM hpN h f hC hF).mp hhom'
  let B : ℍ ≃ₜ ℍ := C.trans (Homeomorph.smul δ⁻¹)
  have hB (z : ℍ) : B z = δ⁻¹ • C z := rfl
  have hBlift : LiZhongQC.IsLift P.model.halfPlaneCover Q.model.halfPlaneCover h B := by
    intro z
    rw [hB, LiZhongQC.s30a_p_smul hpN (Γn.inv_mem hδ)]
    exact hC z
  refine ⟨B, hBlift, LiZhongQC.h23l_lift_isKQC hpM hpN hK hBlift, ?_⟩
  intro d z
  let Dm := P.model.markedPolygonEndpointDeck (m.marking.toHomeomorph.symm.trans e)
    P.liftBase P.liftBase_proj d
  let Dn := Q.model.markedPolygonEndpointDeck (n.marking.toHomeomorph.symm.trans e)
    Q.liftBase Q.liftBase_proj d
  obtain ⟨A, hA, hrep⟩ :=
    exists_uniformization_matrix_representative hpM Dm P.liftBase
  have hnat (y : ℍ) : Dn • F y = F (Dm • y) :=
    m.markedPolygonEndpointDeck_intertwines_lift n P.model Q.model e
      P.liftBase Q.liftBase P.liftBase_proj Q.liftBase_proj F hF hFab d y
  have hR := hrel A hA (C z)
  rw [C.symm_apply_apply] at hR
  rw [P.represents d z, Q.represents d (B z)]
  change B (Dm • z) = Dn • B z
  calc
    B (Dm • z) = δ⁻¹ • C (Dm • z) := hB _
    _ = δ⁻¹ • C (A • z) := congrArg (fun y : ℍ => δ⁻¹ • C y) (hrep z).symm
    _ = F (A • F.symm (δ⁻¹ • C z)) := by rw [hR, inv_smul_smul]
    _ = F (Dm • F.symm (B z)) := by rw [← hB z, hrep]
    _ = Dn • B z := by
      simpa only [F.apply_symm_apply] using (hnat (F.symm (B z))).symm

end LowDimensionalTopology.Geometry.Teichmuller
