/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Unproved.Surfaces.OriginalDehnTwistGeometry

/-!
# The original positive Dehn twist with its literal annular formulas

An annular neighborhood of the given embedded circle supplies the same
ambient full turn, its original orientation and both fixed boundary circles.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

/-- The given embedded circle admits the literal positive annular full turn,
with its original orientation, coordinate formula, outside identity and fixed
boundary circles, under the two precise annular geometry inputs. -/
theorem exists_originalPositiveDehnTwist (R : ClosedRiemannSurface X)
    (hAnnulus : Unproved.Surfaces.SimpleCirclePositiveAnnularNeighborhoods R)
    (hOrientation : Unproved.Surfaces.PositiveAnnularFullTurnOrientation R)
    (c : Circle → X) (hc : Topology.IsEmbedding c) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∃ A : OriginalPositiveAnnularNeighborhood R c,
      IsOriginalPositiveDehnTwistAbout R c A.twist ∧
      LiZhongQC.IsOrientationPreservingRS A.twist ∧
      (∀ (s : Circle) (t : unitInterval),
        A.twist (A.map (s, t)) = A.map (s * Circle.exp (2 * Real.pi * (t : ℝ)), t)) ∧
      (∀ x : X, x ∉ Set.range A.map → A.twist x = x) ∧
      (∀ s : Circle, A.twist (A.map (s, (0 : unitInterval))) = A.map (s, (0 : unitInterval))) ∧
      (∀ s : Circle, A.twist (A.map (s, (1 : unitInterval))) = A.map (s, (1 : unitInterval))) ∧
      (∀ s : Circle, A.twist (c s) = c (s * Circle.exp (2 * Real.pi * (A.coreHeight : ℝ)))) := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨A⟩ := hAnnulus c hc
  refine ⟨A, ⟨A, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change LiZhongQC.IsOrientationPreservingRS
      (dehnAmbientHomeomorph A.map A.closedEmbedding A.openInterior)
    exact hOrientation A.map A.closedEmbedding A.openInterior A.positive
  · intro s t
    change dehnAmbientHomeomorph A.map A.closedEmbedding A.openInterior (A.map (s, t)) = _
    exact dehnAmbientHomeomorph_apply_image A.map A.closedEmbedding A.openInterior s t
  · intro x hx
    change dehnAmbientHomeomorph A.map A.closedEmbedding A.openInterior x = x
    exact dehnAmbientHomeomorph_apply_not_mem A.map A.closedEmbedding A.openInterior hx
  · intro s
    change dehnAmbientHomeomorph A.map A.closedEmbedding A.openInterior
      (A.map (s, (0 : unitInterval))) = _
    exact dehnAmbientHomeomorph_apply_zero A.map A.closedEmbedding A.openInterior s
  · intro s
    change dehnAmbientHomeomorph A.map A.closedEmbedding A.openInterior
      (A.map (s, (1 : unitInterval))) = _
    exact dehnAmbientHomeomorph_apply_one A.map A.closedEmbedding A.openInterior s
  · intro s
    exact dehnTwistAboutCore_apply_core c A.map A.closedEmbedding A.openInterior
      A.coreHeight A.coreHeight_mem A.core_eq s

end LowDimensionalTopology.Geometry.Surfaces
