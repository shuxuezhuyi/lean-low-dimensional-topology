module

public import LowDimensionalTopology.Unproved.Topology.CircleHomeomorphHomotopyDichotomy
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The unoriented free class of an actual embedded circle image

Equal geometric images give a genuine homeomorphism of the circle by the
existing embedding-to-range homeomorphisms. The explicit independent circle
input then removes that parameterization, allowing either orientation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

/-- Equal actual circle images have the same unoriented free class, conditional
only on the explicit classical circle-homeomorphism homotopy dichotomy. -/
theorem EssentialSimpleCircle.freeClass_eq_of_range_eq_of_circleHomeomorphHomotopyDichotomy
    (hCircle : LowDimensionalTopology.Unproved.Topology.CircleHomeomorphHomotopyDichotomy)
    {X : Type} [TopologicalSpace X] [T2Space X] (c d : EssentialSimpleCircle X)
    (h : Set.range c.val = Set.range d.val) :
    c.freeClass = d.freeClass := by
  let ec : Circle ≃ₜ Set.range c.val := c.isClosedEmbedding.isEmbedding.toHomeomorph
  let ed : Circle ≃ₜ Set.range d.val := d.isClosedEmbedding.isEmbedding.toHomeomorph
  let e : Circle ≃ₜ Circle :=
    ec.trans ((Homeomorph.setCongr h).trans ed.symm)
  have hcomp : d.val.comp (_root_.toContinuousMap e) = c.val := by
    ext z
    exact congrArg Subtype.val (ed.apply_symm_apply ((Homeomorph.setCongr h) (ec z)))
  apply (c.freeClass_eq_iff d).2
  rcases hCircle e with he | he
  · left
    simpa only [hcomp, ContinuousMap.comp_id] using
      (ContinuousMap.Homotopic.refl d.val).comp he
  · right
    simpa only [hcomp] using (ContinuousMap.Homotopic.refl d.val).comp he

end LowDimensionalTopology.Geometry.Surfaces
