module

public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleFreeClasses
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The actual action of a surface homeomorphism on simple free classes

Representatives are postcomposed with the given original homeomorphism.
Both free homotopy and reversal descend to the existing unoriented
essential simple free-class quotient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Postcompose the actual embedded essential circle with a homeomorphism. -/
def EssentialSimpleCircle.mapHomeomorph (h : X ≃ₜ Y) (c : EssentialSimpleCircle X) :
    EssentialSimpleCircle Y :=
  ⟨(_root_.toContinuousMap h).comp c.1, by
    refine ⟨h.injective.comp c.2.1, ?_⟩
    intro hnull
    apply c.2.2
    have hn := hnull.comp_right (_root_.toContinuousMap h.symm)
    have he : (_root_.toContinuousMap h.symm).comp
        ((_root_.toContinuousMap h).comp c.1) = c.1 := by
      ext z
      exact h.symm_apply_apply (c.1 z)
    rwa [he] at hn⟩

@[simp] theorem EssentialSimpleCircle.mapHomeomorph_symm
    (h : X ≃ₜ Y) (c : EssentialSimpleCircle X) :
    (c.mapHomeomorph h).mapHomeomorph h.symm = c := by
  apply Subtype.ext
  ext z
  exact h.symm_apply_apply (c.1 z)

/-- Postcomposition respects the actual free homotopy relation, with either
orientation of the original circle parameter. -/
theorem EssentialSimpleCircle.mapHomeomorph_rel
    (h : X ≃ₜ Y) {c d : EssentialSimpleCircle X}
    (hcd : (essentialSimpleCircleSetoid X).r c d) :
    (essentialSimpleCircleSetoid Y).r (c.mapHomeomorph h) (d.mapHomeomorph h) := by
  rcases hcd with hcd | hcd
  · exact Or.inl ((ContinuousMap.Homotopic.refl (_root_.toContinuousMap h)).comp hcd)
  · exact Or.inr ((ContinuousMap.Homotopic.refl (_root_.toContinuousMap h)).comp hcd)

/-- The class permutation induced by the given homeomorphism of the original
carrier. Its inverse is induced by the actual inverse homeomorphism. -/
def essentialSimpleFreeClassEquiv (h : X ≃ₜ Y) :
    EssentialSimpleFreeClass X ≃ EssentialSimpleFreeClass Y where
  toFun := Quotient.map (EssentialSimpleCircle.mapHomeomorph h)
    (fun _ _ hcd => EssentialSimpleCircle.mapHomeomorph_rel h hcd)
  invFun := Quotient.map (EssentialSimpleCircle.mapHomeomorph h.symm)
    (fun _ _ hcd => EssentialSimpleCircle.mapHomeomorph_rel h.symm hcd)
  left_inv := by
    intro a
    refine Quotient.inductionOn a ?_
    intro c
    change ((c.mapHomeomorph h).mapHomeomorph h.symm).freeClass = c.freeClass
    rw [EssentialSimpleCircle.mapHomeomorph_symm]
  right_inv := by
    intro a
    refine Quotient.inductionOn a ?_
    intro c
    change ((c.mapHomeomorph h.symm).mapHomeomorph h).freeClass = c.freeClass
    simpa only [Homeomorph.symm_symm] using
      congrArg EssentialSimpleCircle.freeClass
        (EssentialSimpleCircle.mapHomeomorph_symm h.symm c)

/-- The induced permutation retains the precise postcomposed representative. -/
@[simp] theorem essentialSimpleFreeClassEquiv_apply_freeClass
    (h : X ≃ₜ Y) (c : EssentialSimpleCircle X) :
    essentialSimpleFreeClassEquiv h c.freeClass = (c.mapHomeomorph h).freeClass := rfl

/-- Its inverse is the permutation induced by the given inverse homeomorphism. -/
@[simp] theorem essentialSimpleFreeClassEquiv_symm (h : X ≃ₜ Y) :
    (essentialSimpleFreeClassEquiv h).symm = essentialSimpleFreeClassEquiv h.symm := rfl

end LowDimensionalTopology.Geometry.Surfaces
