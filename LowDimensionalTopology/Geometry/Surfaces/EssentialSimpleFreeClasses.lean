module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Essential unoriented simple free classes on the original surface

Representatives are actual injective continuous circle maps that are not
null-homotopic. Free homotopies may pass through arbitrary continuous maps.
The quotient also identifies the explicit reversal of the circle parameter.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

universe u

/-- The actual orientation reversal of the unit circle, complex conjugation. -/
def circleReversal : C(Circle, Circle) := ⟨fun z => z⁻¹, continuous_inv⟩

/-- Reversing the circle parameter twice restores the original map. -/
@[simp] theorem comp_circleReversal_twice
    {X : Type u} [TopologicalSpace X] (f : C(Circle, X)) :
    (f.comp circleReversal).comp circleReversal = f := by
  ext z
  simp [circleReversal]

/-- An actual simple closed curve on the original carrier, with the essential
condition excluding every free homotopy to a constant map. -/
abbrev EssentialSimpleCircle (X : Type u) [TopologicalSpace X] :=
  {f : C(Circle, X) // Function.Injective f ∧ ¬ f.Nullhomotopic}

/-- Such a representative is an embedded closed circle on a Hausdorff surface. -/
theorem EssentialSimpleCircle.isClosedEmbedding
    {X : Type u} [TopologicalSpace X] [T2Space X] (c : EssentialSimpleCircle X) :
    Topology.IsClosedEmbedding c.1 :=
  c.1.continuous.isClosedEmbedding c.2.1

/-- Reversal keeps both simplicity and essentiality on the same carrier. -/
def EssentialSimpleCircle.reverse
    {X : Type u} [TopologicalSpace X] (c : EssentialSimpleCircle X) :
    EssentialSimpleCircle X :=
  ⟨c.1.comp circleReversal, by
    refine ⟨?_, ?_⟩
    · intro z w h
      have hi : z⁻¹ = w⁻¹ := c.2.1 h
      exact inv_injective hi
    · intro h
      apply c.2.2
      simpa only [comp_circleReversal_twice] using h.comp_left circleReversal⟩

/-- Free homotopy of simple essential representatives, with orientation
forgotten by precomposition with the explicit circle reversal. -/
def essentialSimpleCircleSetoid (X : Type u) [TopologicalSpace X] :
    Setoid (EssentialSimpleCircle X) where
  r c d := c.1.Homotopic d.1 ∨ c.1.Homotopic (d.1.comp circleReversal)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro c
      exact Or.inl (ContinuousMap.Homotopic.refl c.1)
    · intro c d h
      rcases h with h | h
      · exact Or.inl h.symm
      · have hr := h.symm.comp (ContinuousMap.Homotopic.refl circleReversal)
        exact Or.inr (by simpa only [comp_circleReversal_twice] using hr)
    · intro c d e hcd hde
      rcases hcd with hcd | hcd <;> rcases hde with hde | hde
      · exact Or.inl (hcd.trans hde)
      · exact Or.inr (hcd.trans hde)
      · exact Or.inr (hcd.trans (hde.comp (ContinuousMap.Homotopic.refl circleReversal)))
      · have h := hcd.trans (hde.comp (ContinuousMap.Homotopic.refl circleReversal))
        exact Or.inl (by simpa only [comp_circleReversal_twice] using h)

/-- The book's essential unoriented simple closed free-homotopy classes.
The carrier is unchanged; no selected geodesic or isotopy is part of the data. -/
def EssentialSimpleFreeClass (X : Type u) [TopologicalSpace X] :=
  Quotient (essentialSimpleCircleSetoid X)

/-- The actual free class of a supplied original simple essential circle. -/
def EssentialSimpleCircle.freeClass
    {X : Type u} [TopologicalSpace X] (c : EssentialSimpleCircle X) :
    EssentialSimpleFreeClass X :=
  Quotient.mk (essentialSimpleCircleSetoid X) c

/-- Equality is exactly free homotopy, with either orientation allowed. -/
theorem EssentialSimpleCircle.freeClass_eq_iff
    {X : Type u} [TopologicalSpace X] (c d : EssentialSimpleCircle X) :
    c.freeClass = d.freeClass ↔
      c.1.Homotopic d.1 ∨ c.1.Homotopic (d.1.comp circleReversal) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Reversing the same actual simple essential curve leaves its class unchanged. -/
@[simp] theorem EssentialSimpleCircle.freeClass_reverse
    {X : Type u} [TopologicalSpace X] (c : EssentialSimpleCircle X) :
    c.reverse.freeClass = c.freeClass := by
  exact (freeClass_eq_iff c.reverse c).2 (Or.inr (ContinuousMap.Homotopic.refl _))

end LowDimensionalTopology.Geometry.Surfaces
