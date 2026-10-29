module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.DehnAnnulusHomeomorph
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Extending the annular full turn to the original space

A genuine closed annular embedding supplies the coordinates. The image of its
open annulus is assumed open in the original space. The annular full turn then
extends by the identity to a homeomorphism of that same space.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

/-- Extend the actual annular coordinate permutation by identity outside its image. -/
def annulusExtensionEquiv (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (d : Circle × unitInterval ≃ₜ Circle × unitInterval) : X ≃ X := by
  classical
  exact Equiv.Perm.extendDomain d.toEquiv he.isEmbedding.toHomeomorph.toEquiv

private theorem annulusExtensionEquiv_apply_image (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (d : Circle × unitInterval ≃ₜ Circle × unitInterval) (p : Circle × unitInterval) :
    annulusExtensionEquiv e he d (e p) = e (d p) := by
  classical
  exact Equiv.Perm.extendDomain_apply_image d.toEquiv
    he.isEmbedding.toHomeomorph.toEquiv p

private theorem annulusExtensionEquiv_apply_not_mem (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (d : Circle × unitInterval ≃ₜ Circle × unitInterval) {x : X}
    (hx : x ∉ Set.range e) : annulusExtensionEquiv e he d x = x := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype d.toEquiv
    he.isEmbedding.toHomeomorph.toEquiv hx

private theorem annulusExtensionEquiv_symm (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (d : Circle × unitInterval ≃ₜ Circle × unitInterval) :
    (annulusExtensionEquiv e he d).symm = annulusExtensionEquiv e he d.symm := by
  classical
  rfl

/-- Boundary-fixed annular coordinates give a continuous identity extension. -/
theorem continuous_annulusExtensionEquiv (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (hopen : IsOpen (e '' {p : Circle × unitInterval |
      0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}))
    (d : Circle × unitInterval ≃ₜ Circle × unitInterval)
    (hzero : ∀ s : Circle, d (s, (0 : unitInterval)) = (s, (0 : unitInterval)))
    (hone : ∀ s : Circle, d (s, (1 : unitInterval)) = (s, (1 : unitInterval))) :
    Continuous (annulusExtensionEquiv e he d) := by
  classical
  let E : Circle × unitInterval ≃ₜ Set.range e := he.isEmbedding.toHomeomorph
  have hC : ContinuousOn (annulusExtensionEquiv e he d) (Set.range e) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hcont : Continuous (fun x : Set.range e => e (d (E.symm x))) :=
      he.continuous.comp (d.continuous.comp E.symm.continuous)
    apply hcont.congr
    intro x
    have hx : e (E.symm x) = (x : X) :=
      congrArg Subtype.val (E.apply_symm_apply x)
    calc
      e (d (E.symm x)) = annulusExtensionEquiv e he d (e (E.symm x)) :=
        (annulusExtensionEquiv_apply_image e he d (E.symm x)).symm
      _ = annulusExtensionEquiv e he d (x : X) :=
        congrArg (annulusExtensionEquiv e he d) hx
  have hB : Set.EqOn (annulusExtensionEquiv e he d) id
      (e '' {p : Circle × unitInterval |
        0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})ᶜ := by
    intro x hx
    by_cases hxC : x ∈ Set.range e
    · rcases hxC with ⟨⟨s, t⟩, rfl⟩
      have ht : t = 0 ∨ t = 1 := by
        by_cases h0 : 0 < (t : ℝ)
        · right
          apply Subtype.ext
          apply le_antisymm t.property.2
          exact le_of_not_gt (fun h1 => hx ⟨(s, t), ⟨h0, h1⟩, rfl⟩)
        · left
          apply Subtype.ext
          exact le_antisymm (le_of_not_gt h0) t.property.1
      rcases ht with ht | ht
      · simp only [annulusExtensionEquiv_apply_image, ht, hzero, id_eq]
      · simp only [annulusExtensionEquiv_apply_image, ht, hone, id_eq]
    · exact annulusExtensionEquiv_apply_not_mem e he d hxC
  have hcont := hC.union_of_isClosed
    ((continuous_id : Continuous (id : X → X)).continuousOn.congr hB)
    he.isClosed_range hopen.isClosed_compl
  apply continuousOn_univ.mp
  apply hcont.mono
  intro x _
  by_cases hx : x ∈ Set.range e
  · exact Or.inl hx
  · right
    rintro ⟨p, _, hp⟩
    exact hx ⟨p, hp⟩

/-- Extend the full-turn annular homeomorphism by the identity in the original space. -/
def dehnAmbientHomeomorph (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (hopen : IsOpen (e '' {p : Circle × unitInterval |
      0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})) : X ≃ₜ X := by
  classical
  refine
    { toEquiv := annulusExtensionEquiv e he dehnAnnulusHomeomorph
      continuous_toFun := continuous_annulusExtensionEquiv e he hopen
        dehnAnnulusHomeomorph dehnAnnulusHomeomorph_apply_zero
        dehnAnnulusHomeomorph_apply_one
      continuous_invFun := ?_ }
  change Continuous (annulusExtensionEquiv e he dehnAnnulusHomeomorph.symm)
  apply continuous_annulusExtensionEquiv e he hopen dehnAnnulusHomeomorph.symm
  · intro s
    exact dehnAnnulusHomeomorph.symm_apply_eq.mpr
      (dehnAnnulusHomeomorph_apply_zero s).symm
  · intro s
    exact dehnAnnulusHomeomorph.symm_apply_eq.mpr
      (dehnAnnulusHomeomorph_apply_one s).symm

/-- On the actual embedded annulus, the extension has the full-turn circle formula. -/
@[simp] theorem dehnAmbientHomeomorph_apply_image (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (hopen : IsOpen (e '' {p : Circle × unitInterval |
      0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})) (s : Circle) (t : unitInterval) :
    dehnAmbientHomeomorph e he hopen (e (s, t)) =
      e (s * Circle.exp (2 * Real.pi * (t : ℝ)), t) := by
  exact annulusExtensionEquiv_apply_image e he dehnAnnulusHomeomorph (s, t)

/-- The inverse uses the opposite full turn in the same original annular chart. -/
@[simp] theorem dehnAmbientHomeomorph_symm_apply_image (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (hopen : IsOpen (e '' {p : Circle × unitInterval |
      0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})) (s : Circle) (t : unitInterval) :
    (dehnAmbientHomeomorph e he hopen).symm (e (s, t)) =
      e (s * Circle.exp (-(2 * Real.pi * (t : ℝ))), t) := by
  change (annulusExtensionEquiv e he dehnAnnulusHomeomorph).symm (e (s, t)) = _
  rw [annulusExtensionEquiv_symm]
  exact annulusExtensionEquiv_apply_image e he dehnAnnulusHomeomorph.symm (s, t)

/-- The extension is the identity outside the actual embedded closed annulus. -/
theorem dehnAmbientHomeomorph_apply_not_mem (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (hopen : IsOpen (e '' {p : Circle × unitInterval |
      0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})) {x : X} (hx : x ∉ Set.range e) :
    dehnAmbientHomeomorph e he hopen x = x := by
  exact annulusExtensionEquiv_apply_not_mem e he dehnAnnulusHomeomorph hx

/-- The lower boundary circle of the original annular chart is fixed pointwise. -/
@[simp] theorem dehnAmbientHomeomorph_apply_zero (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (hopen : IsOpen (e '' {p : Circle × unitInterval |
      0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})) (s : Circle) :
    dehnAmbientHomeomorph e he hopen (e (s, (0 : unitInterval))) =
      e (s, (0 : unitInterval)) := by
  simp

/-- The upper boundary circle of the original annular chart is fixed pointwise. -/
@[simp] theorem dehnAmbientHomeomorph_apply_one (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (hopen : IsOpen (e '' {p : Circle × unitInterval |
      0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})) (s : Circle) :
    dehnAmbientHomeomorph e he hopen (e (s, (1 : unitInterval))) =
      e (s, (1 : unitInterval)) := by
  simp

end LowDimensionalTopology.Geometry.Surfaces
