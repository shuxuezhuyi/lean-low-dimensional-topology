module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairQuotientReflection
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The full annular mirror group on the original pair-product quotient

Every element of the actual full mirror group induces either the identity or
the existing quotient reflection. In particular, a point fixed by that
reflection is unchanged in the quotient by every full mirror-group element.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action

variable (E r x : ℝ) (hE : 0 < E) (hr : 0 < r)
local notation "S" => annularPairReflectionMirrors E r x hE hr
local notation "G" => annularPairReflectionGroup E r x hE hr
local notation "J" => annularPairQuotientReflection E r x hE hr
local notation "π" => orbitProjection G ℍ

/-- Each full mirror-group element has one of the two actual quotient actions. -/
theorem annularPairFullMirror_projection_eq_or_reflection (f : ℍ ≃ᵢ ℍ)
    (hf : f ∈ ⨆ i : Fin 3, Subgroup.zpowers (halfPlaneLineReflectionIsometry (S i))) :
    (∀ z : ℍ, π (f z) = π z) ∨ (∀ z : ℍ, π (f z) = J (π z)) := by
  let σ : Fin 3 → (ℍ ≃ᵢ ℍ) := fun i => halfPlaneLineReflectionIsometry (S i)
  change f ∈ ⨆ i : Fin 3, Subgroup.zpowers (σ i) at hf
  refine Subgroup.iSup_induction (fun i : Fin 3 => Subgroup.zpowers (σ i))
    (C := fun a => (∀ z : ℍ, π (a z) = π z) ∨
      (∀ z : ℍ, π (a z) = J (π z))) hf ?_ ?_ ?_
  · intro i a ha
    have ha' : a ∈ Subgroup.closure ({σ i} : Set (ℍ ≃ᵢ ℍ)) := by
      simpa only [Subgroup.zpowers_eq_closure] using ha
    rcases closure_single_involution_mem_pair (σ i)
      (nativeLineReflection_square (S i)) a ha' with rfl | rfl
    · exact Or.inl (fun _ => rfl)
    · exact Or.inr (fun z =>
        (annularPairQuotientReflection_mirror_projection E r x hE hr i z).symm)
  · exact Or.inl (fun _ => rfl)
  · intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · left
      intro z
      change π (a (b z)) = π z
      rw [ha, hb]
    · right
      intro z
      change π (a (b z)) = J (π z)
      rw [ha, hb]
    · right
      intro z
      change π (a (b z)) = J (π z)
      rw [ha, hb]
    · left
      intro z
      change π (a (b z)) = π z
      rw [ha, hb]
      exact annularPairQuotientReflection_involutive E r x hE hr (π z)

/-- Every full mirror-group element leaves an actual fixed quotient point unchanged. -/
theorem annularPairFullMirror_fixes_fixed_projection (f : ℍ ≃ᵢ ℍ)
    (hf : f ∈ ⨆ i : Fin 3, Subgroup.zpowers (halfPlaneLineReflectionIsometry (S i)))
    (z : ℍ) (hz : J (π z) = π z) : π (f z) = π z := by
  rcases annularPairFullMirror_projection_eq_or_reflection E r x hE hr f hf with h | h
  · exact h z
  · exact (h z).trans hz

end LowDimensionalTopology.Geometry.Hyperbolic
