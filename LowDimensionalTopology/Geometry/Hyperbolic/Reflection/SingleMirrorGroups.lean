/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeLineReflections
public import Mathlib.Data.Set.Finite.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic

theorem nativeLineReflection_square (L : HalfPlaneLine) :
    (halfPlaneLineReflectionIsometry L)^2=1 := by
  apply IsometryEquiv.ext
  intro z
  change L.reflection (L.reflection z)=z
  exact L.reflection_involutive z

theorem closure_single_involution_mem_pair {G : Type*} [Group G] (s : G) (hs : s^2=1) :
    ∀g∈Subgroup.closure ({s} : Set G), g=1 ∨ g=s := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact Or.inr (Set.mem_singleton_iff.mp hg)
  | one => exact Or.inl rfl
  | mul a b ha hb iha ihb =>
    rcases iha with rfl|rfl <;> rcases ihb with rfl|rfl
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (by simpa only [pow_two] using hs)
  | inv a ha iha =>
    rcases iha with rfl|rfl
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs))

theorem closure_single_involution_finite {G : Type*} [Group G] (s : G) (hs : s^2=1) :
    Finite (Subgroup.closure ({s} : Set G)) := by
  have hsub : (↑(Subgroup.closure ({s} : Set G)) : Set G)⊆{1,s} := by
    intro g hg
    exact closure_single_involution_mem_pair s hs g hg
  exact (((Set.finite_singleton s).insert 1).subset hsub).to_subtype

/-- A genuine native mirror generates only the identity and that mirror, and its
actual original generated subgroup is finite. -/
theorem native_single_mirror_group (L : HalfPlaneLine) :
    (∀g∈Subgroup.closure ({halfPlaneLineReflectionIsometry L} : Set (ℍ≃ᵢℍ)),
      g=1 ∨ g=halfPlaneLineReflectionIsometry L) ∧
    Finite (Subgroup.closure ({halfPlaneLineReflectionIsometry L} : Set (ℍ≃ᵢℍ))) :=
  ⟨closure_single_involution_mem_pair _ (nativeLineReflection_square L),
    closure_single_involution_finite _ (nativeLineReflection_square L)⟩

end LowDimensionalTopology.Geometry.Hyperbolic
