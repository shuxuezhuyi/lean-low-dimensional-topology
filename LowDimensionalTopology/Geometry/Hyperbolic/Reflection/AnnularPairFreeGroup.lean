module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairReflectionGroup
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularTwoGeneratorFree
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The two original reflection products in their fixed source order. -/
def annularPairReflectionGenerators (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) :
    Fin 2 → (ℍ ≃ᵢ ℍ) :=
  let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
  let σ1 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 E hE)
  let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
  ![σ0 * σ1, σ2 * σ0]

theorem annularPairReflectionGenerators_lift_range (E r x : ℝ)
    (hE : 0 < E) (hr : 0 < r) :
    (FreeGroup.lift (annularPairReflectionGenerators E r x hE hr)).range =
      annularPairReflectionGroup E r x hE hr := by
  rw [FreeGroup.range_lift_eq_closure]
  dsimp only [annularPairReflectionGenerators, annularPairReflectionGroup]
  rw [Matrix.range_cons_cons_empty]

/-- The fixed free basis maps to the original ordered pair in the same native subgroup. -/
def annularPairReflectionFreeEquiv (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    FreeGroup (Fin 2) ≃*
      annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr := by
  have hinj : Function.Injective (FreeGroup.lift
      (annularPairReflectionGenerators E r x (zero_lt_one.trans hE) hr)) :=
    annular_reflection_products_free E r x hE hr hinner houter
  exact (MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr
      (annularPairReflectionGenerators_lift_range E r x (zero_lt_one.trans hE) hr))

/-- On every free-group element this is the original lift, with unchanged native action. -/
theorem annularPairReflectionFreeEquiv_coe (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E)
    (w : FreeGroup (Fin 2)) :
    (annularPairReflectionFreeEquiv E r x hE hr hinner houter w : ℍ ≃ᵢ ℍ) =
      FreeGroup.lift (annularPairReflectionGenerators E r x (zero_lt_one.trans hE) hr) w := by
  rfl

theorem annularPairReflectionFreeEquiv_of_zero (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    (annularPairReflectionFreeEquiv E r x hE hr hinner houter
        (FreeGroup.of (0 : Fin 2)) : ℍ ≃ᵢ ℍ) =
      halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one) *
        halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE)) := by
  rw [annularPairReflectionFreeEquiv_coe, FreeGroup.lift_apply_of]
  rfl

theorem annularPairReflectionFreeEquiv_of_one (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    (annularPairReflectionFreeEquiv E r x hE hr hinner houter
        (FreeGroup.of (1 : Fin 2)) : ℍ ≃ᵢ ℍ) =
      halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr) *
        halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one) := by
  rw [annularPairReflectionFreeEquiv_coe, FreeGroup.lift_apply_of]
  rfl

theorem annularPairReflectionGroup_hasUniqueRoots (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    HasUniqueRoots (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) := by
  let e := annularPairReflectionFreeEquiv E r x hE hr hinner houter
  exact Function.Injective.hasUniqueRoots e.symm.toMonoidHom e.symm.injective

theorem annularPairReflectionGroup_isMulTorsionFree (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    IsMulTorsionFree (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) := by
  let e := annularPairReflectionFreeEquiv E r x hE hr hinner houter
  exact Function.Injective.isMulTorsionFree e.symm.toMonoidHom e.symm.injective

end LowDimensionalTopology.Geometry.Hyperbolic
