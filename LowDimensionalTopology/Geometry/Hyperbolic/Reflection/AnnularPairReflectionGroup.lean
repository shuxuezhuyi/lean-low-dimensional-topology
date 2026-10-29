module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularThreeMirrorDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleReflectionGroups
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDiscreteness
public import LowDimensionalTopology.Geometry.DiscreteGroups.Matrix

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The actual two-generator subgroup in the book's reflection-product order. -/
def annularPairReflectionGroup (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) :
    Subgroup (ℍ ≃ᵢ ℍ) :=
  let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
  let σ1 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 E hE)
  let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
  Subgroup.closure ({σ0 * σ1, σ2 * σ0} : Set (ℍ ≃ᵢ ℍ))

/-- The same two actual products act conformally, with their original real matrices. -/
theorem annularPairReflectionGroup_le_conformal (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) :
    annularPairReflectionGroup E r x hE hr ≤ halfPlaneConformalIsometryGroup := by
  have hprod (L M : HalfPlaneLine) :
      halfPlaneLineReflectionIsometry L * halfPlaneLineReflectionIsometry M ∈
        halfPlaneConformalIsometryGroup :=
    ⟨reflectionProductSL L M, (Fuchsian.reflectionProductSL_native L M).symm⟩
  dsimp only [annularPairReflectionGroup]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;> exact hprod _ _

/-- The actual pair-product subgroup inherits discreteness in its native topology. -/
theorem annularPairReflectionGroup_discrete (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    DiscreteTopology (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) := by
  let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
  let σ1 := halfPlaneLineReflectionIsometry
    (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE))
  let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
  let σ : Fin 3 → (ℍ ≃ᵢ ℍ) := ![σ0, σ1, σ2]
  let H : Subgroup (ℍ ≃ᵢ ℍ) := ⨆ i : Fin 3, Subgroup.zpowers (σ i)
  have hgen (i : Fin 3) : σ i ∈ H :=
    (le_iSup (fun j : Fin 3 => Subgroup.zpowers (σ j)) i) (Subgroup.mem_zpowers (σ i))
  have hle : annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr ≤ H := by
    change Subgroup.closure ({σ0 * σ1, σ2 * σ0} : Set (ℍ ≃ᵢ ℍ)) ≤ H
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change g ∈ ({σ0 * σ1, σ2 * σ0} : Set (ℍ ≃ᵢ ℍ)) at hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact H.mul_mem (hgen 0) (hgen 1)
    · exact H.mul_mem (hgen 2) (hgen 0)
  let : DiscreteTopology H :=
    annular_three_reflection_group_discrete E r x hE hr hinner houter
  exact DiscreteGroups.MatrixGroups.subgroup_discrete hle

/-- The actual Mobius-image model of the original pair-product group. -/
theorem annularPairReflectionHalfPlaneData (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    Fuchsian.HalfPlaneFuchsianGroup
      (Fuchsian.nativeConformalSubgroupMobiusHom
        (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr)
        (annularPairReflectionGroup_le_conformal E r x (zero_lt_one.trans hE) hr)).range := by
  let := annularPairReflectionGroup_discrete E r x hE hr hinner houter
  exact Fuchsian.nativeConformalSubgroup_halfPlaneData _ _

end LowDimensionalTopology.Geometry.Hyperbolic
