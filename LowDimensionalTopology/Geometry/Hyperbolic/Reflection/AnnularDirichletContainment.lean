module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularMirrorDistanceReduction
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeLineReflections
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairReflectionGroup
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.NativeClosedDirichletCover
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleProperness

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Hyperbolic

/-- The original two-generator closed Dirichlet set avoids all four open bad caps. -/
theorem annular_closedDirichlet_subset_four_cap_complement
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) :
    let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
    let σ1 := halfPlaneLineReflectionIsometry
      (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE))
    let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
    let K := Subgroup.closure ({σ0 * σ1, σ2 * σ0} : Set (ℍ ≃ᵢ ℍ))
    let AO := {z : ℍ | E < ‖(z : ℂ)‖}
    let AB := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ < r}
    nativeClosedDirichlet K UpperHalfPlane.I ⊆
      (AO ∪ AB ∪ σ0 '' AO ∪ σ0 '' AB)ᶜ := by
  let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
  let σ1 := halfPlaneLineReflectionIsometry
    (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE))
  let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
  let K := Subgroup.closure ({σ0 * σ1, σ2 * σ0} : Set (ℍ ≃ᵢ ℍ))
  let AO := {z : ℍ | E < ‖(z : ℂ)‖}
  let AB := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ < r}
  change nativeClosedDirichlet K UpperHalfPlane.I ⊆
    (AO ∪ AB ∪ σ0 '' AO ∪ σ0 '' AB)ᶜ
  have hγ1 : σ0 * σ1 ∈ K := Subgroup.subset_closure (Or.inl rfl)
  have hγ2 : σ2 * σ0 ∈ K := Subgroup.subset_closure (Or.inr (mem_singleton _))
  have hI : σ0 UpperHalfPlane.I = UpperHalfPlane.I := by
    apply ((HalfPlaneLine.circle 0 1 zero_lt_one).reflection_fixed_iff _).mpr
    change ‖(UpperHalfPlane.I : ℂ) - (0 : ℂ)‖ = 1
    simp only [UpperHalfPlane.coe_I, sub_zero, Complex.norm_I]
  have hbase (u : ℍ) : dist (σ0 u) UpperHalfPlane.I = dist u UpperHalfPlane.I := by
    calc
      _ = dist (σ0 u) (σ0 UpperHalfPlane.I) := congrArg (dist (σ0 u)) hI.symm
      _ = _ := σ0.dist_eq u UpperHalfPlane.I
  intro z hz hbad
  rcases hbad with ((hzO | hzB) | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩
  · have hmin := hz ⟨(σ0 * σ1)⁻¹, K.inv_mem hγ1⟩
    change dist z UpperHalfPlane.I ≤ dist z (σ1 (σ0 UpperHalfPlane.I)) at hmin
    rw [hI] at hmin
    exact (not_lt_of_ge hmin) (outerCircle_reflection_I_dist_lt E hE hzO)
  · have hmin := hz ⟨σ2 * σ0, hγ2⟩
    change dist z UpperHalfPlane.I ≤ dist z (σ2 (σ0 UpperHalfPlane.I)) at hmin
    rw [hI] at hmin
    exact (not_lt_of_ge hmin) (smallCircle_reflection_I_dist_lt r x hr hinner hzB)
  · have hmin := hz ⟨σ0 * σ1, hγ1⟩
    change dist (σ0 u) UpperHalfPlane.I ≤
      dist (σ0 u) (σ0 (σ1 UpperHalfPlane.I)) at hmin
    rw [hbase u, σ0.dist_eq] at hmin
    exact (not_lt_of_ge hmin) (outerCircle_reflection_I_dist_lt E hE hu)
  · have hmin := hz ⟨(σ2 * σ0)⁻¹, K.inv_mem hγ2⟩
    change dist (σ0 u) UpperHalfPlane.I ≤
      dist (σ0 u) (σ0 (σ2 UpperHalfPlane.I)) at hmin
    rw [hbase u, σ0.dist_eq] at hmin
    exact (not_lt_of_ge hmin) (smallCircle_reflection_I_dist_lt r x hr hinner hu)

/-- Under actual discreteness and conformality, the same weak four-cap complement covers. -/
theorem annular_four_cap_complement_cover
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) :
    let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
    let σ1 := halfPlaneLineReflectionIsometry
      (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE))
    let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
    let K := Subgroup.closure ({σ0 * σ1, σ2 * σ0} : Set (ℍ ≃ᵢ ℍ))
    let AO := {z : ℍ | E < ‖(z : ℂ)‖}
    let AB := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ < r}
    DiscreteTopology K → K ≤ halfPlaneConformalIsometryGroup →
      (⋃ g : K, g.val '' (AO ∪ AB ∪ σ0 '' AO ∪ σ0 '' AB)ᶜ) = univ := by
  let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
  let σ1 := halfPlaneLineReflectionIsometry
    (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE))
  let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
  let K := Subgroup.closure ({σ0 * σ1, σ2 * σ0} : Set (ℍ ≃ᵢ ℍ))
  let AO := {z : ℍ | E < ‖(z : ℂ)‖}
  let AB := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ < r}
  change DiscreteTopology K → K ≤ halfPlaneConformalIsometryGroup →
    (⋃ g : K, g.val '' (AO ∪ AB ∪ σ0 '' AO ∪ σ0 '' AB)ᶜ) = univ
  intro hDiscrete hConformal
  let : DiscreteTopology K := hDiscrete
  exact native_closed_region_cover_of_dirichlet K
    (nativeConformalSubgroup_discontinuous K hConformal) UpperHalfPlane.I
    (AO ∪ AB ∪ σ0 '' AO ∪ σ0 '' AB)ᶜ
    (annular_closedDirichlet_subset_four_cap_complement E r x hE hr hinner)

/-- The original annular pair-product group covers by the same weak four-cap complement. -/
theorem annularPairReflectionGroup_four_cap_complement_cover
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hinner : 1 + r < x) (houter : x + r < E) :
    let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
    let K := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
    let AO := {z : ℍ | E < ‖(z : ℂ)‖}
    let AB := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ < r}
    (⋃ g : K, g.val '' (AO ∪ AB ∪ σ0 '' AO ∪ σ0 '' AB)ᶜ) = univ := by
  exact annular_four_cap_complement_cover E r x hE hr hinner
    (annularPairReflectionGroup_discrete E r x hE hr hinner houter)
    (annularPairReflectionGroup_le_conformal E r x (zero_lt_one.trans hE) hr)

end LowDimensionalTopology.Geometry.Fuchsian
