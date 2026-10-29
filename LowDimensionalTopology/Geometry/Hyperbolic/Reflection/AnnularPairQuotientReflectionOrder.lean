module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairQuotientReflection
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeIsometryFreeCenters
public import Mathlib.GroupTheory.OrderOfElement

/-! The original annular quotient reflection moves an actual quotient point
and has exact order two. The source annular separation assumptions give the
full three-mirror group's existing native discreteness and a free point. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Fuchsian

/-- The original annular quotient reflection moves a point of the same actual quotient. -/
theorem annularPairQuotientReflection_exists_moved
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    ∃ q : orbitQuotient (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) ℍ,
      annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr q ≠ q := by
  let σ : Fin 3 → (ℍ ≃ᵢ ℍ) :=
    ![halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one),
      halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE)),
      halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)]
  let H : Subgroup (ℍ ≃ᵢ ℍ) := ⨆ i : Fin 3, Subgroup.zpowers (σ i)
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  have hσ (i : Fin 3) : σ i ∈ H :=
    (le_iSup (fun j : Fin 3 => Subgroup.zpowers (σ j)) i) (Subgroup.mem_zpowers (σ i))
  have hGH : G ≤ H := by
    change Subgroup.closure ({σ 0 * σ 1, σ 2 * σ 0} : Set (ℍ ≃ᵢ ℍ)) ≤ H
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [mem_insert_iff, mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact H.mul_mem (hσ 0) (hσ 1)
    · exact H.mul_mem (hσ 2) (hσ 0)
  let : DiscreteTopology H :=
    annular_three_reflection_group_discrete E r x hE hr hin hout
  obtain ⟨w, hw⟩ := nativeDiscreteIsometrySubgroup_exists_free_point H
  refine ⟨orbitProjection G ℍ w, ?_⟩
  intro hfix
  have hp : orbitProjection G ℍ (σ 0 • w) = orbitProjection G ℍ w := by
    change orbitProjection G ℍ (σ 0 • w) = orbitProjection G ℍ w at hfix
    exact hfix
  obtain ⟨g, hg⟩ := (Quotient.exact hp : MulAction.orbitRel G ℍ (σ 0 • w) w)
  let k : H := ⟨g.val⁻¹ * σ 0, H.mul_mem (H.inv_mem (hGH g.property)) (hσ 0)⟩
  have hk : k • w = w := by
    change (g.val⁻¹ * σ 0) • w = w
    rw [mul_smul, ← hg]
    exact inv_smul_smul g.val w
  have hke : g.val⁻¹ * σ 0 = 1 := congrArg Subtype.val (hw k hk)
  have he : σ 0 = g.val := by
    have hh := congrArg (fun a : ℍ ≃ᵢ ℍ => g.val * a) hke
    simpa only [mul_inv_cancel_left, mul_one] using hh
  apply halfPlaneLineReflectionIsometry_not_conformal (HalfPlaneLine.circle 0 1 zero_lt_one)
  change σ 0 ∈ halfPlaneConformalIsometryGroup
  rw [he]
  exact annularPairReflectionGroup_le_conformal E r x (zero_lt_one.trans hE) hr g.property

/-- The actual quotient reflection is not the identity homeomorphism. -/
theorem annularPairQuotientReflection_ne_one
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr ≠ 1 := by
  obtain ⟨q, hq⟩ := annularPairQuotientReflection_exists_moved E r x hE hr hin hout
  intro h
  exact hq (by simp only [h, Homeomorph.one_apply])

/-- In the source annular range, the original quotient reflection has exact order two. -/
theorem annularPairQuotientReflection_orderOf
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    orderOf (annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr) = 2 := by
  apply orderOf_eq_prime
  · apply Homeomorph.ext
    intro q
    change annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
        (annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr q) = q
    exact annularPairQuotientReflection_involutive E r x (zero_lt_one.trans hE) hr q
  · exact annularPairQuotientReflection_ne_one E r x hE hr hin hout

end LowDimensionalTopology.Geometry.Hyperbolic
