module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairNielsenCoreReflection
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeIsometryFreeCenters
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeMultiplicityPunctures
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.GroupTheory.OrderOfElement

/-! A free point can be chosen inside the literal original Nielsen lift.
The accepted quotient reflection consequently has a nontrivial restriction
of exact order two on that same core's native orbit image. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Fuchsian

/-- The accepted original quotient reflection moves a point inside the
native orbit image of the literal original Nielsen-core lift. -/
theorem annularPairQuotientReflection_exists_moved_in_originalCoreImage
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
    let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
    let C := orbitProjection G ℍ '' K
    let J := annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
    ∃ q ∈ C, J q ≠ q := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
  let C := orbitProjection G ℍ '' K
  let J := annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
  change ∃ q ∈ C, J q ≠ q
  have hnCore : (fuchsianNielsenCore P.cayleyData hNE).Nonempty := by
    obtain ⟨z, hz⟩ := (P.cayleyData.asFuchsianDisc.nielsenRegion_properties hNE).2.1
    exact ⟨⟨z, (P.cayleyData.asFuchsianDisc.nielsenRegion_properties hNE).1 hz⟩, hz⟩
  have hnK : K.Nonempty :=
    P.cayleyCoordinate.surjective.nonempty_preimage.mpr hnCore
  have hoK : IsOpen K :=
    (fuchsianNielsenCore_isOpen P.cayleyData hNE).preimage P.cayleyCoordinate.continuous
  have hmK : volume K ≠ 0 := ne_of_gt (Polygon.native_open_volume_pos hoK hnK)
  let σ : Fin 3 → (ℍ ≃ᵢ ℍ) :=
    ![halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one),
      halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE)),
      halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)]
  let H : Subgroup (ℍ ≃ᵢ ℍ) := ⨆ i : Fin 3, Subgroup.zpowers (σ i)
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
  let : Countable H := nativeDiscreteIsometrySubgroup_countable_of_discontinuous H
  obtain ⟨w, hwK, hw⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmK
    (ae_restrict_of_ae (nativeCountableIsometrySubgroup_free_points_ae H))
  refine ⟨orbitProjection G ℍ w, ⟨w, hwK, rfl⟩, ?_⟩
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

/-- The same original quotient reflection, restricted using its proved
preservation of the literal native Nielsen-core image. -/
def annularPairCoreReflection
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
    let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
    let C := orbitProjection G ℍ '' K
    C ≃ₜ C := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
  let C := orbitProjection G ℍ '' K
  let J := annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
  exact (J.image C).trans (Homeomorph.setCongr
    (annularPairQuotientReflection_preserves_originalCoreImage E r x hE hr hin hout))

/-- The restriction to the actual native core image has exact order two. -/
theorem annularPairCoreReflection_orderOf
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    orderOf (annularPairCoreReflection E r x hE hr hin hout) = 2 := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
  let C := orbitProjection G ℍ '' K
  let J := annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
  apply orderOf_eq_prime
  · apply Homeomorph.ext
    intro q
    apply Subtype.ext
    change J (J q.val) = q.val
    exact annularPairQuotientReflection_involutive E r x (zero_lt_one.trans hE) hr q.val
  · intro h
    obtain ⟨q, hq, hmoved⟩ :=
      annularPairQuotientReflection_exists_moved_in_originalCoreImage E r x hE hr hin hout
    let p : C := ⟨q, hq⟩
    have hp : annularPairCoreReflection E r x hE hr hin hout p = p :=
      congrArg (fun f : C ≃ₜ C => f p) h
    have hv := congrArg Subtype.val hp
    change J q = q at hv
    exact hmoved hv

end LowDimensionalTopology.Geometry.Hyperbolic
