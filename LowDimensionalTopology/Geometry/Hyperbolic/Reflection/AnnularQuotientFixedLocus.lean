module

public import LowDimensionalTopology.Unproved.Hyperbolic.AnnularReflectionTorsion
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularFullMirrorQuotientAction
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeIsometryDiscontinuity
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusDiscontinuity
public import Mathlib.Tactic.FinCases

/-!
# The complete fixed locus on the original annular pair-product quotient

Finite-order conjugacy in the same full mirror group gives the reverse
inclusion from every actual fixed quotient point to an original mirror image.
No component count or seam geometry is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

open LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Fuchsian

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
variable (hin : 1 + r < x) (hout : x + r < E)

local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "G" => annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
local notation "J" => annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
local notation "π" => orbitProjection G ℍ

/-- Under the explicit native finite-order conjugacy input, the entire fixed
locus on the unchanged quotient is exactly the union of the three mirror images. -/
theorem annularPairQuotientReflection_fixed_iff_mirror_projection_of_torsion
    (hTorsion : Unproved.Hyperbolic.AnnularReflectionTorsion E r x hE hr hin hout)
    (q : orbitQuotient G ℍ) :
    J q = q ↔ ∃ i : Fin 3, ∃ z : ℍ, z ∈ (S i).carrier ∧ π z = q := by
  let σ : Fin 3 → (ℍ ≃ᵢ ℍ) := fun i => halfPlaneLineReflectionIsometry (S i)
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
  have hσvec : σ =
      ![halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one),
        halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE)),
        halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)] := by
    funext i
    fin_cases i <;> rfl
  let : DiscreteTopology H := by
    change DiscreteTopology (⨆ i : Fin 3, Subgroup.zpowers (σ i) : Subgroup (ℍ ≃ᵢ ℍ))
    rw [hσvec]
    exact annular_three_reflection_group_discrete E r x hE hr hin hout
  have hClass : ∀ h ∈ H, h ≠ 1 → IsOfFinOrder h →
      ∃ k ∈ H, ∃ i : Fin 3, h = k * σ i * k⁻¹ := hTorsion
  obtain ⟨w, rfl⟩ := orbitProjection_surjective G ℍ q
  constructor
  · intro hfixed
    have hp : π (σ 0 • w) = π w := by
      change π (σ 0 • w) = π w at hfixed
      exact hfixed
    obtain ⟨g, hg⟩ := (Quotient.exact hp : MulAction.orbitRel G ℍ (σ 0 • w) w)
    let h : ℍ ≃ᵢ ℍ := g.val⁻¹ * σ 0
    have hmem : h ∈ H := H.mul_mem (H.inv_mem (hGH g.property)) (hσ 0)
    have hfix : h • w = w := by
      change (g.val⁻¹ * σ 0) • w = w
      rw [mul_smul, ← hg]
      exact inv_smul_smul g.val w
    have hne : h ≠ 1 := by
      intro he
      have heq : σ 0 = g.val := by
        have hm := congrArg (fun a : ℍ ≃ᵢ ℍ => g.val * a) he
        simpa only [h, mul_inv_cancel_left, mul_one] using hm
      apply halfPlaneLineReflectionIsometry_not_conformal (S 0)
      change σ 0 ∈ halfPlaneConformalIsometryGroup
      rw [heq]
      exact annularPairReflectionGroup_le_conformal E r x (zero_lt_one.trans hE) hr g.property
    have hfin : IsOfFinOrder h := by
      let a : H := ⟨h, hmem⟩
      have hafix : a • w = w := hfix
      have hfinite := (nativeIsometrySubgroup_discontinuous H).finite_stabilizer w
      have hfa : IsOfFinOrder a := isOfFinOrder_of_finite_stabilizer a w hfinite hafix
      exact H.subtype.isOfFinOrder hfa
    obtain ⟨k, hk, i, hconj⟩ := hClass h hmem hne hfin
    let v : ℍ := k⁻¹ • w
    have hvfix : (S i).reflection v = v := by
      have hh := hfix
      rw [hconj] at hh
      have hc := congrArg (fun u : ℍ => k⁻¹ • u) hh
      change σ i • v = v
      simpa only [v, mul_smul, inv_smul_smul] using hc
    have hv : v ∈ (S i).carrier := ((S i).reflection_fixed_iff v).mp hvfix
    have hJv : J (π v) = π v :=
      annularPairQuotientReflection_fixes_mirror_projection E r x
        (zero_lt_one.trans hE) hr i v hv
    have hkv : π (k • v) = π v :=
      annularPairFullMirror_fixes_fixed_projection E r x (zero_lt_one.trans hE) hr
        k hk v hJv
    have hkw : k • v = w := by
      change k • (k⁻¹ • w) = w
      exact smul_inv_smul k w
    exact ⟨i, v, hv, hkv.symm.trans (congrArg π hkw)⟩
  · rintro ⟨i, z, hz, hproj⟩
    rw [← hproj]
    exact annularPairQuotientReflection_fixes_mirror_projection E r x
      (zero_lt_one.trans hE) hr i z hz

end LowDimensionalTopology.Geometry.Hyperbolic
