module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairReflectionGroup
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.SingleMirrorGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.OrbitQuotient
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

/-! The first mirror induces an involution on the native annular pair-product
orbit quotient. All three mirrors induce the same map, and points on their
projections are fixed by this involution. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action

/-- The three literal mirrors of the annular construction, in source order. -/
def annularPairReflectionMirrors (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) :
    Fin 3 → HalfPlaneLine :=
  ![HalfPlaneLine.circle 0 1 zero_lt_one,
    HalfPlaneLine.circle 0 E hE, HalfPlaneLine.circle x r hr]

/-- The first actual mirror normalizes the unchanged pair-product group. -/
theorem annularPairReflectionGroup_firstMirror_normalizes
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) :
    halfPlaneLineReflectionIsometry (annularPairReflectionMirrors E r x hE hr 0) ∈
      Subgroup.normalizer (annularPairReflectionGroup E r x hE hr : Set (ℍ ≃ᵢ ℍ)) := by
  let S := annularPairReflectionMirrors E r x hE hr
  let σ : Fin 3 → (ℍ ≃ᵢ ℍ) := fun i => halfPlaneLineReflectionIsometry (S i)
  let G := annularPairReflectionGroup E r x hE hr
  let c := MulAut.conj (σ 0)
  have hsq (i : Fin 3) : σ i * σ i = 1 := by
    simpa only [pow_two] using nativeLineReflection_square (S i)
  have hinv (i : Fin 3) : (σ i)⁻¹ = σ i :=
    inv_eq_of_mul_eq_one_left (hsq i)
  have hgen0 : σ 0 * σ 1 ∈ G := by
    change σ 0 * σ 1 ∈ Subgroup.closure ({σ 0 * σ 1, σ 2 * σ 0} : Set (ℍ ≃ᵢ ℍ))
    exact Subgroup.subset_closure (by simp)
  have hgen1 : σ 2 * σ 0 ∈ G := by
    change σ 2 * σ 0 ∈ Subgroup.closure ({σ 0 * σ 1, σ 2 * σ 0} : Set (ℍ ≃ᵢ ℍ))
    exact Subgroup.subset_closure (by simp)
  have hc0 : c (σ 0 * σ 1) = (σ 0 * σ 1)⁻¹ := by
    change σ 0 * (σ 0 * σ 1) * (σ 0)⁻¹ = (σ 0 * σ 1)⁻¹
    rw [show σ 0 * (σ 0 * σ 1) = σ 1 by
      rw [← mul_assoc, hsq 0, one_mul]]
    rw [mul_inv_rev, hinv 0, hinv 1]
  have hc1 : c (σ 2 * σ 0) = (σ 2 * σ 0)⁻¹ := by
    change σ 0 * (σ 2 * σ 0) * (σ 0)⁻¹ = (σ 2 * σ 0)⁻¹
    calc
      σ 0 * (σ 2 * σ 0) * (σ 0)⁻¹ = σ 0 * σ 2 := by group
      _ = (σ 2 * σ 0)⁻¹ := by rw [mul_inv_rev, hinv 0, hinv 2]
  have hc : ∀ g ∈ G, c g ∈ G := by
    intro g hg
    change g ∈ Subgroup.closure ({σ 0 * σ 1, σ 2 * σ 0} : Set (ℍ ≃ᵢ ℍ)) at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
        simp only [mem_insert_iff, mem_singleton_iff] at hg
        rcases hg with rfl | rfl
        · rw [hc0]
          exact G.inv_mem hgen0
        · rw [hc1]
          exact G.inv_mem hgen1
    | one => simpa only [map_one] using G.one_mem
    | mul a b ha hb iha ihb =>
        simpa only [map_mul] using G.mul_mem iha ihb
    | inv a ha iha => simpa only [map_inv] using G.inv_mem iha
  change σ 0 ∈ Subgroup.normalizer (G : Set (ℍ ≃ᵢ ℍ))
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact hc g
  · intro hg
    have hh := hc (c g) hg
    have he : c (c g) = g := by
      change σ 0 * (σ 0 * g * (σ 0)⁻¹) * (σ 0)⁻¹ = g
      calc
        σ 0 * (σ 0 * g * (σ 0)⁻¹) * (σ 0)⁻¹ =
            (σ 0 * σ 0) * g * ((σ 0)⁻¹ * (σ 0)⁻¹) := by group
        _ = g := by rw [hsq 0, hinv 0, hsq 0, one_mul, mul_one]
    simpa only [he] using hh

theorem annularPairReflection_firstMirror_orbitRel_iff
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) (u v : ℍ) :
    MulAction.orbitRel (annularPairReflectionGroup E r x hE hr) ℍ u v ↔
      MulAction.orbitRel (annularPairReflectionGroup E r x hE hr) ℍ
        ((annularPairReflectionMirrors E r x hE hr 0).reflection u)
        ((annularPairReflectionMirrors E r x hE hr 0).reflection v) := by
  let G := annularPairReflectionGroup E r x hE hr
  let σ := halfPlaneLineReflectionIsometry (annularPairReflectionMirrors E r x hE hr 0)
  have hnorm : σ ∈ Subgroup.normalizer (G : Set (ℍ ≃ᵢ ℍ)) :=
    annularPairReflectionGroup_firstMirror_normalizes E r x hE hr
  have hsq : σ * σ = 1 := by
    simpa only [pow_two] using
      nativeLineReflection_square (annularPairReflectionMirrors E r x hE hr 0)
  have hf : ∀ {a b : ℍ}, MulAction.orbitRel G ℍ a b →
      MulAction.orbitRel G ℍ (σ • a) (σ • b) := by
    rintro a b ⟨g, hg⟩
    refine ⟨⟨σ * g.val * σ⁻¹,
      (Subgroup.mem_normalizer_iff.mp hnorm g.val).mp g.property⟩, ?_⟩
    change (σ * g.val * σ⁻¹) • (σ • b) = σ • a
    rw [mul_smul, mul_smul, inv_smul_smul]
    exact congrArg (fun w : ℍ => σ • w) hg
  change MulAction.orbitRel G ℍ u v ↔ MulAction.orbitRel G ℍ (σ • u) (σ • v)
  refine ⟨hf, ?_⟩
  intro h
  have hh := hf h
  simpa only [← mul_smul, hsq, one_smul] using hh

/-- The actual first reflection descends to a homeomorphism of the original native orbit quotient. -/
def annularPairQuotientReflection (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) :
    orbitQuotient (annularPairReflectionGroup E r x hE hr) ℍ ≃ₜ
      orbitQuotient (annularPairReflectionGroup E r x hE hr) ℍ :=
  Homeomorph.Quotient.congr
    (halfPlaneLineReflectionIsometry (annularPairReflectionMirrors E r x hE hr 0)).toHomeomorph
    (annularPairReflection_firstMirror_orbitRel_iff E r x hE hr)

@[simp]
theorem annularPairQuotientReflection_projection
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) (z : ℍ) :
    annularPairQuotientReflection E r x hE hr
        (orbitProjection (annularPairReflectionGroup E r x hE hr) ℍ z) =
      orbitProjection (annularPairReflectionGroup E r x hE hr) ℍ
        ((annularPairReflectionMirrors E r x hE hr 0).reflection z) := rfl

/-- The descended map squares to the identity on the same actual quotient. -/
theorem annularPairQuotientReflection_involutive
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) :
    Function.Involutive (annularPairQuotientReflection E r x hE hr) := by
  intro q
  induction q using Quotient.inductionOn with
  | h z =>
      change annularPairQuotientReflection E r x hE hr
        (annularPairQuotientReflection E r x hE hr
          (orbitProjection (annularPairReflectionGroup E r x hE hr) ℍ z)) =
        orbitProjection (annularPairReflectionGroup E r x hE hr) ℍ z
      rw [annularPairQuotientReflection_projection,
        annularPairQuotientReflection_projection,
        (annularPairReflectionMirrors E r x hE hr 0).reflection_involutive z]

/-- All three original mirrors induce the same map on the actual pair-product quotient. -/
theorem annularPairQuotientReflection_mirror_projection
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) (i : Fin 3) (z : ℍ) :
    annularPairQuotientReflection E r x hE hr
        (orbitProjection (annularPairReflectionGroup E r x hE hr) ℍ z) =
      orbitProjection (annularPairReflectionGroup E r x hE hr) ℍ
        ((annularPairReflectionMirrors E r x hE hr i).reflection z) := by
  let S := annularPairReflectionMirrors E r x hE hr
  let σ : Fin 3 → (ℍ ≃ᵢ ℍ) := fun j => halfPlaneLineReflectionIsometry (S j)
  let G := annularPairReflectionGroup E r x hE hr
  have hgen0 : σ 0 * σ 1 ∈ G := by
    change σ 0 * σ 1 ∈ Subgroup.closure ({σ 0 * σ 1, σ 2 * σ 0} : Set (ℍ ≃ᵢ ℍ))
    exact Subgroup.subset_closure (by simp)
  have hgen1 : σ 2 * σ 0 ∈ G := by
    change σ 2 * σ 0 ∈ Subgroup.closure ({σ 0 * σ 1, σ 2 * σ 0} : Set (ℍ ≃ᵢ ℍ))
    exact Subgroup.subset_closure (by simp)
  rw [annularPairQuotientReflection_projection]
  change orbitProjection G ℍ ((S 0).reflection z) =
    orbitProjection G ℍ ((S i).reflection z)
  fin_cases i
  · rfl
  · have h := orbitProjection_smul G ℍ (⟨σ 0 * σ 1, hgen0⟩ : G) ((S 1).reflection z)
    change orbitProjection G ℍ
      ((S 0).reflection ((S 1).reflection ((S 1).reflection z))) =
        orbitProjection G ℍ ((S 1).reflection z) at h
    rw [(S 1).reflection_involutive z] at h
    exact h
  · have h := orbitProjection_smul G ℍ (⟨σ 2 * σ 0, hgen1⟩ : G) ((S 0).reflection z)
    change orbitProjection G ℍ
      ((S 2).reflection ((S 0).reflection ((S 0).reflection z))) =
        orbitProjection G ℍ ((S 0).reflection z) at h
    rw [(S 0).reflection_involutive z] at h
    exact h.symm

/-- Each point on any of the three literal mirrors projects to a fixed point. -/
theorem annularPairQuotientReflection_fixes_mirror_projection
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) (i : Fin 3) (z : ℍ)
    (hz : z ∈ (annularPairReflectionMirrors E r x hE hr i).carrier) :
    annularPairQuotientReflection E r x hE hr
        (orbitProjection (annularPairReflectionGroup E r x hE hr) ℍ z) =
      orbitProjection (annularPairReflectionGroup E r x hE hr) ℍ z := by
  rw [annularPairQuotientReflection_mirror_projection E r x hE hr i z,
    ((annularPairReflectionMirrors E r x hE hr i).reflection_fixed_iff z).mpr hz]

end LowDimensionalTopology.Geometry.Hyperbolic
