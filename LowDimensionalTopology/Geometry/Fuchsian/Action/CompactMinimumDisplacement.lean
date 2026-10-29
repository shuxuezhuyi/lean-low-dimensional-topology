module

public import LowDimensionalTopology.Geometry.Fuchsian.Action.BoundedDisplacement
public import LowDimensionalTopology.External.LiZhongQC.Ch03.S14_PoincareMetric
public import Mathlib.Topology.Order.Compact

/-!
# Finitely many group elements have bounded minimum displacement on a compact set

The existing bounded-displacement theorem concerns the same actual upper-half
plane, group matrices and hyperbolic distance. The extreme value theorem
identifies its pointwise existence condition with the attained minimum on
each compact set. The real-infimum statement explicitly requires a nonempty
set; the attained-minimum version also handles the empty set correctly.

The original Poincare distance is identified with Mathlib's actual metric by
Wu Xiaobin's Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0).
See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- On a compact set, a bounded displacement exists exactly when the actual
minimum is attained below the same bound. This includes an empty compact set. -/
theorem compact_displacement_minimum_le_iff {K : Set ℍ} (hK : IsCompact K)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (M : ℝ) :
    (∃ z ∈ K, IsMinOn (fun w : ℍ => dist w (γ • w)) K z ∧ dist z (γ • z) ≤ M) ↔
      ∃ z ∈ K, dist z (γ • z) ≤ M := by
  constructor
  · rintro ⟨z, hz, _, hzM⟩
    exact ⟨z, hz, hzM⟩
  · rintro ⟨z, hz, hzM⟩
    obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn ⟨z, hz⟩
      (continuous_id.dist (continuous_const_smul γ)).continuousOn
    exact ⟨w, hw, hmin, ((isMinOn_iff.mp hmin) z hz).trans hzM⟩

/-- Only finitely many actual group matrices have an attained minimum
hyperbolic displacement on the given compact set below the original bound. -/
theorem finite_compact_minimum_displacement
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : LiZhongQC.IsFuchsian Γ)
    {K : Set ℍ} (hK : IsCompact K) (M : ℝ) :
    {γ | γ ∈ Γ ∧ ∃ z ∈ K,
      IsMinOn (fun w : ℍ => dist w (γ • w)) K z ∧ dist z (γ • z) ≤ M}.Finite := by
  simpa only [compact_displacement_minimum_le_iff hK] using
    finite_bounded_displacement hΓ hK M

/-- The literal real infimum is the same attained minimum whenever the compact
set is nonempty, with no change of the group or distance. -/
theorem compact_displacement_sInf_le_iff {K : Set ℍ} (hK : IsCompact K)
    (hne : K.Nonempty) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (M : ℝ) :
    sInf ((fun z : ℍ => dist z (γ • z)) '' K) ≤ M ↔
      ∃ z ∈ K, dist z (γ • z) ≤ M := by
  obtain ⟨w, hw, heq, hmin⟩ := hK.exists_sInf_image_eq_and_le hne
    (continuous_id.dist (continuous_const_smul γ)).continuousOn
  simp only [id_eq] at heq hmin
  constructor
  · intro h
    refine ⟨w, hw, ?_⟩
    rwa [heq] at h
  · rintro ⟨z, hz, hzM⟩
    rw [heq]
    exact (hmin z hz).trans hzM

/-- Finiteness with the original minimum written as the real infimum over K.
The assertion holds for every real bound, hence for every positive bound. -/
theorem finite_compact_infimum_displacement
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : LiZhongQC.IsFuchsian Γ)
    {K : Set ℍ} (hK : IsCompact K) (hne : K.Nonempty) (M : ℝ) :
    {γ | γ ∈ Γ ∧ sInf ((fun z : ℍ => dist z (γ • z)) '' K) ≤ M}.Finite := by
  simpa only [compact_displacement_sInf_le_iff hK hne] using
    finite_bounded_displacement hΓ hK M

/-- The same original minimum using the actual Poincare path distance.
That distance is finite on H and its real value equals the unchanged H metric. -/
theorem finite_compact_poincare_minimum_displacement
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : LiZhongQC.IsFuchsian Γ)
    {K : Set ℍ} (hK : IsCompact K) (hne : K.Nonempty) (M : ℝ) :
    {γ | γ ∈ Γ ∧ sInf ((fun z : ℍ =>
      (LiZhongQC.poincareDist LiZhongQC.upperHalf (z : ℂ) ((γ • z : ℍ) : ℂ)).toReal) '' K) ≤ M}.Finite := by
  simpa only [LiZhongQC.poincareDist_upperHalf, ENNReal.toReal_ofReal dist_nonneg] using
    finite_compact_infimum_displacement hΓ hK hne M

end LowDimensionalTopology.Geometry.Fuchsian
