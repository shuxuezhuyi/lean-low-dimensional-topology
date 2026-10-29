module

public import LowDimensionalTopology.Geometry.Teichmuller.CoefficientRealMobiusIsometry
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# The same measurable fundamental region under actual real Möbius conjugation

The actual image region retains covering, uniqueness on the interior and the
null boundary. The matrix action on the upper half-plane supplies the local
homeomorphism; the existing real Möbius null-set theorem transports the same
boundary, without a new geometric or finite-area premise.

The actual region and null-set APIs reuse Wu Xiaobin's Li-Zhong-QC
formalization, Apache-2.0, pinned commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open GammaMeasurableBeltrami

private def upperMobiusPartial (Q : Deck) : OpenPartialHomeomorph ℂ ℂ where
  toFun := LiZhongQC.h36p_m Q
  invFun := LiZhongQC.h36p_m Q⁻¹
  source := LiZhongQC.upperHalf
  target := LiZhongQC.upperHalf
  map_source' := fun _ hz => LiZhongQC.h36p_m_mem Q hz
  map_target' := fun _ hz => LiZhongQC.h36p_m_mem Q⁻¹ hz
  left_inv' := fun _ hz => LiZhongQC.h36p_a_inv_m Q hz
  right_inv' := fun _ hz => by simpa only [inv_inv] using LiZhongQC.h36p_a_inv_m Q⁻¹ hz
  continuousOn_toFun := fun _ hz =>
    (LiZhongQC.h36p_m_hasDerivAt Q hz).continuousAt.continuousWithinAt
  continuousOn_invFun := fun _ hz =>
    (LiZhongQC.h36p_m_hasDerivAt Q⁻¹ hz).continuousAt.continuousWithinAt
  open_source := LiZhongQC.isOpen_upperHalf
  open_target := LiZhongQC.isOpen_upperHalf

private theorem interior_forward (Q : Deck) {F : Set ℂ}
    (hFH : F ⊆ LiZhongQC.upperHalf) {z : ℂ} (hz : z ∈ interior F) :
    LiZhongQC.h36p_m Q z ∈ interior (LiZhongQC.h36p_m Q '' F) := by
  have hopen : IsOpen (LiZhongQC.h36p_m Q '' interior F) :=
    (upperMobiusPartial Q).isOpen_image_of_subset_source isOpen_interior
      (interior_subset.trans hFH)
  exact interior_maximal (image_mono interior_subset) hopen ⟨z, hz, rfl⟩

private theorem interior_image_iff (Q : Deck) {F : Set ℂ}
    (hFH : F ⊆ LiZhongQC.upperHalf) {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    LiZhongQC.h36p_m Q z ∈ interior (LiZhongQC.h36p_m Q '' F) ↔ z ∈ interior F := by
  constructor
  · intro hi
    have himage : LiZhongQC.h36p_m Q '' F ⊆ LiZhongQC.upperHalf := by
      rintro _ ⟨w, hw, rfl⟩
      exact LiZhongQC.h36p_m_mem Q (hFH hw)
    have hback := interior_forward Q⁻¹ himage hi
    have hsubset : LiZhongQC.h36p_m Q⁻¹ '' (LiZhongQC.h36p_m Q '' F) ⊆ F := by
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [LiZhongQC.h36p_a_inv_m Q (hFH hw)] using hw
    rw [LiZhongQC.h36p_a_inv_m Q hz] at hback
    exact interior_mono hsubset hback
  · exact interior_forward Q hFH

/-- The same actual image region is a complete measurable fundamental region
for the exact conjugate group, retaining its original null-boundary condition. -/
theorem fundamentalDomainH_realMobius_image
    (Γ : Subgroup Deck) (Q : Deck) {F : Set ℂ}
    (hF : LiZhongQC.IsFundamentalDomainH Γ F) :
    LiZhongQC.IsFundamentalDomainH (LiZhongQC.conjGroup Γ Q)
      (LiZhongQC.h36p_m Q '' F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact LiZhongQC.h36p_m_mem Q (hF.1 hz)
  · rw [LiZhongQC.h36p_a_image_eq Q hF.1]
    exact ((LiZhongQC.h36p_m_measurable Q⁻¹) hF.2.1).inter
      LiZhongQC.isOpen_upperHalf.measurableSet
  · intro τ
    obtain ⟨γ, hγ, hγF⟩ := hF.2.2.1 (Q⁻¹ • τ)
    refine ⟨Q * γ * Q⁻¹, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩, ?_⟩
    refine ⟨((γ • (Q⁻¹ • τ) : ℍ) : ℂ), hγF, ?_⟩
    simp only [LiZhongQC.h36p_m_coe, mul_smul]
  · intro τ₁ τ₂ hτ₁ hτ₂ horbit
    have hi₁ : ((Q⁻¹ • τ₁ : ℍ) : ℂ) ∈ interior F := by
      apply (interior_image_iff Q hF.1 (Q⁻¹ • τ₁).im_pos).mp
      simpa only [LiZhongQC.h36p_m_coe, smul_inv_smul] using hτ₁
    have hi₂ : ((Q⁻¹ • τ₂ : ℍ) : ℂ) ∈ interior F := by
      apply (interior_image_iff Q hF.1 (Q⁻¹ • τ₂).im_pos).mp
      simpa only [LiZhongQC.h36p_m_coe, smul_inv_smul] using hτ₂
    obtain ⟨δ, hδ, hδτ⟩ := horbit
    obtain ⟨γ, hγ, hγδ⟩ := Subgroup.mem_map.mp hδ
    change Q * γ * Q⁻¹ = δ at hγδ
    have horiginal : γ • (Q⁻¹ • τ₁) = Q⁻¹ • τ₂ := by
      have h := congrArg (fun τ : ℍ => Q⁻¹ • τ) hδτ
      rw [← hγδ] at h
      simpa only [mul_smul, inv_smul_smul] using h
    have hsame := hF.2.2.2.1 _ _ hi₁ hi₂ ⟨γ, hγ, horiginal⟩
    have h := congrArg (fun τ : ℍ => Q • τ) hsame
    simpa only [smul_inv_smul] using h
  · have hsubset :
        (LiZhongQC.h36p_m Q '' F) \ interior (LiZhongQC.h36p_m Q '' F) ⊆
          LiZhongQC.upperHalf ∩ LiZhongQC.h36p_m Q⁻¹ ⁻¹' (F \ interior F) := by
      rintro _ ⟨⟨z, hz, rfl⟩, hout⟩
      refine ⟨LiZhongQC.h36p_m_mem Q (hF.1 hz), ?_⟩
      change LiZhongQC.h36p_m Q⁻¹ (LiZhongQC.h36p_m Q z) ∈ F \ interior F
      rw [LiZhongQC.h36p_a_inv_m Q (hF.1 hz)]
      exact ⟨hz, fun hi => hout (interior_forward Q hF.1 hi)⟩
    exact measure_mono_null hsubset (LiZhongQC.h36p_a_preimage_null Q⁻¹ hF.2.2.2.2)

end LowDimensionalTopology.Geometry.Teichmuller
