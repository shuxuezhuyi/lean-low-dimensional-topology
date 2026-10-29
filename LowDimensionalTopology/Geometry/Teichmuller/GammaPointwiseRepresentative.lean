module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.Order.Filter.CountableInter

/-!
# Pointwise bounded representatives of the original compatible classes

Countability of the original Fuchsian group turns its almost-everywhere
compatibility equations into one invariant conull set. Keeping the original
representative on that set and using zero elsewhere gives the actual tensor
law at every point, with the unchanged original class-norm bound.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

/-- Every original compatible class for a Fuchsian group has an a.e.-equal
representative satisfying the full pointwise deck law and its original class
norm bound everywhere. No subunit condition or chosen good representative is
an additional premise. -/
theorem exists_pointwiseRepresentative {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (μ : Space Γ) :
    ∃ κ : ℍ → ℂ, κ =ᵐ[volume] (μ.val : ℍ → ℂ) ∧
      AEStronglyMeasurable κ (volume : Measure ℍ) ∧
      (∀ δ ∈ Γ, ∀ z : ℍ, κ z = phase δ z * κ (δ • z)) ∧
      ∀ z : ℍ, ‖κ z‖ ≤ ‖μ.val‖ := by
  classical
  let : Countable Γ := (LiZhongQC.h36p_countable hΓ).to_subtype
  let good : ℍ → Prop := fun z => ‖μ.val z‖ ≤ ‖μ.val‖ ∧
    ∀ δ : Γ, μ.val z = phase δ.val z * μ.val (δ.val • z)
  have hcompat : ∀ᵐ z : ℍ ∂volume,
      ∀ δ : Γ, μ.val z = phase δ.val z * μ.val (δ.val • z) := by
    apply eventually_countable_forall.mpr
    intro δ
    exact (mem_compatibleSubmodule_iff μ.val).mp μ.property δ.val δ.property
  have hgood : ∀ᵐ z : ℍ ∂volume, good z := by
    filter_upwards [lpInfinity_norm_ae_le μ.val, hcompat] with z hz hδ
    exact ⟨hz, hδ⟩
  let E : ℍ → Prop := fun z => ∀ γ : Γ, good (γ.val • z)
  have hE : ∀ᵐ z : ℍ ∂volume, E z := by
    apply eventually_countable_forall.mpr
    intro γ
    exact (measurePreserving_deck γ.val).quasiMeasurePreserving.ae hgood
  have hstable (δ : Γ) {z : ℍ} (hz : E z) : E (δ.val • z) := by
    intro γ
    have hh := hz (γ * δ)
    change good ((γ.val * δ.val) • z) at hh
    simpa only [mul_smul] using hh
  have hEinv (δ : Γ) (z : ℍ) : E (δ.val • z) ↔ E z := by
    constructor
    · intro hz
      have hh := hstable δ⁻¹ hz
      change E (δ.val⁻¹ • (δ.val • z)) at hh
      simpa only [inv_smul_smul] using hh
    · intro hz
      exact hstable δ hz
  have hbase (z : ℍ) (hz : E z) : good z := by
    have hh := hz (1 : Γ)
    change good ((1 : Deck) • z) at hh
    simpa only [one_smul] using hh
  let κ : ℍ → ℂ := fun z => if E z then μ.val z else 0
  have hκ : κ =ᵐ[volume] (μ.val : ℍ → ℂ) := by
    filter_upwards [hE] with z hz
    simp only [κ, ite_eq_left hz]
  refine ⟨κ, hκ, (Lp.aestronglyMeasurable μ.val).congr hκ.symm, ?_, ?_⟩
  · intro δ hδ z
    by_cases hz : E z
    · have hδz : E (δ • z) := (hEinv ⟨δ, hδ⟩ z).mpr hz
      simp only [κ, ite_eq_left hz, ite_eq_left hδz]
      exact (hbase z hz).2 ⟨δ, hδ⟩
    · have hδz : ¬ E (δ • z) := fun h => hz ((hEinv ⟨δ, hδ⟩ z).mp h)
      simp only [κ, ite_eq_right hz, ite_eq_right hδz, mul_zero]
  · intro z
    by_cases hz : E z
    · simpa only [κ, ite_eq_left hz] using (hbase z hz).1
    · simpa only [κ, ite_eq_right hz, norm_zero] using norm_nonneg μ.val

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
