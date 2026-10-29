module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonIntegral
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegionIntegral
public import Mathlib.Order.Filter.CountableInter

/-!
# Zero detection on the original native fundamental region

The original compatible class is zero when its representative is zero almost
everywhere on the given region. No compactness or connectedness is added.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

/-- Zero on the original fundamental region detects the entire compatible class. -/
theorem eq_zero_of_ae_zero_fundamentalRegion {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    {F : Set ℍ} (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (μ : Space Γ)
    (hzero : ∀ᵐ z ∂WeilPetersson.flatArea.restrict F, μ.val z = 0) : μ = 0 := by
  classical
  let : Countable Γ := (LiZhongQC.h36p_countable hΓ).to_subtype
  have hflat : ∀ᵐ z ∂flatMeasure, z ∈ F → μ.val z = 0 :=
    ae_imp_of_ae_restrict hzero
  have hzF : ∀ᵐ z : ℍ ∂volume, z ∈ F → μ.val z = 0 :=
    ae_hyperbolic_iff.mpr hflat
  have hfront : (volume : Measure ℍ) (frontier F) = 0 :=
    (Hyperbolic.halfPlane_volume_eq_zero_iff_planar_volume_eq_zero
      (frontier F)).mpr hF.2.2.2
  have hzC : ∀ᵐ z : ℍ ∂volume, z ∈ closure F → μ.val z = 0 := by
    filter_upwards [hzF, measure_eq_zero_iff_ae_notMem.mp hfront] with z hz hn
    intro hzc
    have hi : z ∈ interior F := by
      rw [← closure_sdiff_frontier F]
      exact ⟨hzc, hn⟩
    exact hz (interior_subset hi)
  have hall : ∀ᵐ z : ℍ ∂volume,
      ∀ γ : Γ, ((γ.val)⁻¹ • z : ℍ) ∈ closure F → μ.val z = 0 := by
    apply eventually_countable_forall.mpr
    intro γ
    have hc := (mem_compatibleSubmodule_iff μ.val).mp μ.property
      (γ.val)⁻¹ (Γ.inv_mem γ.property)
    have hpull := (measurePreserving_deck (γ.val)⁻¹).quasiMeasurePreserving.ae hzC
    filter_upwards [hc, hpull] with z hc hz
    intro hm
    rw [hc, hz hm, mul_zero]
  have hglobal : ∀ᵐ z : ℍ ∂volume, μ.val z = 0 := by
    filter_upwards [hall] with z hz
    let := P.nativeAction
    obtain ⟨g, y, hy, hgy⟩ := hF.2.2.1 z
    obtain ⟨A, hA, hAg⟩ := g.property
    have hAy : A • y = z := (P.nativeAction_realSL g A hAg y).symm.trans hgy
    apply hz ⟨A, hA⟩
    change A⁻¹ • z ∈ closure F
    rw [← hAy, inv_smul_smul]
    exact hy
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hglobal, Lp.coeFn_zero ℂ (⊤ : ℝ≥0∞) (volume : Measure ℍ)] with z hz h0
  exact hz.trans h0.symm

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
