module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaLpOperators
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Real Möbius normalization of the literal Beltrami Hermitian pairing

Both actual pullback slots retain their unit phases, which cancel under the
measure-preserving action and the same preimage integration region.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson

open GammaMeasurableBeltrami

/-- The same actual Möbius pullback in both slots preserves the original
Hermitian pairing when the actual integration region is pulled back too. -/
theorem beltramiPairing_realMobiusPullback (M : Deck) (F : Set ℍ)
    (hF : MeasurableSet F) (μ ν : Ambient) :
    beltramiPairing ((fun z : ℍ => M • z) ⁻¹' F) (pullback M μ) (pullback M ν) =
      beltramiPairing F μ ν := by
  have hpre : MeasurableSet ((fun z : ℍ => M • z) ⁻¹' F) :=
    hF.preimage (measurePreserving_deck M).measurable
  have hsmul : MeasurableEmbedding (fun z : ℍ => M • z) :=
    (Homeomorph.smul M).measurableEmbedding
  have hcancel (z : ℍ) : phase M z * conj (phase M z) = 1 := by
    rw [Complex.mul_conj', norm_phase M z]
    simp
  rw [beltramiPairing_eq_hyperbolicIntegral _ hpre,
    beltramiPairing_eq_hyperbolicIntegral _ hF]
  calc
    (∫ z in (fun z : ℍ => M • z) ⁻¹' F,
        pullback M μ z * conj (pullback M ν z) ∂(volume : Measure ℍ)) =
        ∫ z in (fun z : ℍ => M • z) ⁻¹' F,
          μ (M • z) * conj (ν (M • z)) ∂(volume : Measure ℍ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (pullback_coe_ae M μ),
        ae_restrict_of_ae (pullback_coe_ae M ν)] with z hμ hν
      rw [hμ, hν]
      calc
        (phase M z * μ (M • z)) * conj (phase M z * ν (M • z)) =
            (phase M z * conj (phase M z)) * (μ (M • z) * conj (ν (M • z))) := by
          simp only [map_mul]
          ring
        _ = μ (M • z) * conj (ν (M • z)) := by rw [hcancel, one_mul]
    _ = ∫ z in F, μ z * conj (ν z) ∂(volume : Measure ℍ) :=
      (measurePreserving_deck M).setIntegral_preimage_emb hsmul
        (fun z : ℍ => μ z * conj (ν z)) F

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson
