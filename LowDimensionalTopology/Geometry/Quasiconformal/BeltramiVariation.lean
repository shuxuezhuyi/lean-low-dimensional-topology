module

public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableBeltrami

/-!
# The integral first variation on actual measurable Beltrami classes

The coefficient is Mathlib's L-infinity a.e. class. The normalized kernel and
its negative 1/pi factor are explicit. The actual selected normalized solution
satisfies a pointwise first-order error bound; no locally uniform remainder
estimate is asserted here.

The analytic kernel estimates and first-variation proof are due to Wu Xiaobin,
from commit 1c0d5473c020b66ed5106331a38a61536760b9b2. The fixed external
source retains the complete author, license and compatibility records.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The normalized kernel with its actual three-point factors. -/
def firstVariationKernel (w ζ : ℂ) : ℂ :=
  w * (w - 1) / (ζ * (ζ - 1) * (ζ - w))

/-- The actual integral variation of a measurable coefficient class. -/
def firstVariation (ν : MeasurableBeltramiSpace) (w : ℂ) : ℂ :=
  -(1 / (Real.pi : ℂ)) * ∫ ζ, ν ζ * firstVariationKernel w ζ

/-- The integral agrees exactly with the fixed analytic source kernel. -/
theorem firstVariation_eq_source (ν : MeasurableBeltramiSpace) (w : ℂ) :
    firstVariation ν w = LiZhongQC.ahVar ν w := rfl

/-- Any representative of the a.e. class gives the same integral. -/
theorem firstVariation_eq_of_ae (ν : MeasurableBeltramiSpace) {ρ : ℂ → ℂ}
    (hν : (ν : ℂ → ℂ) =ᵐ[volume] ρ) (w : ℂ) :
    firstVariation ν w = LiZhongQC.ahVar ρ w := by
  change -(1 / (Real.pi : ℂ)) * (∫ ζ, ν ζ * LiZhongQC.ahKer w ζ) =
    -(1 / (Real.pi : ℂ)) * (∫ ζ, ρ ζ * LiZhongQC.ahKer w ζ)
  apply congrArg (fun z : ℂ => -(1 / (Real.pi : ℂ)) * z)
  exact integral_congr_ae (hν.mono fun ζ hζ =>
    congrArg (fun a : ℂ => a * LiZhongQC.ahKer w ζ) hζ)

/-- The actual class norm bounds the integral evaluation. -/
theorem firstVariation_norm_le (ν : MeasurableBeltramiSpace) (w : ℂ) :
    ‖firstVariation ν w‖ ≤
      (1 / Real.pi) * (∫ ζ, ‖firstVariationKernel w ζ‖) * ‖ν‖ :=
  LiZhongQC.ah_var_bound w (MeasurableBeltramiSpace.isBeltramiCoeff ν)

/-- The kernel variation is complex-linear in the actual a.e. coefficient class. -/
theorem firstVariation_smul_add (ν ρ : MeasurableBeltramiSpace) (a w : ℂ) :
    firstVariation (a • ν + ρ) w = a * firstVariation ν w + firstVariation ρ w := by
  have hsum : ((a • ν + ρ : MeasurableBeltramiSpace) : ℂ → ℂ) =ᵐ[volume]
      fun ζ => a * ν ζ + ρ ζ := by
    filter_upwards [Lp.coeFn_add (a • ν) ρ, Lp.coeFn_smul a ν] with ζ hadd hsmul
    calc
      _ = (a • ν : MeasurableBeltramiSpace) ζ + ρ ζ := by
        simpa only [Pi.add_apply] using hadd
      _ = a * ν ζ + ρ ζ := by
        simpa only [Pi.smul_apply, smul_eq_mul] using
          congrArg (fun z : ℂ => z + ρ ζ) hsmul
  rw [firstVariation_eq_of_ae _ hsum w,
    firstVariation_eq_source ν w, firstVariation_eq_source ρ w]
  exact LiZhongQC.ah_var_linear (MeasurableBeltramiSpace.isBeltramiCoeff ν)
    (MeasurableBeltramiSpace.isBeltramiCoeff ρ) a w

/-- The canonical normalized solution has the pointwise first-order expansion,
with an arbitrary positive upper bound for the coefficient's actual L-infinity norm. -/
theorem normalizedSolution_pointwise_first_variation_bound (w : ℂ) :
    ∀ η > 0, ∃ δ > 0, ∀ (μ : MeasurableBeltramiBall) (ε : ℝ),
      0 < ε → ε ≤ δ → ‖μ.val‖ ≤ ε →
        ‖MeasurableBeltramiBall.normalizedSolution μ w - w - firstVariation μ.val w‖ ≤ η * ε := by
  intro η hη
  obtain ⟨δ, hδ, hF⟩ := LiZhongQC.ah_first_variation w η hη
  refine ⟨δ, hδ, ?_⟩
  intro μ ε hε hεδ hnorm
  have hμ : LiZhongQC.IsBeltramiCoeff μ.val univ ε := by
    refine ⟨(MeasurableBeltramiSpace.isBeltramiCoeff μ.val).1, ?_⟩
    filter_upwards [(MeasurableBeltramiSpace.isBeltramiCoeff μ.val).2] with ζ hζ
    exact hζ.trans hnorm
  exact hF μ.val (MeasurableBeltramiBall.normalizedSolution μ) ε hε hεδ hμ
    (MeasurableBeltramiBall.normalizedSolution_spec μ).1

end LowDimensionalTopology.Geometry.Quasiconformal
