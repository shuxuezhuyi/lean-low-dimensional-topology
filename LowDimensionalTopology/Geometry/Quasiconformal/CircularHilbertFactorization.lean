module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertAnalyticSquare
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertSmoothLpExtension
public import LowDimensionalTopology.Unproved.Quasiconformal.RealDirectionalHilbert

/-!
# The factorization in the original planar Lp

The literal first transform is smooth. Its Lp membership and class come
from the given bounded extension. The same extension on that noncompact
input agrees almost everywhere with its genuine radial principal value,
which the analytic calculation identifies with the negative planar
transform. Thus both sides are equal in the original Lp space.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Every given bounded circular extension satisfies the factorization on
the original compact smooth test classes, in the same planar Lp. -/
theorem circularHilbertFactorization :
    LowDimensionalTopology.Unproved.Quasiconformal.CircularHilbertFactorization := by
  intro p hp
  let : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp)⟩
  dsimp only
  intro S hS φ hφ hc
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hp
  have hmemφ : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hφ.continuous.memLp_of_hasCompactSupport hc
  let f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) := hmemφ.toLp φ
  let g : ℂ → ℂ := circularHilbertTransform φ
  change hilbertLp hp1 f = -(S (S f))
  have hfirst : (S f : ℂ → ℂ) =ᵐ[volume] g := hS φ hφ hc
  have hmemg : MemLp g (ENNReal.ofReal p) (volume : Measure ℂ) :=
    (memLp_congr_ae hfirst).mp (Lp.memLp (S f))
  have hgclass : hmemg.toLp g = S f := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hmemg).trans hfirst.symm
  have hsecond : (S (S f) : ℂ → ℂ) =ᵐ[volume] radialCircularHilbertTransform g := by
    have hs := isCircularHilbertLpExtension_eq_radial_smoothLp hp1 hS
      (contDiff_circularHilbertTransform hφ hc) hmemg
    rwa [hgclass] at hs
  have hpoint (z : ℂ) : radialCircularHilbertTransform g z =
      -LiZhongQC.hilbertHSmooth φ z :=
    radialCircularHilbertTransform_circular_eq_neg_hilbertHSmooth hp1 hφ hc hmemg z
  have hfcoe : (f : ℂ → ℂ) =ᵐ[volume] φ := MemLp.coeFn_toLp hmemφ
  have hH : LiZhongQC.hilbertH (f : ℂ → ℂ) = LiZhongQC.hilbertH φ :=
    LiZhongQC.hilbertH_congr_ae hfcoe
  have hT₀ := hilbertLp_coeFn hp1 f
  rw [hH] at hT₀
  have hT : (hilbertLp hp1 f : ℂ → ℂ) =ᵐ[volume] LiZhongQC.hilbertHSmooth φ :=
    hT₀.trans (LiZhongQC.hilbertH_eq_ae_smooth hφ hc)
  apply Lp.ext
  filter_upwards [hT, hsecond, Lp.coeFn_neg (S (S f))] with z hTz hSz hneg
  calc
    (hilbertLp hp1 f : ℂ → ℂ) z = LiZhongQC.hilbertHSmooth φ z := hTz
    _ = -radialCircularHilbertTransform g z := by rw [hpoint z, neg_neg]
    _ = -((S (S f) : ℂ → ℂ) z) := congrArg (fun c : ℂ => -c) hSz.symm
    _ = ((-(S (S f)) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) : ℂ → ℂ) z := by
      simpa only [Pi.neg_apply] using hneg.symm

end LowDimensionalTopology.Geometry.Quasiconformal
