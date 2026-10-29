/-
The actual smooth approximation used by the existence theorem comes from
Wu Xiaobin's Li-Zhong-QC-formalization, commit
1c0d5473c020b66ed5106331a38a61536760b9b2, with retained attribution.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.WirtingerWeakApproximation

/-!
# Lp smoothing sequences relative to a compact set

The defining property records actual smooth functions supported compactly in
the domain, uniform convergence on the chosen compact set, and convergence of
both actual Wirtinger derivatives in the corresponding Lp seminorm.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- An Lp smoothing sequence relative to K has smooth compact support in U,
converges uniformly to f on K, and has both actual complex derivatives converging
there in Lp to the specified weak derivatives g and h. -/
def IsLpSmoothingSequence (φ : ℕ → ℂ → ℂ) (f g h : ℂ → ℂ)
    (U K : Set ℂ) (p : ℝ≥0∞) : Prop :=
  (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n) ∧ tsupport (φ n) ⊆ U) ∧
    TendstoUniformlyOn φ f atTop K ∧
    Tendsto (fun n => eLpNorm (fun z => LiZhongQC.dz (φ n) z - g z)
      p (volume.restrict K)) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun z => LiZhongQC.dzbar (φ n) z - h z)
      p (volume.restrict K)) atTop (𝓝 0)

/-- Genuine weak locally Lp Wirtinger derivatives give an actual smoothing
sequence for each chosen compact subset, including the finite p=1 endpoint. -/
theorem exists_lpSmoothingSequence_of_distributional
    {f g h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hw : HasDistributionalWirtingerDerivatives f g h U)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hloc : ∀ C ⊆ U, IsCompact C →
      MemLp g p (volume.restrict C) ∧ MemLp h p (volume.restrict C))
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ φ : ℕ → ℂ → ℂ, IsLpSmoothingSequence φ f g h U K p :=
  exists_smooth_compact_wirtinger_approximation hU hf hw hp hp' hloc hK hKU

end LowDimensionalTopology.Geometry.Quasiconformal
