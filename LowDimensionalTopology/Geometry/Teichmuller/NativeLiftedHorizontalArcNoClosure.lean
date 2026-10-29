/-
Portions of the positive-integral argument are adapted from Wu Xiaobin's
Li-Zhong-QC-formalization (Copyright 2026), released under Apache-2.0.
See THIRD_PARTY_NOTICES.md for the pinned source and retained license.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeLiftedHorizontalArcShortest
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# A lifted horizontal arc cannot close

The original differential and its actual lift are retained. The open arc is
regular with nonzero velocity, while either endpoint may be a zero. Its length
is the original nonnegative extended integral; no finiteness premise is needed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- A nondegenerate horizontal arc of the actual lifted differential has
different endpoint values, even when its endpoints are zeros. -/
theorem nativeLiftedHorizontalArc_endpoints_ne
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (p : UpperHalfPlane → X) (_hp : IsUniformization Γ p)
      (c : ℝ → ℂ) (a b : ℝ), a < b →
      IsHorizontalArc (utm_liftQD (q : X → ℂ → ℂ) p) c a b →
      ContinuousOn c (Icc a b) → c '' Icc a b ⊆ upperHalf →
      c a ≠ c b := by
  let := R.t2Space
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro Γ p hp c a b hab hc hcc hcH heq
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let β : LRCurve := ⟨fun _ => c a,
    (LipschitzWith.const (α := ℝ) (c a)).locallyLipschitz.locallyLipschitzOn⟩
  have hβH : β.trace ⊆ upperHalf := by
    rintro _ ⟨t, _, rfl⟩
    exact hcH ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
  have hβa : Tendsto β.toFun (nhdsWithin 0 (Ioi 0)) (𝓝 (c a)) :=
    tendsto_const_nhds
  have hβb : Tendsto β.toFun (nhdsWithin 1 (Iio 1)) (𝓝 (c b)) := by
    rw [← heq]
    exact tendsto_const_nhds
  have hle := nativeLiftedHorizontalArc_shortest R q hq Γ p hp c a b
    hab hc hcc hcH β hβH hβa hβb
  have hzero : (∫⁻ t in Ioo a b, phiDensity ψ (c t) * ‖deriv c t‖ₑ) = 0 := by
    apply le_antisymm ?_ zero_le
    simpa only [phiLength, LRCurve.rhoLength, β, deriv_const, enorm_zero,
      mul_zero, lintegral_zero] using hle
  have hψ : ContinuousOn ψ upperHalf :=
    (utm_liftQD_differentiableOn q.property hp).continuousOn
  have hρ : ContinuousOn (fun t => phiDensity ψ (c t)) (Ioo a b) := by
    have hcomp : ContinuousOn (fun t => ψ (c t)) (Ioo a b) :=
      hψ.comp (hcc.mono Ioo_subset_Icc_self)
        fun t ht => hcH ⟨t, Ioo_subset_Icc_self ht, rfl⟩
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_sqrt.comp_continuousOn hcomp.norm)
  have hmeas : AEMeasurable (fun t => phiDensity ψ (c t) * ‖deriv c t‖ₑ)
      (volume.restrict (Ioo a b)) :=
    (hρ.aemeasurable measurableSet_Ioo).mul (measurable_deriv c).enorm.aemeasurable
  have hpos : ∀ t ∈ Ioo a b, 0 < phiDensity ψ (c t) * ‖deriv c t‖ₑ := by
    intro t ht
    obtain ⟨_, hd0, hq0, _, _⟩ := hc t ht
    refine ENNReal.mul_pos ?_ ?_
    · exact (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 (norm_pos_iff.2 hq0))).ne'
    · exact (enorm_pos.2 hd0).ne'
  have hae : ∀ᵐ t ∂volume, t ∈ Ioo a b → phiDensity ψ (c t) * ‖deriv c t‖ₑ = 0 :=
    (ae_restrict_iff' measurableSet_Ioo).1 ((lintegral_eq_zero_iff' hmeas).1 hzero)
  have hnull : volume (Ioo a b) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with t ht htab
    exact (hpos t htab).ne' (ht htab)
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hnull
  linarith

end LowDimensionalTopology.Geometry.Teichmuller
