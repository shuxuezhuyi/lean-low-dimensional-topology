module

public import LowDimensionalTopology.Geometry.Teichmuller.LiteralKobayashiExtendedCore
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannManifold
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Local holomorphic disks in an original manifold chart

A ball in the actual target of a chart supplies disks joining its center
to nearby original manifold points. Their full Poincare costs tend to
zero along the diagonal. The disk carrier, its finite chart, and the
one-disk infimum are the existing ones.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Manifold ContDiff Complex.UnitDisc ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore

open Surfaces Hyperbolic

universe u

local notation "Δ" => extendedUnitDisc

private theorem discFiniteChart_contMDiff :
    let := discRiemannSurface.toRiemannAtlas.toChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω discFiniteChart := by
  let := discRiemannSurface.toRiemannAtlas.toChartedSpace
  change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω discFiniteChart
  let : IsManifold 𝓘(ℂ) ω Δ := discRiemannSurface.toRiemannAtlas.isManifold
  have hmem : discFiniteChart ∈ atlas ℂ Δ := by
    change discFiniteChart ∈ discRiemannSurface.charts
    exact discFiniteChart_mem
  intro z
  have hz : z ∈ discFiniteChart.source := by
    rw [discFiniteChart_source]
    exact Set.mem_univ z
  exact contMDiffAt_of_mem_maximalAtlas
    (I := 𝓘(ℂ)) (n := ω) (IsManifold.subset_maximalAtlas hmem) hz

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]

/-- Actual disks in the original chart join its center to each sufficiently close point,
with the full logarithmic Poincare bound. -/
theorem exists_chart_holomorphic_disk (p : M) :
    let := discRiemannSurface.toRiemannAtlas.toChartedSpace
    let c := chartAt (Fin d → ℂ) p
    ∃ r : ℝ, 0 < r ∧ ball (c p) r ⊆ c.target ∧
      ∀ q ∈ c.source, ‖c q - c p‖ < r →
        ∃ (f : Δ → M) (b : Δ),
          ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin d → ℂ) ω f ∧
          f (discFiniteHomeomorph.symm (0 : 𝔻)) = p ∧ f b = q ∧
          (∀ z, f z ∈ c.source) ∧
          (discFiniteHomeomorph b : ℂ) = ((‖c q - c p‖ / r : ℝ) : ℂ) ∧
          oneDiskEDist (d := d) p q ≤
            ENNReal.ofReal (Real.log
              ((1 + ‖c q - c p‖ / r) / (1 - ‖c q - c p‖ / r))) := by
  let := discRiemannSurface.toRiemannAtlas.toChartedSpace
  let c := chartAt (Fin d → ℂ) p
  have hp : p ∈ c.source := mem_chart_source (Fin d → ℂ) p
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (c.open_target.mem_nhds (c.map_source hp))
  refine ⟨r, hr, hball, ?_⟩
  intro q hq hqnorm
  let v : Fin d → ℂ := c q - c p
  let s : ℝ := ‖v‖ / r
  let w : Fin d → ℂ := ((r / ‖v‖ : ℝ) : ℂ) • v
  have hs0 : 0 ≤ s := div_nonneg (norm_nonneg v) hr.le
  have hs1 : s < 1 := (div_lt_one hr).mpr hqnorm
  have hsnorm : ‖(s : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact hs1
  let bU : 𝔻 := ⟨(s : ℂ), by
    simpa only [Subsemigroup.mem_unitBall] using! hsnorm⟩
  let a₀ : Δ := discFiniteHomeomorph.symm (0 : 𝔻)
  let b : Δ := discFiniteHomeomorph.symm bU
  have ha : discFiniteChart a₀ = 0 := by
    change (discFiniteHomeomorph a₀ : ℂ) = 0
    exact congrArg (fun z : 𝔻 => (z : ℂ)) (discFiniteHomeomorph.apply_symm_apply 0)
  have hb : (discFiniteHomeomorph b : ℂ) = (s : ℂ) :=
    congrArg (fun z : 𝔻 => (z : ℂ)) (discFiniteHomeomorph.apply_symm_apply bU)
  have hbchart : discFiniteChart b = (s : ℂ) := hb
  have hw : ‖w‖ ≤ r := by
    by_cases hv : v = 0
    · simp only [w, hv, norm_zero, div_zero, Complex.ofReal_zero, zero_smul]
      exact hr.le
    · have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hwEq : ‖w‖ = r := by
        change ‖((r / ‖v‖ : ℝ) : ℂ) • v‖ = r
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (div_pos hr (norm_pos_iff.mpr hv)), div_mul_cancel₀ r hvnorm]
      exact hwEq.le
  have hsw : (s : ℂ) • w = v := by
    by_cases hv : v = 0
    · simp only [w, hv, smul_zero]
    · have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hcancel : (‖v‖ / r) * (r / ‖v‖) = 1 := by
        rw [div_mul_div_comm, mul_comm ‖v‖ r,
          div_self (mul_ne_zero (ne_of_gt hr) hvnorm)]
      change ((‖v‖ / r : ℝ) : ℂ) • (((r / ‖v‖ : ℝ) : ℂ) • v) = v
      rw [smul_smul, ← Complex.ofReal_mul, hcancel, Complex.ofReal_one, one_smul]
  have hmap (z : Δ) : c p + discFiniteChart z • w ∈ c.target := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have hz : ‖discFiniteChart z‖ < 1 :=
      mem_ball_zero_iff.mp (discFiniteHomeomorph z).property
    exact (mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans_lt
      (by simpa only [one_mul] using mul_lt_mul_of_pos_right hz hr)
  let f : Δ → M := fun z => c.symm (c p + discFiniteChart z • w)
  have haff : ContDiff ℂ ω (fun z : ℂ => c p + z • w) :=
    contDiff_const.add (contDiff_id.smul_const w)
  have hinner : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      (fun z : Δ => c p + discFiniteChart z • w) :=
    haff.comp_contMDiff discFiniteChart_contMDiff
  have hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin d → ℂ) ω f := by
    apply contMDiffOn_univ.mp
    exact (contMDiffOn_chart_symm (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) (x := p)).comp
      hinner.contMDiffOn (fun z _ => hmap z)
  have hfa : f a₀ = p := by
    change c.symm (c p + discFiniteChart a₀ • w) = p
    rw [ha, zero_smul, add_zero, c.left_inv hp]
  have hfb : f b = q := by
    change c.symm (c p + discFiniteChart b • w) = q
    rw [hbchart, hsw]
    change c.symm (c p + (c q - c p)) = q
    rw [add_comm (c p) (c q - c p), sub_add_cancel, c.left_inv hq]
  refine ⟨f, b, hf, hfa, hfb, (fun z => c.map_target (hmap z)), hb, ?_⟩
  have hbound := oneDiskEDist_le (d := d) (f := f) hf a₀ b
  rw [hfa, hfb] at hbound
  have hstart : (discFiniteHomeomorph a₀ : 𝔻) = 0 := by
    apply Complex.UnitDisc.coe_injective
    exact ha
  have hend : (discFiniteHomeomorph b : 𝔻) = bU := by
    apply Complex.UnitDisc.coe_injective
    exact hb
  have hcost : discPathEDist 0 bU =
      ENNReal.ofReal (Real.log ((1 + s) / (1 - s))) := by
    have hfinite : discPathEDist 0 bU ≠ ⊤ := by
      rw [discPathEDist_eq_halfPlane, piecewisePathEDist_eq_metric]
      exact ENNReal.ofReal_ne_top
    have hreal : discPathEDist 0 bU = ENNReal.ofReal (discPathDist 0 bU) :=
      (ENNReal.ofReal_toReal hfinite).symm
    have hnormb : ‖(bU : ℂ)‖ = s := by
      change ‖(s : ℂ)‖ = s
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    rw [hreal, disc_radial_distance, hnormb]
  exact hbound.trans_eq ((congrArg₂ discPathEDist hstart hend).trans hcost)

/-- The existing one-disk infimum tends to zero as the second original point approaches the first. -/
theorem oneDiskEDist_tendsto_right (p : M) :
    Tendsto (fun q : M => oneDiskEDist (d := d) p q) (𝓝 p) (𝓝 0) := by
  obtain ⟨r, hr, _hball, hdisks⟩ := exists_chart_holomorphic_disk (d := d) p
  let c := chartAt (Fin d → ℂ) p
  have hp : p ∈ c.source := mem_chart_source (Fin d → ℂ) p
  have hc : ContinuousAt c p := c.continuousAt hp
  let s : M → ℝ := fun q => ‖c q - c p‖ / r
  have hs : ContinuousAt s p := ((hc.sub continuousAt_const).norm).div_const r
  have hs0 : s p = 0 := by simp only [s, sub_self, norm_zero, zero_div]
  have hden : 1 - s p ≠ 0 := by rw [hs0, sub_zero]; exact one_ne_zero
  have hquot : ContinuousAt (fun q => (1 + s q) / (1 - s q)) p :=
    (continuousAt_const.add hs).div (continuousAt_const.sub hs) hden
  have hquot0 : (1 + s p) / (1 - s p) = 1 := by rw [hs0]; simp only [add_zero, sub_zero, div_one]
  have hlog := hquot.log (by rw [hquot0]; exact one_ne_zero)
  have hlimit : Tendsto
      (fun q => ENNReal.ofReal (Real.log ((1 + s q) / (1 - s q)))) (𝓝 p) (𝓝 0) := by
    simpa only [hs0, add_zero, sub_zero, div_one, Real.log_one, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal hlog.tendsto
  have hsource : ∀ᶠ q in 𝓝 p, q ∈ c.source := c.open_source.mem_nhds hp
  have hcoordBall : ∀ᶠ q in 𝓝 p, c q ∈ ball (c p) r :=
    hc.eventually (Metric.ball_mem_nhds (c p) hr)
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ c.source ∧ c q ∈ ball (c p) r :=
    hsource.and hcoordBall
  have hupper : ∀ᶠ q in 𝓝 p, oneDiskEDist (d := d) p q ≤
      ENNReal.ofReal (Real.log ((1 + s q) / (1 - s q))) := by
    apply hnear.mono
    intro q hq
    have hqnorm : ‖c q - c p‖ < r := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hq.2
    obtain ⟨_f, _b, _hf, _hfp, _hfq, _hsource, _hb, hbound⟩ := hdisks q hq.1 hqnorm
    exact hbound
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun q : M => oneDiskEDist (d := d) p q)
    (g := fun _ : M => (0 : ℝ≥0∞))
    (h := fun q => ENNReal.ofReal (Real.log ((1 + s q) / (1 - s q))))
    tendsto_const_nhds hlimit (Eventually.of_forall (fun _ => bot_le)) hupper

end LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore
