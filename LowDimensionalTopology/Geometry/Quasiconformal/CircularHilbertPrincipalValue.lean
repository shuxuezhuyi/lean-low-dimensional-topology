module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertRadialFormula
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Agreement of the radial and directional circular principal values

The absolutely integrable opposite-ray kernel dominates the radial
truncations. Dominated convergence gives the original directional average,
with its exact positive normalization and genuine radial principal value.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The radial truncations converge to the actual directional circular
average for every original smooth compact planar test. -/
theorem hasCircularHilbertPrincipalValue {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) (ζ : ℂ) :
    HasCircularHilbertPrincipalValue φ ζ := by
  let g : ℝ × ℝ → ℂ := circularPairedKernel φ ζ
  let s : Set (ℝ × ℝ) := Ioc (0 : ℝ) Real.pi ×ˢ Ioi (0 : ℝ)
  let t : ℝ → Set (ℝ × ℝ) := fun ε => {v | ε < v.2}
  let F : ℝ → (ℝ × ℝ) → ℂ := fun ε => (t ε).indicator g
  have hs : MeasurableSet s := measurableSet_Ioc.prod measurableSet_Ioi
  have ht (ε : ℝ) : MeasurableSet (t ε) :=
    (isOpen_lt continuous_const continuous_snd).measurableSet
  have hg : IntegrableOn g s (volume : Measure (ℝ × ℝ)) :=
    integrableOn_circularPairedKernel hφ hc ζ
  have hFm : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (F ε) (volume.restrict s) :=
    Eventually.of_forall fun ε => hg.aestronglyMeasurable.indicator (ht ε)
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ᵐ v ∂(volume.restrict s), ‖F ε v‖ ≤ ‖g v‖ := by
    apply Eventually.of_forall
    intro ε
    apply Eventually.of_forall
    intro v
    by_cases hv : v ∈ t ε
    · simp only [F, Set.indicator_of_mem hv, le_refl]
    · simp only [F, Set.indicator_of_notMem hv, norm_zero]
      exact norm_nonneg _
  have hlim : ∀ᵐ v ∂(volume.restrict s),
      Tendsto (fun ε : ℝ => F ε v) (𝓝[>] 0) (𝓝 (g v)) := by
    filter_upwards [self_mem_ae_restrict hs] with v hv
    have hvr : 0 < v.2 := hv.2
    have hevent : (fun ε : ℝ => F ε v) =ᶠ[𝓝[>] 0] fun _ => g v := by
      filter_upwards [(eventually_lt_nhds hvr).filter_mono nhdsWithin_le_nhds] with ε hε
      change (t ε).indicator g v = g v
      exact Set.indicator_of_mem (show v ∈ t ε from hε) g
    exact tendsto_const_nhds.congr' hevent.symm
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict s) (F := F) (f := g) (fun v => ‖g v‖)
      hFm hbound hg.norm hlim
  have hset (δ : ℝ) (hδ : 0 ≤ δ) :
      s ∩ t δ = Ioc (0 : ℝ) Real.pi ×ˢ Ioi δ := by
    ext v
    constructor
    · intro h
      exact ⟨h.1.1, h.2⟩
    · rintro ⟨hθ, hr⟩
      exact ⟨⟨hθ, lt_of_le_of_lt hδ hr⟩, hr⟩
  have hiter (δ : ℝ) (hδ : 0 ≤ δ) :
      (∫ v in s, F δ v) =
        ∫ θ in (0 : ℝ)..Real.pi, ∫ r in Ioi δ, g (θ, r) := by
    have hint : IntegrableOn g (Ioc (0 : ℝ) Real.pi ×ˢ Ioi δ)
        (volume : Measure (ℝ × ℝ)) :=
      hg.mono_set (Set.prod_mono (Subset.refl _) (Ioi_subset_Ioi hδ))
    have hint' : IntegrableOn g (Ioc (0 : ℝ) Real.pi ×ˢ Ioi δ)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      simpa only [← Measure.volume_eq_prod] using hint
    change (∫ v in s, (t δ).indicator g v) = _
    rw [setIntegral_indicator (ht δ), hset δ hδ,
      Measure.volume_eq_prod ℝ ℝ, setIntegral_prod g hint',
      ← intervalIntegral.integral_of_le Real.pi_pos.le]
  have hzero : (∫ v in s, F 0 v) = ∫ v in s, g v := by
    apply setIntegral_congr_fun hs
    intro v hv
    exact Set.indicator_of_mem (show v ∈ t 0 from hv.2) g
  have htarget : (1 / (2 * (Real.pi : ℂ))) * (∫ v in s, g v) =
      circularHilbertTransform φ ζ := by
    rw [← hzero, hiter 0 le_rfl]
    exact (circularHilbertTransform_eq_paired_integral hφ hc ζ).symm
  have htrunc (ε : ℝ) (hε : 0 < ε) :
      (1 / (2 * (Real.pi : ℂ))) * (∫ v in s, F ε v) =
        circularHilbertTruncation φ ζ ε := by
    rw [hiter ε hε.le]
    exact (circularHilbertTruncation_eq_paired_integral hφ hc ζ hε).symm
  have hscaled := hconv.const_mul (1 / (2 * (Real.pi : ℂ)))
  rw [htarget] at hscaled
  change Tendsto (circularHilbertTruncation φ ζ) (𝓝[>] (0 : ℝ))
    (𝓝 (circularHilbertTransform φ ζ))
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact htrunc ε hε

/-- The complete original radial principal-value obligation holds for the
literal directional average on all smooth compact planar tests. -/
theorem circularHilbertPrincipalValue :
    LowDimensionalTopology.Unproved.Quasiconformal.CircularHilbertPrincipalValue := by
  intro φ hφ hc ζ
  exact hasCircularHilbertPrincipalValue hφ hc ζ

end LowDimensionalTopology.Geometry.Quasiconformal
