module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyCosets
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-!
# Positive kernel tails of the actual angular coset coefficients

At each point the coefficient tail eventually vanishes and stays bounded by
the original angular bound. Dominated convergence at a fixed kernel anchor,
the actual kernel's L1 continuity and a finite compact cover then give uniform
convergence of these positive kernel integrals on every compact set.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- Genuine positive kernel tails tend uniformly to zero on each compact set;
the geometric one-support input remains explicit in this intermediate producer. -/
theorem rightCoset_kernelTail_tendstoUniformlyOn
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) [Countable Γ]
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v) :
    let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
    let a : Finset C → ℂ → ℝ := fun F ζ => by
      classical
      exact ∑' u : C, if u ∈ F then 0 else ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ‖
    let E : Finset C → ℂ → ℝ := fun F z =>
      ∫ ζ : ℂ, a F ζ * ‖Quasiconformal.firstVariationKernel z ζ‖
    (∀ (F : Finset C) (z : ℂ),
      Integrable (fun ζ : ℂ => a F ζ * ‖Quasiconformal.firstVariationKernel z ζ‖)
        (volume : Measure ℂ)) ∧
      ∀ K : Set ℂ, IsCompact K →
        TendstoUniformlyOn E (fun _ => 0) (atTop : Filter (Finset C)) K := by
  classical
  let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
  let a : Finset C → ℂ → ℝ := fun F ζ =>
    ∑' u : C, if u ∈ F then 0 else ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ‖
  let ker := Quasiconformal.firstVariationKernel
  let E : Finset C → ℂ → ℝ := fun F z => ∫ ζ : ℂ, a F ζ * ‖ker z ζ‖
  let B : ℝ := 1 / (4 * (θ : ℝ))
  have hB : 0 < B := one_div_pos.mpr (mul_pos (by norm_num) θ.property.1)
  have hm (F : Finset C) : Measurable (a F) := by
    apply Measurable.tsum
    intro u
    by_cases hu : u ∈ F
    · simpa only [ite_eq_left hu] using (measurable_const : Measurable (fun _ : ℂ => (0 : ℝ)))
    · simpa only [ite_eq_right hu] using
        (measurable_rightCosetInfinitesimalZeroExtension θ Γ s u).norm
  have hvalue (F : Finset C) (ζ : ℂ) (u : C)
      (hu : rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0) :
      a F ζ = if u ∈ F then 0 else ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ‖ := by
    apply tsum_eq_single u
    intro v hv
    have he : rightCosetInfinitesimalZeroExtension θ Γ s v ζ = 0 := by
      by_contra hnv
      exact hv (hsep ζ v u hnv hu)
    simp only [he, norm_zero, ite_self]
  have hzero (F : Finset C) (ζ : ℂ)
      (hz : ∀ u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ = 0) : a F ζ = 0 := by
    simp only [a, hz, norm_zero, ite_self, tsum_zero]
  have hb (F : Finset C) (ζ : ℂ) : 0 ≤ a F ζ ∧ a F ζ ≤ B := by
    by_cases h : ∃ u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0
    · obtain ⟨u, hu⟩ := h
      rw [hvalue F ζ u hu]
      split_ifs
      · exact ⟨le_rfl, hB.le⟩
      · exact ⟨norm_nonneg _, norm_rightCosetInfinitesimalZeroExtension_le θ Γ s u ζ⟩
    · have hz : ∀ u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ = 0 := by
        intro u
        exact not_ne_iff.mp (fun hu => h ⟨u, hu⟩)
      rw [hzero F ζ hz]
      exact ⟨le_rfl, hB.le⟩
  have hnorm (F : Finset C) (ζ : ℂ) : ‖a F ζ‖ ≤ B := by
    rw [Real.norm_of_nonneg (hb F ζ).1]
    exact (hb F ζ).2
  have hpoint (ζ : ℂ) : Tendsto (fun F : Finset C => a F ζ) atTop (𝓝 0) := by
    have he : ∀ᶠ F : Finset C in atTop, a F ζ = 0 := by
      by_cases h : ∃ u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0
      · obtain ⟨u, hu⟩ := h
        filter_upwards [eventually_ge_atTop ({u} : Finset C)] with F hF
        rw [hvalue F ζ u hu, ite_eq_left (hF (Finset.mem_singleton_self u))]
      · have hz : ∀ u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ = 0 := by
          intro u
          exact not_ne_iff.mp (fun hu => h ⟨u, hu⟩)
        exact Eventually.of_forall (fun F => hzero F ζ hz)
    exact (tendsto_const_nhds : Tendsto (fun _ : Finset C => (0 : ℝ)) atTop (𝓝 0)).congr' (EventuallyEq.symm he)
  have hker (z : ℂ) : Integrable (ker z) (volume : Measure ℂ) :=
    LiZhongQC.ah_ker_integrable z
  have hL (F : Finset C) (z : ℂ) :
      Integrable (fun ζ : ℂ => a F ζ * ‖ker z ζ‖) (volume : Measure ℂ) :=
    (hker z).norm.bdd_mul (hm F).aestronglyMeasurable (Eventually.of_forall (hnorm F))
  have hfixed (z : ℂ) : Tendsto (fun F : Finset C => E F z) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure ℂ)) (f := fun _ : ℂ => (0 : ℝ))
      (fun ζ : ℂ => B * ‖ker z ζ‖)
      (Eventually.of_forall (fun F : Finset C => (hL F z).aestronglyMeasurable))
      (Eventually.of_forall (fun F : Finset C => Eventually.of_forall (fun ζ : ℂ => by
        rw [Real.norm_of_nonneg (mul_nonneg (hb F ζ).1 (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_right (hb F ζ).2 (norm_nonneg _))))
      ((hker z).norm.const_mul B)
      (Eventually.of_forall (fun ζ : ℂ => by
        simpa only [zero_mul] using (hpoint ζ).mul_const ‖ker z ζ‖))
    simpa only [E, integral_zero] using h
  have hmod (F : Finset C) (z w : ℂ) :
      E F z ≤ E F w + B * ∫ ζ : ℂ, ‖ker z ζ - ker w ζ‖ := by
    have hd : Integrable (fun ζ : ℂ => ‖ker z ζ - ker w ζ‖) (volume : Measure ℂ) :=
      ((hker z).sub (hker w)).norm
    have hp (ζ : ℂ) : a F ζ * ‖ker z ζ‖ ≤
        a F ζ * ‖ker w ζ‖ + B * ‖ker z ζ - ker w ζ‖ := by
      have ht : ‖ker z ζ‖ ≤ ‖ker w ζ‖ + ‖ker z ζ - ker w ζ‖ := by
        linarith [norm_sub_norm_le (ker z ζ) (ker w ζ)]
      calc
        _ ≤ a F ζ * (‖ker w ζ‖ + ‖ker z ζ - ker w ζ‖) :=
          mul_le_mul_of_nonneg_left ht (hb F ζ).1
        _ = a F ζ * ‖ker w ζ‖ + a F ζ * ‖ker z ζ - ker w ζ‖ := mul_add _ _ _
        _ ≤ _ := add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (hb F ζ).2 (norm_nonneg (ker z ζ - ker w ζ)))
    calc
      _ ≤ ∫ ζ : ℂ, a F ζ * ‖ker w ζ‖ + B * ‖ker z ζ - ker w ζ‖ :=
        integral_mono (hL F z) ((hL F w).add (hd.const_mul B)) hp
      _ = _ := by rw [integral_add (hL F w) (hd.const_mul B), integral_const_mul]
  refine ⟨hL, ?_⟩
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hη : 0 < ε / (2 * B) := div_pos hε (mul_pos (by norm_num) hB)
  choose δ hδ hδL using fun w : K =>
    LiZhongQC.ah_ker_continuous (w : ℂ) (ε / (2 * B)) hη
  have hcover : K ⊆ ⋃ w : K, Metric.ball (w : ℂ) (δ w) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, by simpa only [Metric.mem_ball, dist_self] using hδ ⟨z, hz⟩⟩
  obtain ⟨D, hD⟩ := hK.elim_finite_subcover (fun w : K => Metric.ball (w : ℂ) (δ w))
    (fun _ => Metric.isOpen_ball) hcover
  choose Fw hFw using fun w : K => eventually_atTop.mp
    ((tendsto_order.mp (hfixed (w : ℂ))).2 (ε / 2) (half_pos hε))
  let F₀ : Finset C := D.biUnion Fw
  have hhalf : B * (ε / (2 * B)) = ε / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    calc
      (B * (ε / (2 * B))) * 2 = (ε / (2 * B)) * (2 * B) := by ring
      _ = ε := div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) hB))
  filter_upwards [eventually_ge_atTop F₀] with F hF z hz
  obtain ⟨w, hwD, hzw⟩ := mem_iUnion₂.mp (hD hz)
  have hsub : Fw w ≤ F := by
    intro u hu
    exact hF (Finset.mem_biUnion.mpr ⟨w, hwD, hu⟩)
  have hnear : ∫ ζ : ℂ, ‖ker z ζ - ker (w : ℂ) ζ‖ < ε / (2 * B) :=
    hδL w z (by simpa only [Metric.mem_ball, dist_eq_norm] using hzw)
  have hsmall : E F z < ε := by
    calc
      _ ≤ E F (w : ℂ) + B * ∫ ζ : ℂ, ‖ker z ζ - ker (w : ℂ) ζ‖ := hmod F z w
      _ < ε / 2 + B * (ε / (2 * B)) :=
        add_lt_add (hFw w F hsub) (mul_lt_mul_of_pos_left hnear hB)
      _ = ε := by rw [hhalf, add_halves]
  have hnonneg : 0 ≤ E F z :=
    integral_nonneg (fun ζ => mul_nonneg (hb F ζ).1 (norm_nonneg _))
  simp only [Real.dist_eq, zero_sub, abs_neg]
  change |E F z| < ε
  rw [abs_of_nonneg hnonneg]
  exact hsmall

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
