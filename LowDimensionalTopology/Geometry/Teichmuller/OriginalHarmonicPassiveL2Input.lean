module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicFirstSpatialParameters
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicComplexifiedKernel
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonKernelL2Input
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The actual passive weighted input in planar L²

Reflection of the same independent kernel controls the square norm of its
actual weighted input. The actual lower spatial derivative stays near one;
zero extension then gives the original planar input for the Hilbert operator.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped ComplexConjugate UpperHalfPlane ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC WeilPetersson

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

private theorem actual_passive_weighted_input_l2
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ t : ℂ, ‖t‖ < ε →
      let f := canonicalBiparameterFamily R p q 0 t
      let h := fun η : ℍ => harmonicPlane R p q η * dz f η /
        (f η - f (conj (z : ℂ))) ^ 2
      MemLp h 2 flatArea ∧ (∫ η : ℍ, ‖h η‖ ^ 2 ∂flatArea) ≤ C := by
  obtain ⟨εK, C, hεK, hC, hkernel⟩ :=
    canonicalBiparameterKernel_uniform_integrable R p hp q q {z} isCompact_singleton
  obtain ⟨εS, hεS, hC1, hreflect, _, _⟩ :=
    canonicalBiparameterFamily_spatial_c1_compact_control R p hp q
  obtain ⟨εP, hεP, _, _, hparam, _⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control R p hp q
  obtain ⟨M, hM, hμ⟩ := QuadraticBergman.uniformizedQuadratic_weightedBound R p hp q
  have hμbound (η : ℍ) : ‖harmonicPlane R p q η‖ ≤ M := by
    rw [harmonicPlane_eq_coefficient, NativeHarmonicBeltrami.norm_coefficient]
    exact hμ η η.im_pos
  let a : ℂ := conj (z : ℂ)
  have ha : a ∈ lowerHalf := by
    change (conj (z : ℂ)).im < 0
    simpa only [conj_im, UpperHalfPlane.coe_im] using neg_lt_zero.mpr z.im_pos
  let c : ℂ → ℂ := fun t => dz (canonicalBiparameterFamily R p q 0 t) a
  have hf0 : canonicalBiparameterFamily R p q 0 0 = id := by
    simpa only [map_zero] using
      (canonicalBiparameterFamily_diagonal R p q 0).trans (canonicalFamily_zero R p q)
  have hc0 : c 0 = 1 := by
    simp only [c, hf0, dz, fderiv_id, ContinuousLinearMap.id_apply]
    rw [I_mul_I]
    ring
  have hc : ContinuousAt c 0 :=
    (((hparam 0 (by simpa only [norm_zero] using hεP) a (Or.inr ha)).1).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hεP))).continuousAt
  have hnear : ∀ᶠ t : ℂ in 𝓝 0, c t ∈ ball (1 : ℂ) (1 / 2) :=
    hc.eventually_mem (by rw [hc0]; exact ball_mem_nhds _ (by norm_num))
  obtain ⟨δ, hδ, hδc⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := min εK (min εS (min εP δ))
  have hε : 0 < ε := lt_min hεK (lt_min hεS (lt_min hεP hδ))
  have heK : ε ≤ εK := min_le_left _ _
  have heS : ε ≤ εS := (min_le_right _ _).trans (min_le_left _ _)
  have heδ : ε ≤ δ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, 4 * M * C, hε, by positivity, ?_⟩
  intro t ht
  dsimp only
  let f := canonicalBiparameterFamily R p q 0 t
  let T := canonicalBiparameterFamily R p q (conj t) 0
  let h := fun η : ℍ => harmonicPlane R p q η * dz f η / (f η - f a) ^ 2
  let g : ℂ → ℂ := canonicalBiparameterKernelIntegrand R p q q (conj t) 0 z
  have htS : ‖t‖ < εS := ht.trans_le heS
  have hzS : ‖(0 : ℂ)‖ < εS := by simpa only [norm_zero] using hεS
  have hdiff (w : ℂ) (hw : w ∈ upperHalf ∪ lowerHalf) : DifferentiableAt ℝ f w :=
    (hC1 0 t hzS htS).differentiableOn_one.differentiableAt
      ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds hw)
  have hT : T = fun w : ℂ => conj (f (conj w)) := by
    simpa only [T, f, map_zero, Complex.conj_conj] using
      hreflect (conj t) 0 (by simpa only [norm_conj] using htS) hzS
  have hTz : dz T z = conj (c t) := by
    rw [hT]
    exact (abR_x_dz_dzbar_conj (hdiff a (Or.inr ha))).2.1
  have hTη (η : ℍ) : dz T (conj (η : ℂ)) = conj (dz f η) := by
    rw [hT]
    have hd : DifferentiableAt ℝ f (conj (conj (η : ℂ))) := by
      simpa only [Complex.conj_conj] using hdiff η (Or.inl η.im_pos)
    simpa only [Complex.conj_conj] using (abR_x_dz_dzbar_conj hd).2.1
  have hct : 1 / 2 ≤ ‖c t‖ := by
    have hh := hδc (mem_ball_zero_iff.mpr (ht.trans_le heδ))
    simp only [Set.mem_ofPred_eq, mem_ball, dist_eq_norm] at hh
    have htri := norm_sub_norm_le (1 : ℂ) (c t)
    rw [norm_one, norm_sub_rev] at htri
    linarith
  have hgid (η : ℍ) : ‖g η‖ =
      ‖c t‖ ^ 2 * ‖dz f η / (f η - f a) ^ 2‖ ^ 2 * ‖harmonicPlane R p q η‖ := by
    change ‖(dz T z * dz T (conj (η : ℂ)) / (T z - T (conj (η : ℂ))) ^ 2) ^ 2 *
      conj (harmonicPlane R p q η)‖ = _
    rw [hTz, hTη]
    simp only [hT, a, Complex.conj_conj, ← map_sub, norm_conj, norm_mul, norm_pow, norm_div]
    rw [norm_sub_rev (f a) (f η)]
    ring
  have hbound (η : ℍ) : ‖h η‖ ^ 2 ≤ (4 * M) * ‖g η‖ := by
    have hcq : (1 / 4 : ℝ) ≤ ‖c t‖ ^ 2 := by nlinarith
    rw [hgid]
    calc
      ‖h η‖ ^ 2 = ‖harmonicPlane R p q η‖ ^ 2 *
          ‖dz f η / (f η - f a) ^ 2‖ ^ 2 := by
        simp only [h, mul_div_assoc, norm_mul, mul_pow]
      _ ≤ (M * ‖harmonicPlane R p q η‖) * ‖dz f η / (f η - f a) ^ 2‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (by nlinarith [hμbound η, norm_nonneg (harmonicPlane R p q η)]) (sq_nonneg _)
      _ = (4 * M) * ((1 / 4) * ‖dz f η / (f η - f a) ^ 2‖ ^ 2 *
          ‖harmonicPlane R p q η‖) := by ring
      _ ≤ (4 * M) * (‖c t‖ ^ 2 * ‖dz f η / (f η - f a) ^ 2‖ ^ 2 *
          ‖harmonicPlane R p q η‖) := by gcongr
  obtain ⟨hgi, hgC⟩ := hkernel (conj t) 0
    (by simpa only [norm_conj] using ht.trans_le heK)
    (by simpa only [norm_zero] using hεK) z (mem_singleton z)
  have hgiH : Integrable (fun η : ℍ => ‖g η‖) flatArea := by
    apply (UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff (μ := flatArea)
      (g := fun η : ℂ => ‖g η‖)).mp
    rw [map_flat_coe]
    exact hgi.norm
  have hgCH : (∫ η : ℍ, ‖g η‖ ∂flatArea) ≤ C := by
    have he := UpperHalfPlane.measurableEmbedding_coe.integral_map (μ := flatArea)
      (fun η : ℂ => ‖g η‖)
    rw [map_flat_coe] at he
    exact he ▸ hgC
  have hμc : Continuous (fun η : ℍ => harmonicPlane R p q η) := by
    simpa only [harmonicPlane_eq_coefficient] using
      NativeHarmonicBeltrami.coefficient_continuous R p hp q
  have hfH : Continuous (fun η : ℍ => f η) :=
    (hC1 0 t hzS htS).continuousOn.comp_continuous UpperHalfPlane.continuous_coe
      (fun η => Or.inl η.im_pos)
  have hhm : Measurable h :=
    (hμc.measurable.fun_mul
      ((measurable_dz f).comp UpperHalfPlane.continuous_coe.measurable)).div
      ((hfH.measurable.sub measurable_const).pow_const 2)
  have hhi : Integrable (fun η : ℍ => ‖h η‖ ^ 2) flatArea :=
    (hgiH.const_mul (4 * M)).mono' (hhm.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun η => by
        simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hbound η)
  refine ⟨(memLp_two_iff_integrable_sq_norm hhm.aestronglyMeasurable).2 hhi, ?_⟩
  calc
    (∫ η : ℍ, ‖h η‖ ^ 2 ∂flatArea) ≤ ∫ η : ℍ, (4 * M) * ‖g η‖ ∂flatArea :=
      integral_mono_ae hhi (hgiH.const_mul (4 * M)) (Eventually.of_forall hbound)
    _ = (4 * M) * ∫ η : ℍ, ‖g η‖ ∂flatArea := integral_const_mul _ _
    _ ≤ 4 * M * C := mul_le_mul_of_nonneg_left hgCH (by positivity)


/-- The same passive weighted input is extended by zero off the actual upper
half-plane, giving a planar input for the existing Hilbert L² operator. -/
def canonicalPassiveWeightedKernelInput
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) (t : ℂ) : ℂ → ℂ :=
  SourceKernel.upperExtension (fun η : ℍ =>
    harmonicPlane R p q η * dz (canonicalBiparameterFamily R p q 0 t) η /
      (canonicalBiparameterFamily R p q 0 t η -
        canonicalBiparameterFamily R p q 0 t (conj (z : ℂ))) ^ 2)

/-- The actual zero-extended passive input has a uniform planar square-integral
bound near the original parameter. No ordinary first Cauchy transform is assumed. -/
theorem canonicalPassiveWeightedKernelInput_uniform_memLp_two
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ t : ℂ, ‖t‖ < ε →
      MemLp (canonicalPassiveWeightedKernelInput R p q z t) 2 (volume : Measure ℂ) ∧
        (∫ η : ℂ, ‖canonicalPassiveWeightedKernelInput R p q z t η‖ ^ 2) ≤ C := by
  obtain ⟨ε, C, hε, hC, hinput⟩ := actual_passive_weighted_input_l2 R p hp q z
  refine ⟨ε, C, hε, hC, ?_⟩
  intro t ht
  have hH := hinput t ht
  dsimp only at hH
  let H := canonicalPassiveWeightedKernelInput R p q z t
  have hext (η : ℍ) : H η = harmonicPlane R p q η *
      dz (canonicalBiparameterFamily R p q 0 t) η /
        (canonicalBiparameterFamily R p q 0 t η -
          canonicalBiparameterFamily R p q 0 t (conj (z : ℂ))) ^ 2 := by
    dsimp only [H, canonicalPassiveWeightedKernelInput, SourceKernel.upperExtension]
    rw [dite_eq_left η.coe_im_pos]
  have hlocal : MemLp H 2 (volume.restrict upperHalf) := by
    rw [← map_flat_coe]
    apply UpperHalfPlane.measurableEmbedding_coe.memLp_map_measure_iff.mpr
    change MemLp (fun η : ℍ => H η) 2 flatArea
    exact (memLp_congr_ae (Eventually.of_forall hext)).2 hH.1
  have hzero (η : ℂ) (hη : η ∉ upperHalf) : H η = 0 := by
    simp only [H, canonicalPassiveWeightedKernelInput, SourceKernel.upperExtension,
      show ¬0 < η.im from hη, dite_false]
  have hind : upperHalf.indicator H = H := by
    funext η
    by_cases hη : η ∈ upperHalf
    · exact indicator_of_mem hη H
    · simpa only [indicator_of_notMem hη] using (hzero η hη).symm
  have hglobal := (memLp_indicator_iff_restrict
    isOpen_upperHalf.measurableSet.nullMeasurableSet).2 hlocal
  refine ⟨by simpa only [hind] using hglobal, ?_⟩
  have hmap := UpperHalfPlane.measurableEmbedding_coe.integral_map (μ := flatArea)
    (fun η : ℂ => ‖H η‖ ^ 2)
  rw [map_flat_coe] at hmap
  calc
    (∫ η : ℂ, ‖H η‖ ^ 2) = ∫ η in upperHalf, ‖H η‖ ^ 2 :=
      (setIntegral_eq_integral_of_ae_compl_eq_zero (Eventually.of_forall
        (fun η hη => by rw [hzero η hη]; simp))).symm
    _ = ∫ η : ℍ, ‖H η‖ ^ 2 ∂flatArea := hmap
    _ ≤ C := by
      simpa only [hext] using hH.2

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
