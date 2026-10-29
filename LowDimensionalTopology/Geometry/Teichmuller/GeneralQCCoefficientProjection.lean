/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCCoefficientRealization
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCCoefficientDistance
public import LowDimensionalTopology.Geometry.Teichmuller.CoefficientDifferenceEstimate
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBersInverse
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCDistanceTopology

/-!
# The actual coefficient projection to general marked classes

Every element of the full compatible L-infinity unit ball is realized by an
actual native target and an actual QC marking of the original reference.
The realized raw coefficient agrees almost everywhere with its original
planar representative. The original full-log class distance is continuous
under norm convergence of these coefficients, without compactness or genus.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u

variable (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
  {p : ℍ → R.carrier} (hp : IsUniformization Γ p)

/-- An actual general marking realizing the given compatible Banach coefficient. -/
def coefficientMarking (μ : GammaMeasurableBeltrami.Ball Γ) : Marked.{u, u} R :=
  Classical.choose (exists_marked_of_compatible_coefficient R hp
    (norm_nonneg μ.val.val) (GammaMeasurableBeltrami.Ball.norm_lt_one μ)
    (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val.val)
    (GammaMeasurableBeltrami.planeRepresentative_isGammaCompatible μ.val))

/-- Realization preserves the original raw lifted coefficient almost everywhere
and gives the genuine uniform QC upper bound of the realized marking. -/
theorem coefficientMarking_spec (μ : GammaMeasurableBeltrami.Ball Γ) :
    IsKQCRS (coefficientMarking R hp μ).marking
        ((1 + ‖μ.val‖) / (1 - ‖μ.val‖)) ∧
      s27u_liftCoeff p (coefficientMarking R hp μ).marking
        =ᵐ[volume.restrict upperHalf]
          GammaMeasurableBeltrami.planeRepresentative μ.val.val := by
  obtain ⟨F, -, -, -, -, -, hK, hμ⟩ :=
    Classical.choose_spec (exists_marked_of_compatible_coefficient R hp
      (norm_nonneg μ.val.val) (GammaMeasurableBeltrami.Ball.norm_lt_one μ)
      (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val.val)
      (GammaMeasurableBeltrami.planeRepresentative_isGammaCompatible μ.val))
  exact ⟨hK, hμ⟩

/-- The projection lands in the original general QC-marked quotient. -/
def coefficientProjection (μ : GammaMeasurableBeltrami.Ball Γ) : Space.{u, u} R :=
  mk (coefficientMarking R hp μ)

/-- The original transition distortion is controlled by the genuine Banach
coefficient difference on each fixed subunit norm ball. -/
theorem coefficientMarking_delta_le
    (μ ν : GammaMeasurableBeltrami.Ball Γ) {k : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : ‖μ.val‖ ≤ k) (hν : ‖ν.val‖ ≤ k) :
    UniversalTeichmuller.dilatationDiffNorm
        (s27u_liftCoeff p (coefficientMarking R hp μ).marking)
        (s27u_liftCoeff p (coefficientMarking R hp ν).marking) ≤
      ‖μ.val - ν.val‖ / (1 - k ^ 2) := by
  rw [bersInverse_dilatationDiffNorm_congr_ae
    (coefficientMarking_spec R hp μ).2 (coefficientMarking_spec R hp ν).2]
  exact GammaMeasurableBeltrami.dilatationDiffNorm_planeRepresentative_le
    μ.val.val ν.val.val hk₀ hk hμ hν

/-- Actual norm-convergent coefficients project to convergent original marked
classes for the same original full-log distance and distance-ball topology. -/
theorem coefficientProjection_tendsto
    {ι : Type*} {l : Filter ι} {μ : ι → GammaMeasurableBeltrami.Ball Γ}
    {ν : GammaMeasurableBeltrami.Ball Γ} (hμ : Tendsto μ l (𝓝 ν)) :
    letI := distanceTopology.{u, u} R
    Tendsto (fun i => coefficientProjection R hp (μ i)) l
      (𝓝 (coefficientProjection R hp ν)) := by
  let := pseudoMetricSpace.{u, u} R
  have hval : Tendsto (fun i => (μ i).val) l (𝓝 ν.val) :=
    (continuous_subtype_val.tendsto ν).comp hμ
  let k : ℝ := (‖ν.val‖ + 1) / 2
  have hkν : ‖ν.val‖ < k := by
    dsimp only [k]
    linarith [GammaMeasurableBeltrami.Ball.norm_lt_one ν]
  have hk₀ : 0 ≤ k := by dsimp only [k]; positivity
  have hk : k < 1 := by
    dsimp only [k]
    linarith [GammaMeasurableBeltrami.Ball.norm_lt_one ν]
  have hb : ∀ᶠ i in l, ‖(μ i).val‖ ≤ k :=
    (hval.norm.eventually (gt_mem_nhds hkν)).mono fun _ h => h.le
  let δ : ι → ℝ := fun i => UniversalTeichmuller.dilatationDiffNorm
    (s27u_liftCoeff p (coefficientMarking R hp (μ i)).marking)
    (s27u_liftCoeff p (coefficientMarking R hp ν).marking)
  have hnorm : Tendsto (fun i => ‖(μ i).val - ν.val‖) l (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using (hval.sub_const ν.val).norm
  have hδ : Tendsto δ l (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      (hb.mono fun i hi => coefficientMarking_delta_le R hp (μ i) ν hk₀ hk hi hkν.le)
      (by simpa only [zero_div] using hnorm.div_const (1 - k ^ 2))
  have hratio : Tendsto (fun i => (1 + δ i) / (1 - δ i)) l (𝓝 (1 : ℝ)) := by
    have h1 : Tendsto (fun _ : ι => (1 : ℝ)) l (𝓝 (1 : ℝ)) := tendsto_const_nhds
    have hq : Tendsto ((fun i => 1 + δ i) / (fun i => 1 - δ i)) l (𝓝 (1 : ℝ)) := by
      simpa only [add_zero, sub_zero, div_self (one_ne_zero : (1 : ℝ) ≠ 0)] using
        (h1.add hδ).div (h1.sub hδ) (by norm_num)
    exact hq.congr (fun _ => rfl)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun i => distance_nonneg _ _)
    (fun i => distance_mk_le_fractional_log R hp
      (coefficientMarking R hp (μ i)) (coefficientMarking R hp ν))
  simpa only [Real.log_one] using hratio.log (one_ne_zero : (1 : ℝ) ≠ 0)

/-- The actual realization projection is continuous on the entire compatible
unit ball, with the original general distance-ball topology on its target. -/
theorem coefficientProjection_continuous :
    letI := distanceTopology.{u, u} R
    Continuous (coefficientProjection R hp) := by
  let := distanceTopology.{u, u} R
  exact continuous_iff_continuousAt.mpr fun μ => coefficientProjection_tendsto R hp
    (μ := id) (ν := μ) tendsto_id

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
