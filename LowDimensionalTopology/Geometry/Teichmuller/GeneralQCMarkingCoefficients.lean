/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCCoefficientProjection
public import LowDimensionalTopology.Geometry.Teichmuller.CoefficientDifferenceReverseEstimate
public import LowDimensionalTopology.Geometry.Teichmuller.GammaCoefficientEncoding
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCMetric

/-!
# The actual Banach coefficients of original general markings

Every original QC marking gives a compatible L-infinity coefficient with its
original lifted representative. Its norm is controlled by every genuine QC
bound. Small actual transitions control differences of these coefficients.
The actual coefficient projection recovers the same original marked class.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC GammaMeasurableBeltrami
universe u

variable (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
  {p : ℍ → R.carrier} (hp : IsUniformization Γ p)

/-- Encode the actual original lifted coefficient in the closed compatible
Banach space. The selected QC bound affects no almost-everywhere values. -/
def markingCoefficient (m : Marked.{u, u} R) : GammaMeasurableBeltrami.Space Γ :=
  ofCoefficient (s27u_liftCoeff_isBeltramiCoeff hp (Classical.choose_spec m.qc))
    (s27u_liftCoeff_isGammaCompatible hp m.marking)

/-- The encoded native planar representative is the original lifted coefficient. -/
theorem markingCoefficient_ae (m : Marked.{u, u} R) :
    planeRepresentative (markingCoefficient R hp m).val
      =ᵐ[volume.restrict upperHalf] s27u_liftCoeff p m.marking := by
  apply ae_plane_iff.2
  have hAE := ofCoefficient_coe_ae
    (s27u_liftCoeff_isBeltramiCoeff hp (Classical.choose_spec m.qc))
    (s27u_liftCoeff_isGammaCompatible hp m.marking)
  filter_upwards [hAE] with z hz
  simpa only [markingCoefficient, planeRepresentative_coe] using hz

/-- Every actual QC upper bound controls the same intrinsic coefficient norm. -/
theorem markingCoefficient_norm_le (m : Marked.{u, u} R) {K : ℝ}
    (hK : IsKQCRS m.marking K) :
    ‖markingCoefficient R hp m‖ ≤ (K - 1) / (K + 1) := by
  have hk₀ : 0 ≤ (K - 1) / (K + 1) :=
    div_nonneg (by linarith [hK.1]) (by linarith [hK.1])
  apply (norm_le_iff_plane_bound (markingCoefficient R hp m) hk₀).2
  filter_upwards [markingCoefficient_ae R hp m,
    (s27u_liftCoeff_isBeltramiCoeff hp hK).2] with z hz hb
  rwa [hz]

/-- The actual coefficient of every original QC marking is genuinely subunit. -/
theorem markingCoefficient_norm_lt_one (m : Marked.{u, u} R) :
    ‖markingCoefficient R hp m‖ < 1 := by
  obtain ⟨K, hK⟩ := m.qc
  exact (markingCoefficient_norm_le R hp m hK).trans_lt
    ((div_lt_one (by linarith [hK.1])).2 (by linarith))

/-- The original marking's actual coefficient, in the entire compatible unit ball. -/
def markingBall (m : Marked.{u, u} R) : GammaMeasurableBeltrami.Ball Γ :=
  ⟨markingCoefficient R hp m, by
    rw [Metric.mem_ball, dist_zero_right]
    exact markingCoefficient_norm_lt_one R hp m⟩

/-- The actual transition controls the genuine Banach coefficient difference.
The exact transition formula is used before applying the logarithmic estimate. -/
theorem markingCoefficient_sub_norm_le (m n : Marked.{u, u} R) :
    ‖markingCoefficient R hp m - markingCoefficient R hp n‖ ≤
      2 * Real.log (maxDilatationRS (m.marking.symm.trans n.marking)).toReal := by
  let δ := UniversalTeichmuller.dilatationDiffNorm
    (s27u_liftCoeff p m.marking) (s27u_liftCoeff p n.marking)
  have hnorm := norm_sub_le_twice_dilatationDiffNorm
    (markingCoefficient R hp m).val (markingCoefficient R hp n).val
    (markingCoefficient_norm_lt_one R hp m) (markingCoefficient_norm_lt_one R hp n)
  rw [bersInverse_dilatationDiffNorm_congr_ae
    (markingCoefficient_ae R hp m) (markingCoefficient_ae R hp n)] at hnorm
  obtain ⟨hδ, hK⟩ := transition_dilatation_spec R hp m n
  have hδ₀ : 0 ≤ δ := ENNReal.toReal_nonneg
  have hr₀ : 0 ≤ (1 + δ) / (1 - δ) := div_nonneg (by linarith) (by linarith)
  have hlog : δ ≤ Real.log ((1 + δ) / (1 - δ)) := by
    rw [Real.log_div (by linarith : 1 + δ ≠ 0) (by linarith : 1 - δ ≠ 0)]
    have hminus := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - δ)
    have hplus := Real.log_nonneg (by linarith : 1 ≤ 1 + δ)
    linarith
  rw [hK, ENNReal.toReal_ofReal hr₀]
  exact hnorm.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

variable
  (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
    ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)

include hfixed in
/-- Equal actual raw coefficients recover the same original marked class
through the actual realization projection. -/
theorem coefficientProjection_eq_mk (m : Marked.{u, u} R) :
    coefficientProjection R hp (markingBall R hp m) = mk m := by
  apply eq_of_distance_zero R hp hfixed
  apply le_antisymm ?_ (distance_nonneg _ _)
  have hbound := distance_mk_le_fractional_log R hp
    (coefficientMarking R hp (markingBall R hp m)) m
  have hae : s27u_liftCoeff p (coefficientMarking R hp (markingBall R hp m)).marking
      =ᵐ[volume.restrict upperHalf] s27u_liftCoeff p m.marking :=
    (coefficientMarking_spec R hp (markingBall R hp m)).2.trans
      (markingCoefficient_ae R hp m)
  rw [bersInverse_dilatationDiffNorm_congr_ae hae EventuallyEq.rfl,
    UniversalTeichmuller.ut_d_self] at hbound
  have hfull : distance (mk (coefficientMarking R hp (markingBall R hp m))) (mk m) ≤ 0 := by
    simpa only [add_zero, sub_zero, div_one, Real.log_one] using hbound
  change distance (mk (coefficientMarking R hp (markingBall R hp m))) (mk m) ≤ 0
  exact hfull

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
