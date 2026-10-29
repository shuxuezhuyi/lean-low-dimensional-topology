module

public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicTarget
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Completeness of the actual weighted automorphic space

Norm convergence in the faithful weighted supremum space gives uniform
convergence of the original functions on every compact lower-plane set, because
the square of height has a positive minimum there. The holomorphic limit theorem
and pointwise limits of the original automorphy equations show that the actual
automorphic submodule is closed. It consequently inherits completeness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open LiZhongQC

/-- The actual weighted norm controls the difference at every original point. -/
theorem decode_sub_weighted_bound (f g : Target) (z : Lower) :
    ‖decode f z - decode g z‖ * z.val.im ^ 2 ≤ ‖f - g‖ := by
  have he : decode (f - g) z = decode f z - decode g z :=
    congrFun (decodeLinearMap.map_sub f g) (z : ℂ)
  rw [← he, norm_decode_mul_weight]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero (f - g) z

/-- Genuine weighted-norm convergence gives locally uniform convergence of
the actual decoded functions on the complete lower half-plane. -/
theorem tendstoLocallyUniformlyOn_decode {ι : Type*} {l : Filter ι}
    {F : ι → Target} {f : Target} (hF : Tendsto F l (𝓝 f)) :
    TendstoLocallyUniformlyOn (fun n => decode (F n)) (decode f) l lowerHalf := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_lowerHalf]
  intro K hKU hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_cases hKn : K.Nonempty
  · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKn
      ((Complex.continuous_im.pow 2).continuousOn)
    let m : ℝ := z₀.im ^ 2
    have hm : 0 < m := sq_pos_of_ne_zero (ne_of_lt (show z₀.im < 0 from hKU hz₀))
    have hsmall : ∀ᶠ n in l, ‖F n - f‖ < ε * m := by
      simpa only [mem_ball, dist_eq_norm] using
        hF.eventually (ball_mem_nhds f (mul_pos hε hm))
    filter_upwards [hsmall] with n hn
    intro z hz
    have hprod : ‖decode f z - decode (F n) z‖ * m ≤ ‖F n - f‖ := by
      calc
        ‖decode f z - decode (F n) z‖ * m ≤
            ‖decode f z - decode (F n) z‖ * z.im ^ 2 :=
          mul_le_mul_of_nonneg_left (hmin hz) (norm_nonneg _)
        _ ≤ ‖f - F n‖ := decode_sub_weighted_bound f (F n) ⟨z, hKU hz⟩
        _ = ‖F n - f‖ := norm_sub_rev _ _
    have hlt : ‖decode f z - decode (F n) z‖ < ε :=
      (mul_lt_mul_iff_left₀ hm).mp (hprod.trans_lt hn)
    simpa only [dist_eq_norm] using hlt
  · exact Eventually.of_forall fun _ z hz => (hKn ⟨z, hz⟩).elim

/-- Holomorphy and the actual group equations are closed for the weighted
supremum norm, rather than for the unrelated raw pointwise topology. -/
theorem isClosed_automorphicSubmodule
    (Γ : Subgroup GammaMeasurableBeltrami.Deck) :
    IsClosed (automorphicSubmodule Γ : Set Target) := by
  apply isSeqClosed_iff_isClosed.mp
  intro F f hF hlim
  have hmem (n : ℕ) : decode (F n) ∈ LiZhongQC.automorphicQD Γ := hF n
  have hconv := tendstoLocallyUniformlyOn_decode hlim
  change decode f ∈ LiZhongQC.automorphicQD Γ
  refine ⟨hconv.differentiableOn (Eventually.of_forall fun n => (hmem n).1)
    isOpen_lowerHalf, fun z hz => decode_off _ hz, ?_⟩
  intro γ hγ z hz
  let w : ℂ := ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)
  let d : ℂ := (γ 1 0 : ℂ) * z + γ 1 1
  have hw : w ∈ lowerHalf := bg2_a_mem γ hz
  have hleft := (hconv.tendsto_at hw).div_const (d ^ 4)
  have hright := hconv.tendsto_at hz
  have heq : (fun n : ℕ => decode (F n) w / d ^ 4) =
      fun n : ℕ => decode (F n) z := by
    funext n
    exact (hmem n).2.2 γ hγ z hz
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The original bounded automorphic quadratic differentials form an actual
complex Banach space with their precise weighted supremum norm. -/
theorem automorphic_completeSpace
    (Γ : Subgroup GammaMeasurableBeltrami.Deck) : CompleteSpace (Automorphic Γ) :=
  (isClosed_automorphicSubmodule Γ).isComplete.completeSpace_coe

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
