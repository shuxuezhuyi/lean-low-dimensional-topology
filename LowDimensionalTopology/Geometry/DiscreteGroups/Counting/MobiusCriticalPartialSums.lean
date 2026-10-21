/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Counting.MobiusCountingSeries
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology OnePoint ENNReal NNReal
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- The actual finite critical partial sum over the normalized-norm sublevel. -/
def mobiusNormCriticalPartialSum (H : Subgroup Mobius.complexMobiusGroup) [DiscreteTopology H] (t : ℝ) : ℝ :=
  let : Fintype {g : H // Mobius.mobiusNormalizedNorm g.val ≤ t} :=
    @Fintype.ofFinite _ (Mobius.discreteMobius_norm_sublevel_finite H (by assumption) t).to_subtype
  ∑ g : {g : H // Mobius.mobiusNormalizedNorm g.val ≤ t}, (Mobius.mobiusNormalizedNorm g.val.val ^ 4)⁻¹

theorem mobiusNormCriticalPartialSum_nonneg (H : Subgroup Mobius.complexMobiusGroup) [DiscreteTopology H] (t : ℝ) :
    0 ≤ mobiusNormCriticalPartialSum H t := by
  unfold mobiusNormCriticalPartialSum
  exact Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (by positivity))

theorem mobiusCounting_critical_rpow (f : Mobius.complexMobiusGroup) :
    Mobius.mobiusNormalizedNorm f ^ (-4 : ℝ) = (Mobius.mobiusNormalizedNorm f ^ 4)⁻¹ := by
  rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg (mobiusCountingNorm_positive f).le]
  exact congrArg Inv.inv (Real.rpow_natCast (Mobius.mobiusNormalizedNorm f) 4)

/-- The finite critical sum below a dyadic cutoff grows at most linearly in the number of levels. -/
theorem mobiusCounting_critical_partial_dyadic (H : Subgroup Mobius.complexMobiusGroup) [DiscreteTopology H]
    (C : ℝ) (hcount : ∀ t : ℝ, 1 ≤ t → (mobiusNormCountingFunction H t : ℝ) ≤ C * t ^ 4)
    (t : ℝ) (N : ℕ) (ht : t < (2 : ℝ) ^ (N + 1)) :
    mobiusNormCriticalPartialSum H t ≤ 16 * C * (N + 1) := by
  classical
  let S := {g : H // Mobius.mobiusNormalizedNorm g.val ≤ t}
  let : Fintype S := @Fintype.ofFinite _ (Mobius.discreteMobius_norm_sublevel_finite H (by assumption) t).to_subtype
  let T := Σ n : Fin (N + 1), mobiusDyadicNormSublevel H n.val
  have hnear (g : S) := exists_nat_pow_near (mobiusCountingNorm_ge_one g.val.val) (by norm_num : (1 : ℝ) < 2)
  let k (g : S) : ℕ := Classical.choose (hnear g)
  have hk (g : S) : (2 : ℝ) ^ k g ≤ Mobius.mobiusNormalizedNorm g.val.val ∧
      Mobius.mobiusNormalizedNorm g.val.val < (2 : ℝ) ^ (k g + 1) := Classical.choose_spec (hnear g)
  have hkN (g : S) : k g < N + 1 := by
    have hN : Mobius.mobiusNormalizedNorm g.val.val ≤ t := g.property
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp ((hk g).1.trans_lt (hN.trans_lt ht))
  let e (g : S) : T := ⟨⟨k g, hkN g⟩, ⟨g.val, (hk g).2.le⟩⟩
  have hinj : Function.Injective e := by
    intro g h he
    exact Subtype.ext (congrArg (fun p : T => p.2.val) he)
  have hweight (g : S) : (Mobius.mobiusNormalizedNorm g.val.val ^ 4)⁻¹ ≤
      mobiusDyadicCountingWeight 4 (e g).1.val := by
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < 2 ^ k g)
      (hk g).1 (by norm_num : (-4 : ℝ) ≤ 0)
    rw [mobiusCounting_critical_rpow] at h
    exact h
  have hsum : (∑ g : S, (Mobius.mobiusNormalizedNorm g.val.val ^ 4)⁻¹) ≤
      ∑ p : T, mobiusDyadicCountingWeight 4 p.1.val := by
    apply Finset.sum_le_sum_of_injOn e hinj.injOn (Finset.subset_univ _)
    · intro g _
      exact hweight g
    · intro p _ _
      exact Real.rpow_nonneg (by positivity) _
  have hlevel (n : Fin (N + 1)) :
      (∑ _ : mobiusDyadicNormSublevel H n.val, mobiusDyadicCountingWeight 4 n.val) ≤ 16 * C := by
    have h := mobiusCounting_dyadic_level_bound H C 4 hcount n.val
    rw [tsum_fintype] at h
    simpa only [sub_self, Real.rpow_zero, one_pow, mul_one] using h
  have htotal : (∑ p : T, mobiusDyadicCountingWeight 4 p.1.val) ≤ 16 * C * (N + 1) := by
    change (∑ p : Σ n : Fin (N + 1), mobiusDyadicNormSublevel H n.val,
      mobiusDyadicCountingWeight 4 p.1.val) ≤ _
    rw [Fintype.sum_sigma]
    calc
      (∑ n : Fin (N + 1), ∑ _ : mobiusDyadicNormSublevel H n.val, mobiusDyadicCountingWeight 4 n.val)
          ≤ ∑ _ : Fin (N + 1), 16 * C := Finset.sum_le_sum fun n _ => hlevel n
      _ = _ := by simp [mul_comm]
  exact hsum.trans htotal

/-- A global logarithmic bound for the actual critical partial sums. -/
theorem mobius_critical_partial_sum_log_bound (H : Subgroup Mobius.complexMobiusGroup) [DiscreteTopology H] :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 2 ≤ t → mobiusNormCriticalPartialSum H t ≤ K * Real.log t := by
  obtain ⟨C, hC, hcount⟩ := normCountingFunction_le_quartic H (by assumption)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨32 * C / Real.log 2, by positivity, ?_⟩
  intro t ht
  have ht0 : 0 < t := by linarith
  obtain ⟨N, hNt, htN⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ t by linarith) (by norm_num : (1 : ℝ) < 2)
  have hp := mobiusCounting_critical_partial_dyadic H C hcount t N htN
  have hNlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ N) hNt
  rw [Real.log_pow] at hNlog
  have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hnum : (N + 1 : ℝ) * Real.log 2 ≤ 2 * Real.log t := by linarith
  have hprod := mul_le_mul_of_nonneg_left hnum (show 0 ≤ 16 * C by positivity)
  have hmain : mobiusNormCriticalPartialSum H t * Real.log 2 ≤ 32 * C * Real.log t := by
    have hm := mul_le_mul_of_nonneg_right hp hlog.le
    nlinarith
  have he : (32 * C / Real.log 2) * Real.log t = (32 * C * Real.log t) / Real.log 2 := by ring
  rw [he]
  exact (le_div_iff₀ hlog).mpr hmain

/-- Critical normalized-norm partial sums grow at most logarithmically. -/
theorem mobius_critical_partial_sum_log (H : Subgroup Mobius.complexMobiusGroup) [DiscreteTopology H] :
    Asymptotics.IsBigO atTop (mobiusNormCriticalPartialSum H) Real.log := by
  obtain ⟨K, _, hK⟩ := mobius_critical_partial_sum_log_bound H
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
  change |mobiusNormCriticalPartialSum H t| ≤ K * |Real.log t|
  rw [abs_of_nonneg (mobiusNormCriticalPartialSum_nonneg H t),
    abs_of_nonneg (Real.log_nonneg (by linarith : 1 ≤ t))]
  exact hK t ht

end
end LowDimensionalTopology.Geometry.DiscreteGroups
