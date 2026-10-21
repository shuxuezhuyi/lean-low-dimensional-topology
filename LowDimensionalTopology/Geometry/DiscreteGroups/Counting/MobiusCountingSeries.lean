/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Counting.MobiusQuarticCounting
public import Mathlib.Analysis.PSeries
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology OnePoint ENNReal NNReal
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
noncomputable section
/-! Dyadic norm sublevels and quartic counting bounds imply convergence for exponents above four. -/

theorem mobiusCountingNorm_ge_one (f : Mobius.complexMobiusGroup) : 1 ≤ Mobius.mobiusNormalizedNorm f := by
  have h := mobiusCountingNorm_sq_ge_two f
  have hp := mobiusCountingNorm_positive f
  nlinarith

theorem mobiusCounting_dyadic_identity (n : ℕ) (s : ℝ) :
    ((2 : ℝ) ^ (n + 1)) ^ 4 * ((2 : ℝ) ^ n) ^ (-s) =
      16 * ((2 : ℝ) ^ (4 - s)) ^ n := by
  calc
    ((2 : ℝ) ^ (n + 1)) ^ 4 * ((2 : ℝ) ^ n) ^ (-s)
        = 16 * (((2 : ℝ) ^ n) ^ 4 * ((2 : ℝ) ^ n) ^ (-s)) := by rw [pow_succ (2 : ℝ) n, mul_pow]; ring
    _ = 16 * ((2 : ℝ) ^ n) ^ (4 - s) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ n) 4, ← Real.rpow_add (by positivity)]
      congr 2
    _ = _ := by rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]


def mobiusDyadicNormSublevel (H : Subgroup Mobius.complexMobiusGroup) (n : ℕ) :=
  {g : H // Mobius.mobiusNormalizedNorm g.val ≤ (2 : ℝ) ^ (n + 1)}

instance mobiusDyadicNormSublevelFintype (H : Subgroup Mobius.complexMobiusGroup) [DiscreteTopology H] (n : ℕ) :
    Fintype (mobiusDyadicNormSublevel H n) :=
  @Fintype.ofFinite _ (Mobius.discreteMobius_norm_sublevel_finite H (by assumption) _).to_subtype

def mobiusDyadicCountingWeight (s : ℝ) (n : ℕ) : ℝ := ((2 : ℝ) ^ n) ^ (-s)

theorem mobiusCounting_dyadic_level_bound (H : Subgroup Mobius.complexMobiusGroup) [DiscreteTopology H]
    (C s : ℝ) (hcount : ∀ t : ℝ, 1 ≤ t → (mobiusNormCountingFunction H t : ℝ) ≤ C * t ^ 4) (n : ℕ) :
    (∑' _ : mobiusDyadicNormSublevel H n, mobiusDyadicCountingWeight s n) ≤
      (16 * C) * ((2 : ℝ) ^ (4 - s)) ^ n := by
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc := hcount ((2 : ℝ) ^ (n + 1)) (one_le_pow₀ (by norm_num))
  have he : Fintype.card (mobiusDyadicNormSublevel H n) =
      mobiusNormCountingFunction H ((2 : ℝ) ^ (n + 1)) := (Nat.card_eq_fintype_card).symm
  rw [he]
  have h := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ mobiusDyadicCountingWeight s n from Real.rpow_nonneg (by positivity) _)
  calc
    (mobiusNormCountingFunction H ((2 : ℝ) ^ (n + 1)) : ℝ) * mobiusDyadicCountingWeight s n
        ≤ (C * ((2 : ℝ) ^ (n + 1)) ^ 4) * mobiusDyadicCountingWeight s n := h
    _ = _ := by rw [mobiusDyadicCountingWeight, mul_assoc, mobiusCounting_dyadic_identity]; ring

theorem mobiusCounting_dyadicSigma_summable (H : Subgroup Mobius.complexMobiusGroup) [DiscreteTopology H]
    (s : ℝ) (hs : 4 < s) :
    Summable (fun p : Σ n, mobiusDyadicNormSublevel H n => mobiusDyadicCountingWeight s p.1) := by
  obtain ⟨C, _, hcount⟩ := normCountingFunction_le_quartic H (by assumption)
  let r : ℝ := (2 : ℝ) ^ (4 - s)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : Summable (fun n : ℕ => (16 * C) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hlevel : Summable (fun n : ℕ => ∑' _ : mobiusDyadicNormSublevel H n, mobiusDyadicCountingWeight s n) :=
    hgeom.of_nonneg_of_le
      (fun n => tsum_nonneg (fun (_ : mobiusDyadicNormSublevel H n) => Real.rpow_nonneg (by positivity) _))
      (fun n => mobiusCounting_dyadic_level_bound H C s hcount n)
  exact (summable_sigma_of_nonneg
    (f := fun p : Σ n, mobiusDyadicNormSublevel H n => mobiusDyadicCountingWeight s p.1)
    (fun (p : Σ n, mobiusDyadicNormSublevel H n) => Real.rpow_nonneg (by positivity) _)).mpr
      ⟨fun n => (hasSum_fintype (fun (_ : mobiusDyadicNormSublevel H n) => mobiusDyadicCountingWeight s
        n)).summable, hlevel⟩

/-- With arbitrary real exponent above four. -/
theorem summable_normalizedNorm_rpow_of_exponent_gt_four (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (s : ℝ) (hs : 4 < s) :
    Summable (fun g : H => Mobius.mobiusNormalizedNorm g.val ^ (-s)) := by
  classical
  let : DiscreteTopology H := hd
  have hnear (g : H) := exists_nat_pow_near (mobiusCountingNorm_ge_one g.val) (by norm_num : (1 : ℝ) < 2)
  let k (g : H) : ℕ := Classical.choose (hnear g)
  have hk (g : H) : (2 : ℝ) ^ k g ≤ Mobius.mobiusNormalizedNorm g.val ∧
      Mobius.mobiusNormalizedNorm g.val < (2 : ℝ) ^ (k g + 1) := Classical.choose_spec (hnear g)
  let e (g : H) : Σ n, mobiusDyadicNormSublevel H n := ⟨k g, ⟨g, (hk g).2.le⟩⟩
  have hinj : Function.Injective e := by
    intro g h he
    exact congrArg (fun p : Σ n, mobiusDyadicNormSublevel H n => p.2.val) he
  have heSum : Summable (fun g : H => mobiusDyadicCountingWeight s (k g)) :=
    (mobiusCounting_dyadicSigma_summable H s hs).comp_injective (i := e) hinj
  apply heSum.of_nonneg_of_le (fun (g : H) => Real.rpow_nonneg (mobiusCountingNorm_positive g.val).le (-s))
  intro g
  change Mobius.mobiusNormalizedNorm g.val ^ (-s) ≤ ((2 : ℝ) ^ k g) ^ (-s)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (hk g).1 (by linarith)

end
end LowDimensionalTopology.Geometry.DiscreteGroups
