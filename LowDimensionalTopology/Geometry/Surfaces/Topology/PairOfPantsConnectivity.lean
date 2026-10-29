module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.PairOfPantsModel
public import Mathlib.Analysis.Convex.PathConnected

public section
noncomputable section
open Set
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Surfaces

private def pantsUpperArc (z : ℂ) (t : ℝ) : ℂ :=
  ⟨(1 - t) * z.re, Real.sqrt (z.im ^ 2 + z.re ^ 2 * (t * (2 - t)))⟩

private theorem pantsUpperArc_radicand (x y t : ℝ) (ht : t ∈ Icc 0 1) :
    0 ≤ y ^ 2 + x ^ 2 * (t * (2 - t)) :=
  add_nonneg (sq_nonneg y)
    (mul_nonneg (sq_nonneg x) (mul_nonneg ht.1 (by linarith [ht.2])))

private theorem pantsUpperArc_hole_inequality (x y a t : ℝ) (ht : t ∈ Icc 0 1)
    (ha : (1 : ℝ) / 4 < (x - a) ^ 2 + y ^ 2)
    (hb : (1 : ℝ) / 4 < a ^ 2) :
    (1 : ℝ) / 4 < ((1 - t) * x - a) ^ 2 +
      (Real.sqrt (y ^ 2 + x ^ 2 * (t * (2 - t)))) ^ 2 := by
  have hb' : (1 : ℝ) / 4 < x ^ 2 + y ^ 2 + a ^ 2 := by
    nlinarith only [hb, sq_nonneg x, sq_nonneg y]
  have hc : (1 : ℝ) / 4 < (1 - t) * ((x - a) ^ 2 + y ^ 2) +
      t * (x ^ 2 + y ^ 2 + a ^ 2) :=
    (convex_Ioi (𝕜 := ℝ) ((1 : ℝ) / 4)) ha hb'
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  rw [Real.sq_sqrt (pantsUpperArc_radicand x y t ht)]
  nlinarith only [hc]

private theorem pantsHalf_norm_iff (z : ℂ) (a : ℝ) :
    (1 : ℝ) / 2 < ‖z - (a : ℂ)‖ ↔
      (1 : ℝ) / 4 < (z.re - a) ^ 2 + z.im ^ 2 := by
  rw [← sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg _)]
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num [pow_two]

private theorem pantsUpperArc_mem (z : ℂ) (hz : z ∈ pantsPlanarRegion)
    (t : ℝ) (ht : t ∈ Icc 0 1) : pantsUpperArc z t ∈ pantsPlanarRegion := by
  have hn : ‖pantsUpperArc z t‖ = ‖z‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, pantsUpperArc, ← pow_two]
    rw [Real.sq_sqrt (pantsUpperArc_radicand z.re z.im t ht)]
    ring
  have hh (a : ℝ) (ha : (1 : ℝ) / 4 < a ^ 2)
      (hz' : (1 : ℝ) / 2 < ‖z - (a : ℂ)‖) :
      (1 : ℝ) / 2 < ‖pantsUpperArc z t - (a : ℂ)‖ := by
    apply (pantsHalf_norm_iff _ _).mpr
    simpa only [pantsUpperArc] using pantsUpperArc_hole_inequality
      z.re z.im a t ht ((pantsHalf_norm_iff z a).mp hz') ha
  refine ⟨hn.trans_lt hz.1, ?_, ?_⟩
  · simpa using hh (-1) (by norm_num) (by simpa using hz.2.1)
  · simpa using hh 1 (by norm_num) (by simpa using hz.2.2)

private theorem pantsAxis_join (z : ℂ) (hz : z ∈ pantsPlanarRegion) :
    JoinedIn pantsPlanarRegion 0 ((‖z‖ : ℂ) * Complex.I) := by
  let f : ℝ → ℂ := fun t => ((t * ‖z‖ : ℝ) : ℂ) * Complex.I
  refine JoinedIn.ofLine (f := f) (by dsimp [f]; fun_prop)
    (by simp [f]) (by simp [f]) ?_
  rintro _ ⟨t, ht, rfl⟩
  have hnon : 0 ≤ t * ‖z‖ := mul_nonneg ht.1 (norm_nonneg z)
  have hle : t * ‖z‖ ≤ ‖z‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
  have hout : ‖f t‖ < 2 := by
    simpa [f, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnon, abs_of_nonneg ht.1] using hle.trans_lt hz.1
  have hp : 1 ≤ ‖f t + 1‖ := by
    simpa [f] using Complex.abs_re_le_norm (f t + 1)
  have hm : 1 ≤ ‖f t - 1‖ := by
    simpa [f] using Complex.abs_re_le_norm (f t - 1)
  exact ⟨hout, by linarith, by linarith⟩

private theorem pantsUpper_join (z : ℂ) (hz : z ∈ pantsPlanarRegion)
    (hy : 0 ≤ z.im) : JoinedIn pantsPlanarRegion 0 z := by
  have h₀ : pantsUpperArc z 0 = z := by
    apply Complex.ext <;> simp [pantsUpperArc, Real.sqrt_sq hy]
  have h₁ : pantsUpperArc z 1 = (‖z‖ : ℂ) * Complex.I := by
    apply Complex.ext <;> norm_num [pantsUpperArc, Complex.norm_eq_sqrt_sq_add_sq, add_comm]
  have harc : JoinedIn pantsPlanarRegion z ((‖z‖ : ℂ) * Complex.I) := by
    refine JoinedIn.ofLine (f := pantsUpperArc z) ?_ h₀ h₁ ?_
    · unfold pantsUpperArc
      simp_rw [Complex.mk_eq_add_mul_I]
      fun_prop
    · rintro _ ⟨t, ht, rfl⟩
      exact pantsUpperArc_mem z hz t ht
  exact (pantsAxis_join z hz).trans harc.symm

private theorem pantsPlanarRegion_conj_iff (z : ℂ) :
    conj z ∈ pantsPlanarRegion ↔ z ∈ pantsPlanarRegion := by
  have hp : ‖conj z + 1‖ = ‖z + 1‖ := by
    simpa only [map_add, map_one] using Complex.norm_conj (z + 1)
  have hm : ‖conj z - 1‖ = ‖z - 1‖ := by
    simpa only [map_sub, map_one] using Complex.norm_conj (z - 1)
  simp only [pantsPlanarRegion, mem_ofPred_eq, Complex.norm_conj, hp, hm]

/-- Any two points of the standard planar region can be joined inside it. -/
theorem isPathConnected_pantsPlanarRegion : IsPathConnected pantsPlanarRegion := by
  refine ⟨0, by norm_num [pantsPlanarRegion], ?_⟩
  intro z hz
  by_cases hy : 0 ≤ z.im
  · exact pantsUpper_join z hz hy
  · have hcz : conj z ∈ pantsPlanarRegion := (pantsPlanarRegion_conj_iff z).mpr hz
    have hcy : 0 ≤ (conj z).im := by
      simpa using neg_nonneg.mpr (le_of_not_ge hy)
    have hp := (pantsUpper_join (conj z) hcz hcy).map
      Complex.continuous_conj.continuousOn
    have hm : conj '' pantsPlanarRegion ⊆ pantsPlanarRegion := by
      rintro _ ⟨w, hw, rfl⟩
      exact (pantsPlanarRegion_conj_iff w).mpr hw
    simpa using hp.mono hm

end LowDimensionalTopology.Geometry.Surfaces
