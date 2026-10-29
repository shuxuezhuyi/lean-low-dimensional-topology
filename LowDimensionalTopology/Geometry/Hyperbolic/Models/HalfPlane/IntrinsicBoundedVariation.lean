module
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Hyperbolic and Euclidean rectifiability of actual half-plane curves

The complex coordinate inclusion is locally Lipschitz for Mathlib's existing
hyperbolic metric. A positive height floor supplies a Lipschitz inverse.
On every compact trace these comparisons prove that intrinsic hyperbolic
bounded variation is equivalent to Euclidean bounded variation, including
arbitrary continuous curves on compact intervals with singular parametrizations.
-/

public section
noncomputable section
open Set Metric Filter
open scoped UpperHalfPlane NNReal
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The actual complex coordinate map is locally Lipschitz for the native H metric. -/
theorem locallyLipschitz_halfPlane_coe : LocallyLipschitz ((↑) : ℍ → ℂ) := by
  intro z
  let C : ℝ := 2 * z.im * Real.exp 1
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) z.im_pos.le)
    (Real.exp_pos _).le
  refine ⟨Real.toNNReal C, ball z (1 / 2), ball_mem_nhds _ (by norm_num), ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.coe_toNNReal _ hC]
  have hd : dist x y ≤ 1 := by
    have htri := dist_triangle x z y
    rw [dist_comm z y] at htri
    linarith [mem_ball.mp hx, mem_ball.mp hy]
  have him : y.im ≤ z.im * Real.exp 1 :=
    (UpperHalfPlane.im_le_im_mul_exp_dist y z).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [mem_ball.mp hy]))
        z.im_pos.le)
  have he := Real.abs_exp_sub_one_le (x := dist x y)
    (by simpa only [abs_of_nonneg dist_nonneg] using hd)
  have hexp : Real.exp (dist x y) - 1 ≤ 2 * dist x y :=
    (le_abs_self _).trans (by simpa only [abs_of_nonneg dist_nonneg] using he)
  calc
    dist (x : ℂ) (y : ℂ) ≤ y.im * (Real.exp (dist x y) - 1) :=
      UpperHalfPlane.dist_coe_le x y
    _ ≤ y.im * (2 * dist x y) := mul_le_mul_of_nonneg_left hexp y.im_pos.le
    _ ≤ (z.im * Real.exp 1) * (2 * dist x y) :=
      mul_le_mul_of_nonneg_right him (by positivity)
    _ = C * dist x y := by dsimp only [C]; ring

/-- A positive height floor makes the inverse complex coordinate globally Lipschitz. -/
theorem lipschitzOnWith_halfPlane_ofComplex_height {δ : ℝ} (hδ : 0 < δ) :
    LipschitzOnWith (Real.toNNReal (1 / δ)) UpperHalfPlane.ofComplex {z : ℂ | δ ≤ z.im} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx0 : 0 < x.im := hδ.trans_le hx
  have hy0 : 0 < y.im := hδ.trans_le hy
  have hs : δ ≤ Real.sqrt (x.im * y.im) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [pow_two] using mul_le_mul hx hy hδ.le hx0.le
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hx0,
    UpperHalfPlane.ofComplex_apply_of_im_pos hy0,
    Real.coe_toNNReal _ (by positivity)]
  calc
    dist (⟨x, hx0⟩ : ℍ) (⟨y, hy0⟩ : ℍ) ≤ dist x y / Real.sqrt (x.im * y.im) :=
      UpperHalfPlane.dist_le_dist_coe_div_sqrt _ _
    _ ≤ dist x y / δ := div_le_div_of_nonneg_left dist_nonneg hδ hs
    _ = (1 / δ) * dist x y := by ring

/-- Intrinsic and Euclidean rectifiability coincide on any actual compact H trace. -/
theorem halfPlane_boundedVariation_iff_coe_of_compact_image
    {α : Type*} [LinearOrder α] {f : α → ℍ} {s : Set α}
    (hcompact : IsCompact (f '' s)) :
    BoundedVariationOn f s ↔ BoundedVariationOn (fun t => (f t : ℂ)) s := by
  constructor
  · intro h
    obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcompact
      locallyLipschitz_halfPlane_coe.locallyLipschitzOn
    exact hK.comp_boundedVariationOn (mapsTo_image f s) h
  · intro h
    by_cases hs : s.Nonempty
    · obtain ⟨z, _hz, hmin⟩ := hcompact.exists_isMinOn (hs.image f)
        UpperHalfPlane.continuous_im.continuousOn
      have hmaps : MapsTo (fun t => (f t : ℂ)) s {ζ : ℂ | z.im ≤ ζ.im} := by
        intro t ht
        exact hmin ⟨t, ht, rfl⟩
      have hback := (lipschitzOnWith_halfPlane_ofComplex_height z.im_pos).comp_boundedVariationOn
        hmaps h
      simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply] using hback
    · rw [Set.not_nonempty_iff_eq_empty.mp hs]
      exact BoundedVariationOn.of_finite f ∅

/-- Every continuous lift on a compact interval has equivalent intrinsic and
Euclidean BV predicates, with no differentiability or Lipschitz assumption. -/
theorem halfPlane_boundedVariation_iff_coe_of_continuousOn
    {f : ℝ → ℍ} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) :
    BoundedVariationOn f (Icc a b) ↔
      BoundedVariationOn (fun t => (f t : ℂ)) (Icc a b) :=
  halfPlane_boundedVariation_iff_coe_of_compact_image
    (isCompact_Icc.image_of_continuousOn hf)

end LowDimensionalTopology.Geometry.Hyperbolic
