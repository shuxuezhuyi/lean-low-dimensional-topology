module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorPairing
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Pointwise positivity of the original tensor contraction

At one original point, an existing orthogonal-basis theorem diagonalizes the
positive metric. The same raised tensor then has matrix entries Hᵢⱼ / dᵢ,
so its squared trace is a finite sum of Hᵢⱼ² / (dᵢ dⱼ). All dᵢ are positive.
No norm or inner product is installed on the original tangent fibre.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

private theorem pointwisePairing_square_sum
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) (x : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    ∃ (n : ℕ) (d : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ),
      (∀ i, 0 < d i) ∧
      metricTensorPointwisePairing R g h h x =
        ∑ i, ∑ j, H i j ^ 2 / (d i * d j) ∧
      (h.val.toFun x = 0 ↔ H = 0) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  classical
  let V := TangentSpace 𝓘(ℝ, ℂ) x
  let gB : LinearMap.BilinForm ℝ V := (g.inner x).toLinearMap₁₂
  let hB : LinearMap.BilinForm ℝ V := (h.val.toFun x).toLinearMap₁₂
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have hgs : gB.IsSymm := ⟨fun v w => g.symm x v w⟩
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp hgs)
  let n := Module.finrank ℝ V
  let d : Fin n → ℝ := fun i => g.inner x (b i) (b i)
  let H : Matrix (Fin n) (Fin n) ℝ := LinearMap.BilinForm.toMatrix b hB
  let A : Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.toMatrix b b (metricRaisedTensor R g h x)
  have hd (i : Fin n) : 0 < d i := g.pos x (b i) (b.ne_zero i)
  have hs := h.property
  change ∀ (y : X) (v w : RealSurfaceTangent R.toRiemannSurface y),
    h.val.toFun y v w = h.val.toFun y w v at hs
  have hsym (i j : Fin n) : H i j = H j i := by
    simp only [H, LinearMap.BilinForm.toMatrix_apply]
    change h.val.toFun x (b i) (b j) = h.val.toFun x (b j) (b i)
    exact hs x (b i) (b j)
  have hG : LinearMap.BilinForm.toMatrix b gB = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    change g.inner x (b i) (b j) = Matrix.diagonal d i j
    by_cases hij : i = j
    · subst j
      exact (Matrix.diagonal_apply_eq d i).symm
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hb hij
  have heq : gB.compRight (metricRaisedTensor R g h x) = hB := by
    ext v w
    change g.inner x v (metricRaisedTensor R g h x w) = h.val.toFun x v w
    rw [g.symm x v (metricRaisedTensor R g h x w), metricRaisedTensor_spec]
    exact hs x w v
  have hm := congrArg (LinearMap.BilinForm.toMatrix b) heq
  rw [LinearMap.BilinForm.toMatrix_compRight, hG] at hm
  change Matrix.diagonal d * A = H at hm
  have hA (i j : Fin n) : A i j = H i j / d i := by
    apply (eq_div_iff (ne_of_gt (hd i))).mpr
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hm
    have hdA : d i * A i j = H i j := by
      simpa only [Matrix.diagonal_mul] using hij
    simpa only [mul_comm] using hdA
  refine ⟨n, d, H, hd, ?_, ?_⟩
  · change LinearMap.trace ℝ V
      ((metricRaisedTensor R g h x).comp (metricRaisedTensor R g h x)) = _
    rw [LinearMap.trace_eq_matrix_trace ℝ b, LinearMap.toMatrix_comp b b b]
    change (∑ i, ∑ j, A i j * A j i) = _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA i j, hA j i, hsym j i, div_mul_div_comm, pow_two]
  · constructor
    · intro hh
      ext i j
      change LinearMap.BilinForm.toMatrix b hB i j = 0
      rw [LinearMap.BilinForm.toMatrix_apply]
      change h.val.toFun x (b i) (b j) = 0
      exact congrArg
        (fun L : V →L[ℝ] V →L[ℝ] ℝ => L (b i) (b j)) hh
    · intro hH
      have hlin : hB = 0 := by
        apply (LinearMap.BilinForm.toMatrix b).injective
        simpa only [map_zero] using hH
      ext v w
      exact congrArg (fun B : LinearMap.BilinForm ℝ V => B v w) hlin

/-- The original metric contraction of a symmetric tensor with itself is
nonnegative at every original point, for every original positive metric. -/
theorem metricTensorPointwisePairing_self_nonneg
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) (x : X) :
    0 ≤ metricTensorPointwisePairing R g h h x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  obtain ⟨n, d, H, hd, hpair, _⟩ := pointwisePairing_square_sum R g h x
  rw [hpair]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (sq_nonneg (H i j)) (le_of_lt (mul_pos (hd i) (hd j)))

/-- Zero self-contraction at an original point is equivalent to the whole
original bilinear form being zero, with both native tangent slots retained. -/
theorem metricTensorPointwisePairing_self_eq_zero_iff
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) (x : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    metricTensorPointwisePairing R g h h x = 0 ↔ h.val.toFun x = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  obtain ⟨n, d, H, hd, hpair, hform⟩ := pointwisePairing_square_sum R g h x
  have hterm (i j : Fin n) : 0 ≤ H i j ^ 2 / (d i * d j) :=
    div_nonneg (sq_nonneg (H i j)) (le_of_lt (mul_pos (hd i) (hd j)))
  have hrow (i : Fin n) : 0 ≤ ∑ j, H i j ^ 2 / (d i * d j) :=
    Finset.sum_nonneg (fun j _ => hterm i j)
  constructor
  · intro hz
    apply hform.mpr
    ext i j
    change H i j = 0
    have hsum : (∑ i, ∑ j, H i j ^ 2 / (d i * d j)) = 0 := by
      rw [← hpair]
      exact hz
    have hrow0 : (∑ j, H i j ^ 2 / (d i * d j)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hrow i)).mp hsum i (Finset.mem_univ i)
    have hij0 : H i j ^ 2 / (d i * d j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm i j)).mp
        hrow0 j (Finset.mem_univ j)
    have hsq : H i j ^ 2 = 0 :=
      (div_eq_zero_iff.mp hij0).resolve_right (ne_of_gt (mul_pos (hd i) (hd j)))
    exact sq_eq_zero_iff.mp hsq
  · intro hz
    have hH : H = 0 := hform.mp hz
    rw [hpair, hH]
    simp only [Matrix.zero_apply, zero_pow two_ne_zero, zero_div, Finset.sum_const_zero]

end LowDimensionalTopology.Geometry.Teichmuller
