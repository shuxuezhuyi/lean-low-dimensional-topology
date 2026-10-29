module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import LowDimensionalTopology.Unproved.Surfaces.GenusComparison
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S22_RiemannSurfaces

/-!
# Holomorphic quadratic differentials on the original complex atlas

The coefficient family satisfies the quadratic transition law and is holomorphic
on the target of each selected chart of the given atlas. It is zero outside that
chart target. The space is finite dimensional without any genus comparison.

The dimension stated with the native handle genus uses the explicit outstanding
comparison with analytic genus. No Teichmüller quotient or metric is involved.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The complex subspace of actual holomorphic quadratic coefficient families in
preferred charts selected from the original atlas. -/
def RiemannAtlas.holomorphicQuadraticDifferentialSubmodule (A : RiemannAtlas X) :
    Submodule ℂ (X → ℂ → ℂ) :=
  let := A.toChartedSpace
  LiZhongQC.holQuadDiffSubmodule X

/-- A holomorphic quadratic differential on the given original complex atlas. -/
abbrev HolomorphicQuadraticDifferential (A : RiemannAtlas X) : Type u :=
  ↥A.holomorphicQuadraticDifferentialSubmodule

namespace ClosedRiemannSurface

/-- Holomorphic quadratic differentials on any closed Riemann surface form a
finite dimensional complex vector space. -/
theorem finiteDimensional_holomorphicQuadraticDifferential (R : ClosedRiemannSurface X) :
    FiniteDimensional ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  exact LiZhongQC.k22q_finite_quadratic (S := X)

/-- The dimension of the actual quadratic differential space, stated using the
native handle genus. The only outstanding mathematical input is the explicit
comparison between analytic genus and handle genus. -/
theorem finrank_holomorphicQuadraticDifferential (R : ClosedRiemannSurface X) {g : ℕ}
    (hcomparison : Unproved.Surfaces.GenusComparison R g) (hgenus : R.HasGenus g)
    (hg : 1 < g) :
    Module.finrank ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) = 3 * g - 3 ∧
      Module.finrank ℝ (HolomorphicQuadraticDifferential R.toRiemannAtlas) = 6 * g - 6 := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let : FiniteDimensional ℂ (LiZhongQC.holQuadDiffSubmodule X) :=
    LiZhongQC.k22q_finite_quadratic (S := X)
  have hanalytic : _root_.genus X = g := hcomparison hgenus
  obtain ⟨K, hK⟩ := LiZhongQC.k22q_canonical_exists (S := X)
  obtain ⟨e⟩ := LiZhongQC.k22q_canonical_equiv hK
  have hdeg : LiZhongQC.Divisor.deg K = 2 * (g : ℤ) - 2 := by
    have h0 := LiZhongQC.k22rr_riemann_roch_analytic hK (0 : LiZhongQC.Divisor X)
    have hK' := LiZhongQC.k22rr_riemann_roch_analytic hK K
    rw [sub_zero, ← LiZhongQC.k22rr_degree_eq (0 : LiZhongQC.Divisor X),
      Jacobians.Divisor.deg_zero, hanalytic] at h0
    rw [sub_self, hanalytic] at hK'
    omega
  have hnegdeg : Jacobians.Divisor.deg X (-K) < 0 := by
    rw [map_neg, LiZhongQC.k22rr_degree_eq, hdeg]
    omega
  have hneg : LiZhongQC.ellDim (-K) = 0 := by
    rw [LiZhongQC.k22rr_ellDim_eq_lDim]
    exact Jacobians.lDim_eq_zero_of_deg_neg (-K) hnegdeg
  have hsub : K - 2 • K = -K := by
    simp only [two_smul, sub_add_eq_sub_sub, sub_self, zero_sub]
  have hdegdouble : LiZhongQC.Divisor.deg (2 • K) = 2 * LiZhongQC.Divisor.deg K := by
    change Jacobians.Divisor.deg X (2 • K) = 2 * Jacobians.Divisor.deg X K
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using
      (map_nsmul (Jacobians.Divisor.deg X) 2 K)
  have hrr2 := LiZhongQC.k22rr_riemann_roch_analytic hK (2 • K)
  rw [hsub, hneg, hdegdouble, hdeg, hanalytic] at hrr2
  have hdim : LiZhongQC.ellDim (2 • K) = 3 * g - 3 := by omega
  have hcomplex : Module.finrank ℂ (LiZhongQC.holQuadDiffSubmodule X) = 3 * g - 3 :=
    e.finrank_eq.symm.trans hdim
  change Module.finrank ℂ (LiZhongQC.holQuadDiffSubmodule X) = 3 * g - 3 ∧
    Module.finrank ℝ (LiZhongQC.holQuadDiffSubmodule X) = 6 * g - 6
  refine ⟨hcomplex, ?_⟩
  rw [finrank_real_of_complex, hcomplex]
  omega

end ClosedRiemannSurface

end LowDimensionalTopology.Geometry.Surfaces
