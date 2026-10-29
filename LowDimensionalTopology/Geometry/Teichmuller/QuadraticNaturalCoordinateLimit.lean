module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticNaturalCoordinateProjection
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.Positivity

/-! The projected slit coordinate has zero boundary value at its original centre.
The positive-order slit excludes the centre; its totalized outside-source value
is not used by this limit. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.QuadraticNaturalCoordinateData
open LowDimensionalTopology.Geometry.Teichmuller
open LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    {q : HolomorphicQuadraticDifferential R.toRiemannAtlas} {p : X}
    (D : QuadraticNaturalCoordinateData R q p)

/-- The flat primitive is normalized to zero as its original surface point
approaches the zero through the actual punctured slit source. -/
theorem projectedCoordinate_tendsto_zero (hm : 0 < D.order) :
    Tendsto D.projectedCoordinate
      (nhdsWithin p D.retainedCoordinate.source) (𝓝 (0 : ℂ)) := by
  let A := D.ordinaryNeighborhood
  have hpos : 0 < D.exponent := by dsimp [exponent]; positivity
  have hzero : A p = 0 := (ordinaryNeighborhood_data D).2.1
  have hordinary : Tendsto (fun x => ‖A x‖)
      (nhdsWithin p D.retainedCoordinate.source) (𝓝 (0 : ℝ)) := by
    have h := (A.continuousAt (ordinaryNeighborhood_data D).1).norm.tendsto
    simpa only [hzero, norm_zero] using h.mono_left nhdsWithin_le_nhds
  have hpower : Tendsto (fun x => Real.rpow ‖A x‖ D.exponent)
      (nhdsWithin p D.retainedCoordinate.source) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.rpow_eq_pow, Real.zero_rpow hpos.ne'] using
      (Real.continuousAt_rpow_const 0 D.exponent (Or.inr hpos.le)).tendsto.comp hordinary
  have hnorm : (fun x => ‖D.projectedCoordinate x‖) =ᶠ[
      nhdsWithin p D.retainedCoordinate.source] (fun x => Real.rpow ‖A x‖ D.exponent) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hcut : A x ∈ quadraticSlitExponential.target := by
      rw [retainedCoordinate, ite_eq_right (Nat.ne_of_gt hm)] at hx
      exact hx.2
    let u := quadraticSlitExponential.symm (A x)
    have he : Complex.exp u = A x :=
      (quadraticSlitExponential_apply u).symm.trans (quadraticSlitExponential.right_inv hcut)
    have hp : D.projectedCoordinate x = Complex.exp ((D.exponent : ℂ) * u) := by
      simp only [projectedCoordinate, targetProjection, retainedCoordinate,
        ite_eq_right (Nat.ne_of_gt hm)]
      change Complex.exp ((((D.order + 2 : ℕ) : ℂ) / 2) *
        quadraticSlitExponential.symm (A x)) = Complex.exp ((D.exponent : ℂ) * u)
      congr 1
      simp only [u, exponent, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
    rw [hp, ← he, Complex.norm_exp, Complex.norm_exp, Real.rpow_eq_pow, ← Real.exp_mul]
    congr 1
    simp [Complex.mul_re, mul_comm]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (Filter.Tendsto.congr' hnorm.symm hpower)

end LowDimensionalTopology.Geometry.Teichmuller.QuadraticNaturalCoordinateData
