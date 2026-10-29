module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticC1LengthFinite
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Finite smooth chart subdivisions of an actual path in its original Riemann atlas. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The actual path has a finite subdivision into smooth pieces in its original selected atlas. -/
def HasPiecewiseSmoothChartSubdivision (R : RiemannSurface X) {a b : X}
    (γ : Path a b) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  ∃ (n : ℕ) (τ : Fin (n + 1) → ℝ) (x : Fin n → X),
    τ 0 = 0 ∧ τ (Fin.last n) = 1 ∧ StrictMono τ ∧
      (∀ i : Fin n,
        γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source) ∧
      ∀ i : Fin n, ContDiffOn ℝ ∞ (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
        (Icc (τ i.castSucc) (τ i.succ))

/-- The native quadratic length of such a smooth path is finite, also through coefficient zeros. -/
theorem quadraticLengthPath_lt_top_of_piecewiseSmooth (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {a b : X} (γ : Path a b)
    (hγ : HasPiecewiseSmoothChartSubdivision R γ) :
    letI := R.toRiemannAtlas.toChartedSpace
    phiLengthPath (q : X → ℂ → ℂ) γ < ⊤ := by
  let := R.toRiemannAtlas.toChartedSpace
  rcases hγ with ⟨n, τ, x, h0, hn, hτ, hsrc, hsmooth⟩
  refine quadraticLengthPath_lt_top_of_c1_chartSubdivision R q γ τ x h0 hn hτ.monotone hsrc ?_
  exact fun i => (hsmooth i).of_le (by simp)

/-- A smooth subdivision computes the same original length by its literal finite chart integrals. -/
theorem quadraticLengthPath_eq_integrals_of_piecewiseSmooth (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {a b : X} (γ : Path a b)
    (hγ : HasPiecewiseSmoothChartSubdivision R γ) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∃ (n : ℕ) (τ : Fin (n + 1) → ℝ) (x : Fin n → X),
      τ 0 = 0 ∧ τ (Fin.last n) = 1 ∧ StrictMono τ ∧
        (∀ i : Fin n,
          γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source) ∧
        (∀ i : Fin n, ContDiffOn ℝ ∞ (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
          (Icc (τ i.castSucc) (τ i.succ))) ∧
        phiLengthPath (q : X → ℂ → ℂ) γ =
          ∑ i : Fin n, ∫⁻ v in Ioo (τ i.castSucc) (τ i.succ),
            phiDensity ((q : X → ℂ → ℂ) (x i)) (chartAt ℂ (x i) (γ.extend v)) *
              ‖deriv (fun w : ℝ => chartAt ℂ (x i) (γ.extend w)) v‖ₑ := by
  let := R.toRiemannAtlas.toChartedSpace
  rcases hγ with ⟨n, τ, x, h0, hn, hτ, hsrc, hsmooth⟩
  refine ⟨n, τ, x, h0, hn, hτ, hsrc, hsmooth, ?_⟩
  exact quadraticLengthPath_eq_c1_chartSubdivision R q γ τ x h0 hn hτ.monotone hsrc
    (fun i => (hsmooth i).of_le (by simp))

end LowDimensionalTopology.Geometry.Teichmuller
