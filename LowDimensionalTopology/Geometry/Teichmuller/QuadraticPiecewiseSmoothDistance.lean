module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticPiecewiseSmoothPath
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Order.Fin.Basic

/-! The literal quadratic-length infimum over the same native piecewise smooth paths. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The extended infimum of the original lengths of exactly the native smooth path carrier. -/
def piecewiseSmoothQuadraticDistance (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (a b : X) : ℝ≥0∞ :=
  letI := R.toRiemannAtlas.toChartedSpace
  ⨅ (γ : Path a b) (_ : HasPiecewiseSmoothChartSubdivision R γ),
    phiLengthPath (q : X → ℂ → ℂ) γ

/-- Every actual admissible smooth curve bounds the source infimum from above. -/
theorem piecewiseSmoothQuadraticDistance_le_length (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {a b : X} (γ : Path a b)
    (hγ : HasPiecewiseSmoothChartSubdivision R γ) :
    letI := R.toRiemannAtlas.toChartedSpace
    piecewiseSmoothQuadraticDistance R q a b ≤ phiLengthPath (q : X → ℂ → ℂ) γ := by
  let := R.toRiemannAtlas.toChartedSpace
  unfold piecewiseSmoothQuadraticDistance
  exact iInf_le_of_le γ (iInf_le _ hγ)

/-- The existing all-path infimum is below the literal smooth-path infimum. -/
theorem phiDistRS_le_piecewiseSmoothQuadraticDistance (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (a b : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    phiDistRS (q : X → ℂ → ℂ) a b ≤ piecewiseSmoothQuadraticDistance R q a b := by
  let := R.toRiemannAtlas.toChartedSpace
  unfold piecewiseSmoothQuadraticDistance
  refine le_iInf fun γ => le_iInf fun _ => ?_
  exact iInf_le (fun δ : Path a b => phiLengthPath (q : X → ℂ → ℂ) δ) γ

/-- A supplied actual smooth joining curve gives a finite source infimum. -/
theorem piecewiseSmoothQuadraticDistance_lt_top (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {a b : X} (γ : Path a b)
    (hγ : HasPiecewiseSmoothChartSubdivision R γ) :
    piecewiseSmoothQuadraticDistance R q a b < ⊤ := by
  let := R.toRiemannAtlas.toChartedSpace
  exact (piecewiseSmoothQuadraticDistance_le_length R q γ hγ).trans_lt
    (quadraticLengthPath_lt_top_of_piecewiseSmooth R q γ hγ)

/-- The actual constant path has one smooth piece in the original native chart. -/
theorem hasPiecewiseSmoothChartSubdivision_refl (R : RiemannSurface X) (a : X) :
    HasPiecewiseSmoothChartSubdivision R (Path.refl a) := by
  let := R.toRiemannAtlas.toChartedSpace
  refine ⟨1, (fun i : Fin 2 => (i.val : ℝ)), (fun _ : Fin 1 => a),
    by simp, by simp, ?_, ?_, ?_⟩
  · exact Nat.strictMono_cast.comp Fin.val_strictMono
  · intro _
    rintro _ ⟨t, _, rfl⟩
    change a ∈ (chartAt ℂ a).source
    exact mem_chart_source ℂ a
  · intro _
    change ContDiffOn ℝ ∞ (fun _ : ℝ => chartAt ℂ a a) _
    exact contDiffOn_const

/-- The original native quadratic length of the actual constant path is zero. -/
theorem quadraticLengthPath_refl (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (a : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    phiLengthPath (q : X → ℂ → ℂ) (Path.refl a) = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨n, τ, x, -, -, -, -, -, hlen⟩ :=
    quadraticLengthPath_eq_integrals_of_piecewiseSmooth R q (Path.refl a)
      (hasPiecewiseSmoothChartSubdivision_refl R a)
  rw [hlen]
  simp [Path.refl_extend]

/-- The literal source infimum is zero on the diagonal, also for the zero differential. -/
theorem piecewiseSmoothQuadraticDistance_self (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (a : X) :
    piecewiseSmoothQuadraticDistance R q a a = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  simpa only [quadraticLengthPath_refl, nonpos_iff_eq_zero] using
    piecewiseSmoothQuadraticDistance_le_length R q (Path.refl a)
      (hasPiecewiseSmoothChartSubdivision_refl R a)

end LowDimensionalTopology.Geometry.Teichmuller
