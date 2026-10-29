module

public import LowDimensionalTopology.Unproved.SeveralComplexVariables.HolomorphicZeroSetDisk
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.NormNum

/-!
# The zero-derivative contradiction on an actual holomorphic disk

The independent scalar zero-set disk principle supplies the actual disk.
The actual composite has zero derivative everywhere on the open unit disk,
so the native mean-value theorem makes it constant. Injectivity of both
original maps then gives a contradiction. No Jacobian theorem is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set

namespace LowDimensionalTopology.Geometry.SeveralComplexVariables

/-- An analytic vector map whose derivative vanishes on a nonempty proper
scalar analytic zero set cannot be injective on the original domain,
conditional only on the independent scalar zero-set disk principle. -/
theorem not_injOn_of_fderiv_zero_on_zero_set
    (hDisk : LowDimensionalTopology.Unproved.SeveralComplexVariables.HolomorphicZeroSetContainsDisk)
    {n : ℕ} (hn : 2 ≤ n) {D : Set (Fin n → ℂ)}
    (hD : IsOpen D) (hDc : IsPreconnected D)
    {g : (Fin n → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g D)
    (hzero : ∃ z ∈ D, g z = 0) (hproper : ∃ z ∈ D, g z ≠ 0)
    {F : (Fin n → ℂ) → (Fin n → ℂ)} (hF : AnalyticOnNhd ℂ F D)
    (hDF : ∀ z ∈ D, g z = 0 → fderiv ℂ F z = 0) :
    ¬Set.InjOn F D := by
  intro hInj
  obtain ⟨γ, hγ, hγInj, hγMaps⟩ := hDisk n hn D hD hDc g hg hzero hproper
  have hcomp : DifferentiableOn ℂ (F ∘ γ) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact (((hF (γ z) (hγMaps hz).1).differentiableAt).comp z
      (hγ z hz).differentiableAt).differentiableWithinAt
  have hcompZero : (Metric.ball (0 : ℂ) 1).EqOn (fderiv ℂ (F ∘ γ)) 0 := by
    intro z hz
    change fderiv ℂ (F ∘ γ) z = 0
    have hFz := (hF (γ z) (hγMaps hz).1).differentiableAt
    have hγz := (hγ z hz).differentiableAt
    calc
      fderiv ℂ (F ∘ γ) z =
          (fderiv ℂ F (γ z)).comp (fderiv ℂ γ z) := fderiv_comp z hFz hγz
      _ = (0 : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)).comp (fderiv ℂ γ z) :=
        congrArg (fun L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) =>
          L.comp (fderiv ℂ γ z)) (hDF (γ z) (hγMaps hz).1 (hγMaps hz).2)
      _ = 0 := rfl
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    norm_num [Metric.mem_ball]
  have hhalf : ((1 / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    norm_num [Metric.mem_ball, Complex.norm_real, Real.norm_eq_abs]
  have hconst : (F ∘ γ) (0 : ℂ) = (F ∘ γ) ((1 / 2 : ℝ) : ℂ) :=
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).is_const_of_fderiv_eq_zero
      (𝕜 := ℂ) (f := F ∘ γ)
      (convex_ball (0 : ℂ) 1).isPreconnected hcomp hcompZero h0 hhalf
  have hγeq : γ (0 : ℂ) = γ ((1 / 2 : ℝ) : ℂ) :=
    hInj (hγMaps h0).1 (hγMaps hhalf).1 hconst
  have hpoints : (0 : ℂ) = ((1 / 2 : ℝ) : ℂ) := hγInj h0 hhalf hγeq
  have hreal := congrArg Complex.re hpoints
  norm_num at hreal

end LowDimensionalTopology.Geometry.SeveralComplexVariables
