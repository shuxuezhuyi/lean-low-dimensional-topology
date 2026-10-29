module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Smooth finite-dimensional two-forms from their actual evaluations

This criterion is used for the actual WP two-form in inverse real Bers
coordinates. The factor `1 / 2` only cancels the curry/alternatize round trip.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.FormInterior

/-- Smoothness of the entire finite-dimensional two-form family follows from
smoothness of all its fixed-vector evaluations. -/
theorem contDiffOn_twoForm_of_evaluations
    {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {f : D → V [⋀^Fin 2]→L[ℝ] ℝ} {s : Set D}
    (h : ∀ v w, ContDiffOn ℝ ∞ (fun t => f t ![v, w]) s) :
    ContDiffOn ℝ ∞ f s := by
  let e := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hc : ContDiffOn ℝ ∞ (fun t => (f t).curryLeft) s := by
    apply contDiffOn_clm_apply.mpr
    intro v
    have hv : ContDiffOn ℝ ∞ (fun t => e.symm ((f t).curryLeft v)) s := by
      apply contDiffOn_clm_apply.mpr
      intro w
      apply (h v w).congr
      intro t _
      change f t (Matrix.vecCons v (fun _ : Fin 1 => w)) = f t ![v, w]
      congr 1
      ext i
      fin_cases i <;> rfl
    simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using
      e.contDiff.comp_contDiffOn hv
  have hA := (hc.continuousLinearMap_comp
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := 1) ℝ V ℝ)).const_smul (1 / 2 : ℝ)
  apply hA.congr
  intro t _
  change f t = (1 / 2 : ℝ) •
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := 1) ℝ V ℝ) ((f t).curryLeft)
  rw [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft,
    ← Nat.cast_smul_eq_nsmul ℝ]
  norm_num [smul_smul]

end LowDimensionalTopology.Geometry.Teichmuller.FormInterior
