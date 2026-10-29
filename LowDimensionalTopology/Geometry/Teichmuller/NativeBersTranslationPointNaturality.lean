module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedPointNaturality

/-!
# The actual Bers-coordinate translation depends on the original point

Equal normalized boundary markings give equal inverses on the real axis.
Consequently every normalized translated coefficient has the same genuine
Bers function when the base representative is changed within that point.
The entire original coordinate-translation functions agree. The final
consumer uses equality in the original native marked-surface quotient;
it does not assume a raw coefficient operator is independent of the base.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

/-- Actual normalized inverses agree on the real axis for equal boundary markings. -/
theorem normalizedSourceInverse_eq_on_real (ν ν' : LiZhongQC.BeltramiH)
    (hpoint : ∀ x : ℝ, LiZhongQC.fMuSym ν.val x = LiZhongQC.fMuSym ν'.val x)
    (x : ℝ) :
    Function.invFunOn (LiZhongQC.fMuSym ν.val) univ (x : ℂ) =
      Function.invFunOn (LiZhongQC.fMuSym ν'.val) univ (x : ℂ) := by
  obtain ⟨_, _, _, hright, hsym⟩ := LiZhongQC.b33_t_fs_inv_spec ν
  obtain ⟨_, _, hleft', _, _⟩ := LiZhongQC.b33_t_fs_inv_spec ν'
  let y := Function.invFunOn (LiZhongQC.fMuSym ν.val) univ (x : ℂ)
  have hyreal : y.im = 0 := by
    have he := hsym (x : ℂ)
    rw [Complex.conj_ofReal] at he
    exact Complex.conj_eq_iff_im.mp he.symm
  have hy : ((y.re : ℝ) : ℂ) = y := LiZhongQC.b33_d_ofReal_re hyreal
  have he := hpoint y.re
  rw [hy] at he
  have hh : LiZhongQC.fMuSym ν'.val y = (x : ℂ) := he.symm.trans (hright x)
  have hi := congrArg (Function.invFunOn (LiZhongQC.fMuSym ν'.val) univ) hh
  rw [hleft'] at hi
  exact hi

/-- Changing the same-point base preserves every actual translated Bers function. -/
theorem translatedSourceBers_eq_of_sameBoundary (ν ν' : LiZhongQC.BeltramiH)
    (hpoint : ∀ x : ℝ, LiZhongQC.fMuSym ν.val x = LiZhongQC.fMuSym ν'.val x)
    (μ : LiZhongQC.BeltramiH) :
    LiZhongQC.bersFunction (LiZhongQC.translatedBeltrami ν.val μ.val) =
      LiZhongQC.bersFunction (LiZhongQC.translatedBeltrami ν'.val μ.val) := by
  apply (LiZhongQC.b33_t_bf_eq_iff (LiZhongQC.b33_t_tb ν μ) (LiZhongQC.b33_t_tb ν' μ)).2
  apply LiZhongQC.bg_l_forward
    (μ₁ := LiZhongQC.b33_t_tb ν μ) (μ₂ := LiZhongQC.b33_t_tb ν' μ)
  intro x
  change LiZhongQC.fMuSym (LiZhongQC.translatedBeltrami ν.val μ.val) (x : ℂ) =
    LiZhongQC.fMuSym (LiZhongQC.translatedBeltrami ν'.val μ.val) (x : ℂ)
  rw [LiZhongQC.b33_t_tb_fMuSym, LiZhongQC.b33_t_tb_fMuSym]
  simp only [Function.comp_apply]
  rw [normalizedSourceInverse_eq_on_real ν ν' hpoint x]

/-- The entire genuine coordinate-translation function is independent of the same boundary point. -/
theorem sourceBersTranslation_eq_of_sameBoundary (ν ν' : LiZhongQC.BeltramiH)
    (hpoint : ∀ x : ℝ, LiZhongQC.fMuSym ν.val x = LiZhongQC.fMuSym ν'.val x) :
    LiZhongQC.b33_t_chi ν = LiZhongQC.b33_t_chi ν' := by
  classical
  funext φ
  by_cases h : ∃ μ : LiZhongQC.BeltramiH, LiZhongQC.bersFunction μ.val = φ
  · simp only [LiZhongQC.b33_t_chi, dite_eq_left h]
    exact translatedSourceBers_eq_of_sameBoundary ν ν' hpoint h.choose
  · simp only [LiZhongQC.b33_t_chi, dite_eq_right h]

/-- The actual source Teichmüller class suffices; a.e. equality is not required. -/
theorem sourceBersTranslation_eq_of_samePoint (ν ν' : LiZhongQC.BeltramiH)
    (hpoint : (Quotient.mk LiZhongQC.teichSetoid ν : LiZhongQC.UniversalTeichmuller) =
      Quotient.mk LiZhongQC.teichSetoid ν') :
    LiZhongQC.b33_t_chi ν = LiZhongQC.b33_t_chi ν' := by
  apply sourceBersTranslation_eq_of_sameBoundary
  exact LiZhongQC.bg_l_backward (μ₁ := ν) (μ₂ := ν') (Quotient.exact hpoint)

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)

/-- Equality at the original native marked-surface point preserves the actual coordinate map. -/
theorem nativePointBersTranslation_eq (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν') :
    LiZhongQC.b33_t_chi (toSourceGamma ν).val = LiZhongQC.b33_t_chi (toSourceGamma ν').val := by
  apply sourceBersTranslation_eq_of_sameBoundary
  exact Quotient.exact (sourcePoint_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint)

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
