module

public import LowDimensionalTopology.Geometry.Teichmuller.FrickeGeodesicLength
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

/-- The full scalar translation length is arcosh of its hyperbolic trace square. -/
theorem translationLength_eq_arcosh_traceSquare
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ht : 4 < (Matrix.trace A.val) ^ 2) :
    LiZhongQC.translationLength A = Real.arcosh ((Matrix.trace A.val) ^ 2 / 2 - 1) := by
  have htr : LiZhongQC.slTrace A = Matrix.trace A.val := by
    simp only [LiZhongQC.slTrace, Matrix.trace_fin_two]
  have hh : LiZhongQC.IsHyperbolic A := by
    change 2 < |LiZhongQC.slTrace A|
    rw [htr]
    nlinarith [sq_abs (Matrix.trace A.val), abs_nonneg (Matrix.trace A.val)]
  have h4 : 0 ≤ LiZhongQC.slTrace A ^ 2 - 4 := by rw [htr]; linarith
  have hs : (Real.sqrt (LiZhongQC.slTrace A ^ 2 - 4) / 2) ^ 2 =
      ((Matrix.trace A.val) ^ 2 - 4) / 4 := by
    rw [div_pow, Real.sq_sqrt h4, htr]
    norm_num
  have hd := Real.cosh_two_mul (Real.arsinh (Real.sqrt (LiZhongQC.slTrace A ^ 2 - 4) / 2))
  have hc := Real.cosh_sq_sub_sinh_sq
    (Real.arsinh (Real.sqrt (LiZhongQC.slTrace A ^ 2 - 4) / 2))
  rw [Real.sinh_arsinh] at hd hc
  have hcosh : Real.cosh (LiZhongQC.translationLength A) = (Matrix.trace A.val) ^ 2 / 2 - 1 := by
    rw [LiZhongQC.translationLength_eq_arsinh h4]
    nlinarith only [hd, hc, hs]
  rw [← hcosh, Real.arcosh_cosh (LiZhongQC.s30a_tl_pos hh).le]

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

/-- Any freely homotopic actual target loop computes the same marked free-class length. -/
theorem markedGeodesicLength_mk_eq_freeLength_of_freelyHomotopic
    (α : LiZhongQC.Loop X) (m : MarkedRiemannSurface.{0, 0} R)
    (M : HyperbolicSurfaceModel m.surface.toRiemannSurface) (β : LiZhongQC.Loop m.carrier)
    (hβ : LiZhongQC.FreelyHomotopic
      ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩ β) :
    markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α (TeichmullerSpace.mk m) =
      (LiZhongQC.freeHomotopyLength M.halfPlaneCover β).toReal := by
  have hi := freeLength_eq_of_analyticHomeomorph _ _
    (m.geodesicLengthModel R (Nat.succ_le_of_lt hg) hgenus) M
    (Homeomorph.refl _) (RiemannAnalyticMap.id _)
    ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩
  exact congrArg ENNReal.toReal (hi.symm.trans (LiZhongQC.s30b_fhl_congr _ hβ))

/-- A genuine full covering word computes the literal Fricke value through its actual loop. -/
theorem frickeGeodesicLength_coordinates_eq_arcosh_of_word_covers
    (α : LiZhongQC.Loop X) (m : MarkedRiemannSurface.{0, 0} R)
    (M : HyperbolicSurfaceModel m.surface.toRiemannSurface) (β : LiZhongQC.Loop m.carrier)
    (hβ : LiZhongQC.FreelyHomotopic
      ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩ β)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hdeck : ∀ z : ℍ, M.halfPlaneCover (A • z) = M.halfPlaneCover z)
    (ht : 4 < (Matrix.trace A.val) ^ 2) (hcov : LiZhongQC.Covers M.halfPlaneCover A β) :
    frickeGeodesicLength R hg hgenus hA hAlt α
      ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m), ⟨TeichmullerSpace.mk m, rfl⟩⟩ =
      Real.arcosh ((Matrix.trace A.val) ^ 2 / 2 - 1) := by
  rw [frickeGeodesicLength_coordinates,
    markedGeodesicLength_mk_eq_freeLength_of_freelyHomotopic R hg hgenus α m M β hβ]
  let := m.surface.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  have hh : LiZhongQC.IsHyperbolic A := by
    unfold LiZhongQC.IsHyperbolic LiZhongQC.slTrace
    change 2 < |A.val 0 0 + A.val 1 1|
    rw [← Matrix.trace_fin_two]
    nlinarith [sq_abs (Matrix.trace A.val), abs_nonneg (Matrix.trace A.val)]
  rw [LiZhongQC.s30a_len_hyp hp ((hΓ A).2 hdeck) hh hcov,
    ENNReal.toReal_ofReal (LiZhongQC.s30a_tl_pos hh).le]
  exact translationLength_eq_arcosh_traceSquare A ht

include hg hgenus in
/-- Essentiality of the original source excludes the zero-length covering-word branch. -/
theorem traceSquare_gt_four_of_essential_word_covers
    (α : LiZhongQC.Loop X) (hα : ¬ IsNullHomotopicLoop α)
    (m : MarkedRiemannSurface.{0, 0} R)
    (M : HyperbolicSurfaceModel m.surface.toRiemannSurface) (β : LiZhongQC.Loop m.carrier)
    (hβ : LiZhongQC.FreelyHomotopic
      ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩ β)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hdeck : ∀ z : ℍ, M.halfPlaneCover (A • z) = M.halfPlaneCover z)
    (hcov : LiZhongQC.Covers M.halfPlaneCover A β) : 4 < (Matrix.trace A.val) ^ 2 := by
  let := m.surface.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  rcases LiZhongQC.s30a_classify hp (LiZhongQC.s27g_actsFreely hp) ((hΓ A).2 hdeck) hcov with
    ⟨hzero, _⟩ | ⟨hh, _⟩
  · have hval := markedGeodesicLength_mk_eq_freeLength_of_freelyHomotopic
      R hg hgenus α m M β hβ
    rw [hzero] at hval
    have hpos := markedGeodesicLength_pos R (Nat.succ_le_of_lt hg) hgenus α hα
      (TeichmullerSpace.mk m)
    rw [hval] at hpos
    simp at hpos
  · have hht : 2 < |Matrix.trace A.val| := by
      simpa only [LiZhongQC.IsHyperbolic, LiZhongQC.slTrace, Matrix.trace_fin_two] using hh
    nlinarith [sq_abs (Matrix.trace A.val), abs_nonneg (Matrix.trace A.val)]

end LowDimensionalTopology.Geometry.Teichmuller
