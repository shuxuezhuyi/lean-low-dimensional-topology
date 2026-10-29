module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNBookLeftCopyTransport
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNRescaledRealTwistCoordinate
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring.Basic

/-!
# The actual left-to-right original FN phase and its full real branch

The previous ordered coordinates retain their arbitrary Fin2 labels. Book
coordinates use the geometrically certified left foot first. Exchanging the
two literal BV feet inverts the phase, so the same fixed sign corrects both
the full angle branch and the actual length-rescaled twist coordinate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped unitInterval UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

/-- The sign of the actual left-copy label relative to the retained raw order. -/
def originalFNBookSideSign (left : Fin 2) : ℝ := if left = 0 then 1 else -1

theorem originalFNBookSideSign_sq (left : Fin 2) :
    originalFNBookSideSign left * originalFNBookSideSign left = 1 := by
  by_cases h : left = 0 <;> simp only [originalFNBookSideSign, h, ite_true, ite_false] <;> norm_num

section CuffPhase

variable {Y : Type} [TopologicalSpace Y] {S : ClosedRiemannSurface Y}
    {N : HyperbolicSurfaceModel S.toRiemannSurface} {g : ℕ}
    {inc : OriginalFNCuffIncidence g}

/-- The literal BV phase from the actual left foot to the other actual foot. -/
def originalFNBookPhase (D : OriginalFNRealization N inc)
    (left : Fin (3 * g - 3) → Fin 2) (j : Fin (3 * g - 3)) : Circle :=
  originalCuffTwistPhase (D.cuff j) (D.simple j)
    (D.foot (j, left j)) (D.foot (j, if left j = 0 then 1 else 0))

/-- Reordering the two actual feet gives precisely the retained raw phase
or its inverse, without choosing any angle branch. -/
theorem originalFNBookPhase_eq (D : OriginalFNRealization N inc)
    (left : Fin (3 * g - 3) → Fin 2) (j : Fin (3 * g - 3)) :
    originalFNBookPhase D left j =
      if left j = 0 then D.phase j else (D.phase j)⁻¹ := by
  by_cases h : left j = 0
  · rw [originalFNBookPhase, h]
    rfl
  · have h1 : left j = 1 := by omega
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [originalFNBookPhase, h1]
    simp only [h10, ite_false, OriginalFNRealization.phase]
    exact originalCuffTwistPhase_reverse (D.cuff j) (D.simple j)
      (D.foot (j, 0)) (D.foot (j, 1))

/-- The side returned by an actual signed-marking seam witness is the fixed
book-left copy, using its literal lift, full cuff and positive normalizer. -/
theorem OriginalFNCopyLeftGerm.side_eq
    (D : OriginalFNRealization N inc) (j : Fin (3 * g - 3)) (left : Fin 2)
    (hleft : OriginalFNCopyLeftGerm D j left)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hp : let := S.toRiemannAtlas.toChartedSpace;
      LiZhongQC.IsUniformization Γ N.halfPlaneCover)
    (A Q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (s : ℝ) (hs : 0 < s)
    (hAΓ : A ∈ Γ) (hcov : LiZhongQC.Covers N.halfPlaneCover A (D.cuff j).toLoop)
    (hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
    (c : Fin 2) (v : C(I, ℍ))
    (hlift : ∀ u : I, LiZhongQC.adjustProjection N.halfPlaneCover Q (v u) =
      (D.pants (inc.copy (j, c)).1).projection ((D.seam (j, c)).curve u))
    (haxis : (v 0 : ℂ).re = 0)
    (hneg : ∃ ε : ℝ, 0 < ε ∧
      ∀ u : I, 0 < (u : ℝ) → (u : ℝ) < ε → (v u : ℂ).re < 0) : c = left :=
  (hleft Γ hp A Q s hs hAΓ hcov hQA c v hlift haxis).mp hneg

end CuffPhase

/-- The fixed sign correction of the same continuous full real angle branch. -/
def originalFNBookAngle
    {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    {g : ℕ} {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (left : Fin (3 * g - 3) → Fin 2) :
    C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ) :=
  ⟨fun t j => originalFNBookSideSign (left j) * Θ t j,
    continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp Θ.continuous)⟩

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface}
    {inc : OriginalFNCuffIncidence g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)

/-- The same actual positive cuff length rescales the book full real angle. -/
def originalFNBookTwistCoordinate
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (left : Fin (3 * g - 3) → Fin 2) :
    nativeFrickeImage hA → (Fin (3 * g - 3) → ℝ) :=
  originalFNRescaledRealTwistCoordinate R hg hgenus hA hAlt D₀
    (originalFNBookAngle hA Θ left)

/-- The book twist is exactly the geometrically fixed sign times the raw
twist of the same cuff, not a different length or a new branch choice. -/
theorem originalFNBookTwistCoordinate_eq
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (left : Fin (3 * g - 3) → Fin 2)
    (t : nativeFrickeImage hA) (j : Fin (3 * g - 3)) :
    originalFNBookTwistCoordinate R hg hgenus hA hAlt D₀ Θ left t j =
      originalFNBookSideSign (left j) *
        originalFNRescaledRealTwistCoordinate R hg hgenus hA hAlt D₀ Θ t j := by
  change (_ / (2 * Real.pi)) * (originalFNBookSideSign (left j) * Θ t j) =
    originalFNBookSideSign (left j) * ((_ / (2 * Real.pi)) * Θ t j)
  dsimp only [originalFNRealCoordinateMap]
  ring

/-- The geometric left-copy input yields an actual left-to-right branch on
every compatible marked target; the raw labels and the supplied branch remain. -/
theorem exists_originalFN_book_coordinates
    (hBook : Unproved.Teichmuller.OriginalFNBookLeftCopyTransport D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j) :
    ∃ left : Fin (3 * g - 3) → Fin 2,
      (∀ j, OriginalFNCopyLeftGerm D₀ j (left j)) ∧
      (∀ (m : MarkedRiemannSurface.{0, 0} R)
        (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
        (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
        (j : Fin (3 * g - 3)),
        OriginalFNCopyLeftGerm D j (left j) ∧
          Circle.exp (originalFNBookAngle hA Θ left
            ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
              ⟨TeichmullerSpace.mk m, rfl⟩⟩ j) = originalFNBookPhase D left j) ∧
      ∀ (t : nativeFrickeImage hA) (j : Fin (3 * g - 3)),
        originalFNBookTwistCoordinate R hg hgenus hA hAlt D₀ Θ left t j =
          originalFNBookSideSign (left j) *
            originalFNRescaledRealTwistCoordinate R hg hgenus hA hAlt D₀ Θ t j := by
  obtain ⟨left, href, htarget⟩ := hBook
  refine ⟨left, href, ?_, originalFNBookTwistCoordinate_eq R hg hgenus hA hAlt D₀ Θ left⟩
  intro m N D transport j
  refine ⟨htarget m N D transport j, ?_⟩
  have hraw := (congrFun (hΘ j)
    ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩).trans (hφ m N D transport j)
  rw [originalFNBookPhase_eq]
  change Circle.exp (originalFNBookSideSign (left j) * Θ _ j) = _
  by_cases h : left j = 0
  · simpa only [originalFNBookSideSign, h, ite_true, one_mul, Function.comp_apply] using hraw
  · simpa only [originalFNBookSideSign, h, ite_false, neg_one_mul, Circle.exp_neg,
      Function.comp_apply] using
      congrArg (fun z : Circle => z⁻¹) hraw

end LowDimensionalTopology.Geometry.Teichmuller
