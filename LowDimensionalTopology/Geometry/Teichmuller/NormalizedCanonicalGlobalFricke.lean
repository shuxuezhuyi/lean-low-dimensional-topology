module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalBookPointCriterion
public import LowDimensionalTopology.Unproved.Teichmuller.CanonicalNormalizedModelsAvailable
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Finite Fricke coordinates on the native marked-surface quotient

Actual normalized-model availability supplies the coordinate representatives.
The proved native invariance descends their literal coordinates to the quotient;
injectivity additionally receives the explicit canonical-axis obligations.
The finite target preserves the ascending handle and six-entry book order.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology
open Geometry.Surfaces Geometry.Teichmuller Geometry.Surfaces.HandlePresentation

namespace Geometry.Teichmuller
variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}

abbrev FirstBookData (g : ℕ) :=
  Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)

def chosenCanonicalModel
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (m : MarkedRiemannSurface.{0, 0} R) : NormalizedCanonicalFuchsianModel hg e m :=
  Classical.choice (hA m)

/-- Descent uses only the proved native equivalence invariance. -/
def groupedFrickeCoordinates
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e) :
    TeichmullerSpace.{0, 0} R → FirstBookData g :=
  Quotient.lift (fun m => (chosenCanonicalModel hA m).firstBookCoordinates)
    (fun m n hmn => (chosenCanonicalModel hA m).firstBookCoordinates_eq_of_equivalent
      (chosenCanonicalModel hA n) hmn)

theorem groupedFrickeCoordinates_mk
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (m : MarkedRiemannSurface.{0, 0} R) :
    groupedFrickeCoordinates hA (TeichmullerSpace.mk m) =
      (chosenCanonicalModel hA m).firstBookCoordinates := rfl

/-- Any supplied actual model gives the same coordinates. No alternation is used. -/
theorem groupedFrickeCoordinates_eq_model
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    {m : MarkedRiemannSurface.{0, 0} R}
    (P : NormalizedCanonicalFuchsianModel hg e m) :
    groupedFrickeCoordinates hA (TeichmullerSpace.mk m) = P.firstBookCoordinates :=
  (chosenCanonicalModel hA m).firstBookCoordinates_eq_of_equivalent P
    (MarkedRiemannSurface.equivalent_refl m)

theorem groupedFrickeCoordinates_injective
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    Function.Injective (groupedFrickeCoordinates hA) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ m =>
    induction y using Quotient.inductionOn with
    | _ n =>
      exact (TeichmullerSpace.mk_eq_mk_iff m n).mpr
        (((chosenCanonicalModel hA m).firstBookCoordinates_eq_iff_equivalent
          (chosenCanonicalModel hA n) (hAlt m) (hAlt n)).mp hxy)

/-- The six retained matrix coefficients in their original order. -/
def sixBookEntries (v : (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) : Fin 6 → ℝ :=
  ![v.1.1, v.1.2.1, v.1.2.2, v.2.1, v.2.2.1, v.2.2.2]

private theorem sixBookEntries_injective : Function.Injective sixBookEntries := by
  intro v w h
  exact Prod.ext
    (Prod.ext (congrFun h 0) (Prod.ext (congrFun h 1) (congrFun h 2)))
    (Prod.ext (congrFun h 3) (Prod.ext (congrFun h 4) (congrFun h 5)))

/-- Lexicographic handle and entry indices with the literal dimension bound. -/
def bookIndexEquiv (n : ℕ) : Fin (n - 1) × Fin 6 ≃ Fin (6 * n - 6) :=
  (finProdFinEquiv : Fin (n - 1) × Fin 6 ≃ Fin ((n - 1) * 6)).trans
    (finCongr (by rw [Nat.sub_mul, one_mul, Nat.mul_comm]))

/-- Literal ascending-handle order: a,c,d,a',c',d'. -/
def flattenFirstBookData (v : FirstBookData g) : Fin (6 * g - 6) → ℝ :=
  fun j => let p := (bookIndexEquiv g).symm j
    sixBookEntries (v p.1) p.2

theorem flattenFirstBookData_injective :
    Function.Injective (flattenFirstBookData (g := g)) := by
  intro v w h
  funext i
  apply sixBookEntries_injective
  funext k
  have hi := congrFun h ((bookIndexEquiv g) (i, k))
  simpa only [flattenFirstBookData, Equiv.symm_apply_apply] using hi

/-- The genuine global finite Fricke map on the original native quotient. -/
def finiteFrickeCoordinates
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e) :
    TeichmullerSpace.{0, 0} R → (Fin (6 * g - 6) → ℝ) :=
  flattenFirstBookData ∘ groupedFrickeCoordinates hA

/-- The full native quotient injectivity conclusion, conditional on concrete
model availability and the existing pointwise alternation obligations. -/
theorem finiteFrickeCoordinates_injective
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    Function.Injective (finiteFrickeCoordinates hA) :=
  flattenFirstBookData_injective.comp (groupedFrickeCoordinates_injective hA hAlt)

end Geometry.Teichmuller
end LowDimensionalTopology
