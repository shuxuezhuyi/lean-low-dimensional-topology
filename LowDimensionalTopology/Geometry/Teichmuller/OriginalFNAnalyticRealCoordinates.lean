/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNRealBranchAnalytic
public import LowDimensionalTopology.Geometry.Teichmuller.FrickeGeodesicLengthAnalytic
public import Mathlib.Tactic.Convert

/-!
# The prescribed original positive-length and real-angle map

The length coordinates are the actual marked lengths of the fixed original
cuffs. The real coordinates are the same supplied continuous twist branch.
The map takes values in the positive orthant times the real angle space.
Its ambient expression is analytic for every admissible continuous branch,
and a basepoint-normalized branch is obtained as a derived choice.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
variable (D₀ : OriginalFNRealization M inc)

/-- The actual positive original cuff lengths and the same supplied real
twist branch. Essentiality and positivity are derived from the actual cuffs. -/
def originalFNRealCoordinateMap
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ)) :
    nativeFrickeImage hA →
      (Fin (3 * g - 3) → Set.Ioi (0 : ℝ)) × (Fin (3 * g - 3) → ℝ) := by
  let := R.compactSpace
  exact fun t =>
    ((fun j => ⟨frickeGeodesicLength R hg hgenus hA hAlt (D₀.cuff j).toLoop t,
      frickeGeodesicLength_pos R hg hgenus hA hAlt (D₀.cuff j).toLoop
        (D₀.cuff j).not_isNullHomotopicLoop t⟩), Θ t)

/-- The literal Euclidean coordinate expression of the same positive-target
map, extended by the zero pair outside the original Fricke image. -/
def originalFNRealCoordinateZeroExtension
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ)) :
    (Fin (6 * g - 6) → ℝ) →
      (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ) := by
  classical
  exact fun x =>
    if hx : x ∈ nativeFrickeImage hA then
      ((fun j => ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ ⟨x, hx⟩).1 j : ℝ)),
        (originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ ⟨x, hx⟩).2)
    else (0, 0)

/-- Every fixed continuous real branch of the prescribed circle phases
gives an analytic positive-length and real-angle map by the prescribed formula.
At actual marked coordinates, the length and phase retain every compatible
original target model and its prescribed cuff realization. -/
theorem originalFNRealCoordinateMap_analytic_and_coordinates
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j) :
    AnalyticOnNhd ℝ (originalFNRealCoordinateZeroExtension R hg hgenus hA hAlt D₀ Θ)
      (nativeFrickeImage hA) ∧
      ∀ (m : MarkedRiemannSurface.{0, 0} R)
        (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
        (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
        (j : Fin (3 * g - 3)),
        ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
          ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
            ⟨TeichmullerSpace.mk m, rfl⟩⟩).1 j : ℝ) = (D.cuff j).length.toReal ∧
        Circle.exp ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
          ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
            ⟨TeichmullerSpace.mk m, rfl⟩⟩).2 j) = D.phase j := by
  classical
  let := R.compactSpace
  constructor
  · have hL (j : Fin (3 * g - 3)) : AnalyticOnNhd ℝ
        (fun x : Fin (6 * g - 6) → ℝ =>
          if hx : x ∈ nativeFrickeImage hA then
            frickeGeodesicLength R hg hgenus hA hAlt (D₀.cuff j).toLoop ⟨x, hx⟩ else 0)
        (nativeFrickeImage hA) :=
      frickeGeodesicLength_zeroExtension_analyticOnNhd R hg hgenus hA hAlt
        (D₀.cuff j).toLoop (D₀.cuff j).not_isNullHomotopicLoop
    have hT := originalFNRealBranch_analyticOnNhd R hg hgenus hA hAlt D₀ hU φ Θ hφ hΘ
    have hpair := (AnalyticOnNhd.pi hL).prod (AnalyticOnNhd.pi hT)
    convert hpair using 1
    funext x
    by_cases hx : x ∈ nativeFrickeImage hA
    · simp only [originalFNRealCoordinateZeroExtension, originalFNRealCoordinateMap, dite_eq_left hx]
    · simp only [originalFNRealCoordinateZeroExtension, dite_eq_right hx]
      rfl
  · intro m N D transport j
    constructor
    · exact frickeGeodesicLength_coordinates_eq R hg hgenus hA hAlt (D₀.cuff j).toLoop
        m N (D.cuff j) (transport.cuff_orientation j)
    · exact (congrFun (hΘ j)
        ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
          ⟨TeichmullerSpace.mk m, rfl⟩⟩).trans (hφ m N D transport j)

/-- A principal-argument normalization at any actual original Fricke
basepoint selects one of the same analytic real coordinate maps. The
universal fixed-branch theorem remains independent of this normalization. -/
theorem exists_originalFNAnalyticRealCoordinates
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (t₀ : nativeFrickeImage hA) :
    ∃ (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
      (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ)),
      (∀ j, (originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ t₀).2 j =
        Complex.arg (φ t₀ j)) ∧
      (∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j) ∧
      AnalyticOnNhd ℝ (originalFNRealCoordinateZeroExtension R hg hgenus hA hAlt D₀ Θ)
        (nativeFrickeImage hA) ∧
      ∀ (m : MarkedRiemannSurface.{0, 0} R)
        (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
        (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
        (j : Fin (3 * g - 3)),
        ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
          ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
            ⟨TeichmullerSpace.mk m, rfl⟩⟩).1 j : ℝ) = (D.cuff j).length.toReal ∧
        Circle.exp ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
          ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
            ⟨TeichmullerSpace.mk m, rfl⟩⟩).2 j) = D.phase j := by
  classical
  obtain ⟨φ, Θ, hbase, hcover, htarget⟩ :=
    exists_originalFNContinuousRealBranch R hg hgenus hA hAlt D₀ hU t₀
  have hφ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)) :
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j :=
    (congrFun (hcover j)
      ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩).symm.trans (htarget m N D transport j)
  obtain ⟨hreg, heval⟩ :=
    originalFNRealCoordinateMap_analytic_and_coordinates R hg hgenus hA hAlt D₀
      hU φ Θ hφ hcover
  exact ⟨φ, Θ, hbase, hcover, hreg, heval⟩

end LowDimensionalTopology.Geometry.Teichmuller
