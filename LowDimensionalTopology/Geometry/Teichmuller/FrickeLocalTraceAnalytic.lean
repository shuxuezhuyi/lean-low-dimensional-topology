module

public import LowDimensionalTopology.Geometry.Teichmuller.FrickeGeodesicLengthTrace
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalProjectiveRelator
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

/-- The positive hyperbolic trace-square branch is analytic in finite real coordinates. -/
theorem analyticAt_arcosh_traceSquare {n : ℕ} {T : (Fin n → ℝ) → ℝ}
    {v : Fin n → ℝ} (hT : AnalyticAt ℝ T v) (ht : 4 < T v) :
    AnalyticAt ℝ (fun y => Real.arcosh (T y / 2 - 1)) v := by
  have ha : AnalyticAt ℝ (fun y => T y / 2 - 1) v :=
    (hT.div_const (c := 2)).sub analyticAt_const
  have hd : T v / 2 - 1 ∈ Set.Ioi (1 : ℝ) := by
    change 1 < T v / 2 - 1
    linarith
  simpa only [Function.comp_def] using (Real.analyticAt_arcosh hd).comp (f := fun y => T y / 2 - 1) ha

/-- A raw real two-by-two matrix germ has analytic trace square. -/
theorem analyticAt_rawMatrix_traceSquare {n : ℕ}
    {B : (Fin n → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {v : Fin n → ℝ}
    (hB : ∀ i j, AnalyticAt ℝ (fun y => B y i j) v) :
    AnalyticAt ℝ (fun y => (Matrix.trace (B y)) ^ 2) v := by
  simp only [Matrix.trace_fin_two]
  exact ((hB 0 0).add (hB 1 1)).pow 2

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

/-- A scalar trace-square germ matching one fixed original word extends the literal length locally. -/
theorem exists_local_analytic_frickeLength_extension_of_traceSquare
    (α : LiZhongQC.Loop X) (w : FreeGroup (StandardLabels g))
    (v : nativeFrickeImage hA) (U : Set (Fin (6 * g - 6) → ℝ))
    (hU : U ∈ 𝓝 (v : Fin (6 * g - 6) → ℝ))
    (T : (Fin (6 * g - 6) → ℝ) → ℝ)
    (hT : AnalyticAt ℝ T (v : Fin (6 * g - 6) → ℝ)) (ht : 4 < T v)
    (hmatch : ∀ m : MarkedRiemannSurface.{0, 0} R,
      finiteFrickeCoordinates hA (TeichmullerSpace.mk m) ∈ U →
      T (finiteFrickeCoordinates hA (TeichmullerSpace.mk m)) =
        (Matrix.trace ((FreeGroup.lift (fun s =>
          (chosenCanonicalModel hA m).matrices ((edgeLabelEquiv g).symm s)) w).val)) ^ 2)
    (hcover : ∀ m : MarkedRiemannSurface.{0, 0} R,
      finiteFrickeCoordinates hA (TeichmullerSpace.mk m) ∈ U →
      let P := chosenCanonicalModel hA m
      let A := FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w
      ∃ q : OriginalClosedGeodesic P.model,
        LiZhongQC.FreelyHomotopic
          ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩ q.toLoop ∧
        (∀ z : ℍ, P.model.halfPlaneCover (A • z) = P.model.halfPlaneCover z) ∧
        4 < (Matrix.trace A.val) ^ 2 ∧
        LiZhongQC.Covers P.model.halfPlaneCover A q.toLoop) :
    ∃ F : (Fin (6 * g - 6) → ℝ) → ℝ,
      AnalyticAt ℝ F (v : Fin (6 * g - 6) → ℝ) ∧
      ∃ W ∈ 𝓝 (v : Fin (6 * g - 6) → ℝ),
        ∀ t : nativeFrickeImage hA, (t : Fin (6 * g - 6) → ℝ) ∈ W →
          F t = frickeGeodesicLength R hg hgenus hA hAlt α t := by
  refine ⟨fun y => Real.arcosh (T y / 2 - 1),
    analyticAt_arcosh_traceSquare hT ht, U, hU, ?_⟩
  intro t htU
  obtain ⟨p, hp⟩ := (mem_nativeFrickeImage_iff hA t.val).mp t.property
  obtain ⟨m, rfl⟩ := Quotient.exists_rep p
  have heq : t = ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩ := Subtype.ext hp.symm
  subst t
  obtain ⟨q, hq, hdeck, htrace, hcov⟩ := hcover m htU
  let P := chosenCanonicalModel hA m
  let A := FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w
  have hlen := frickeGeodesicLength_coordinates_eq_arcosh_of_covers
    R hg hgenus hA hAlt α m P.model q hq A hdeck htrace hcov
  change Real.arcosh
      (T (finiteFrickeCoordinates hA (TeichmullerSpace.mk m)) / 2 - 1) = _
  rw [hmatch m htU]
  exact hlen.symm

end LowDimensionalTopology.Geometry.Teichmuller
