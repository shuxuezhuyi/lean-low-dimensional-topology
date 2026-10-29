module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalWordDeck
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalLocalRawGenerators
public import LowDimensionalTopology.Geometry.Teichmuller.FixedSourceLoopWordCovers
public import LowDimensionalTopology.Geometry.Teichmuller.FrickeLocalWordTraceAnalytic
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeDomain

@[expose] public section
noncomputable section
set_option autoImplicit false
open Filter Set
open scoped UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

/-- Each actual Fricke point has an ambient analytic extension of the full original marked length. -/
theorem frickeGeodesicLength_exists_analytic_germ
    (α : LiZhongQC.Loop X) (hα : ¬ IsNullHomotopicLoop α) :
    ∀ v : nativeFrickeImage hA,
      ∃ F : (Fin (6 * g - 6) → ℝ) → ℝ,
        AnalyticAt ℝ F (v : Fin (6 * g - 6) → ℝ) ∧
        ∃ W ∈ 𝓝 (v : Fin (6 * g - 6) → ℝ),
          ∀ t : nativeFrickeImage hA, (t : Fin (6 * g - 6) → ℝ) ∈ W →
            F t = frickeGeodesicLength R hg hgenus hA hAlt α t := by
  classical
  obtain ⟨β, w, _, hw⟩ := fixedSourceLoop_word_covers_freeClass R hg e α
  intro v
  obtain ⟨p, hp⟩ := (mem_nativeFrickeImage_iff hA v.val).mp v.property
  obtain ⟨m, rfl⟩ := Quotient.exists_rep p
  have heq : v = ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩ := Subtype.ext hp.symm
  subst v
  let P := chosenCanonicalModel hA m
  let v0 := flattenFirstBookData P.firstBookCoordinates
  obtain ⟨B, hB, hnear⟩ := exists_canonicalLocalRawGenerators P (hAlt m)
  let A : (Fin (6 * g - 6) → ℝ) → StandardLabels g → FrickeRawWordMatrix :=
    fun t s => B t ((edgeLabelEquiv g).symm s)
  let T : (Fin (6 * g - 6) → ℝ) → ℝ :=
    fun t => frickeRawWordTraceInvariant w (A t)
  let U : Set (Fin (6 * g - 6) → ℝ) := {t |
    ∀ (n : MarkedRiemannSurface.{0, 0} R)
      (Q : NormalizedCanonicalFuchsianModel hg e n),
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation Q →
      flattenFirstBookData Q.firstBookCoordinates = t →
      ∀ d, ∃ c : ℝ, c ≠ 0 ∧ B t d = c • (Q.matrices d).val}
  have hU : U ∈ 𝓝 v0 := hnear
  have hbase := hnear.self_of_nhds m P (hAlt m) rfl
  choose c hc hBc using hbase
  have hcmp := frickeRawWordTraceInvariant_eq_trace_sq w (A v0)
    (fun s => P.matrices ((edgeLabelEquiv g).symm s))
    (fun s => c ((edgeLabelEquiv g).symm s))
    (fun s => hc ((edgeLabelEquiv g).symm s))
    (fun s => hBc ((edgeLabelEquiv g).symm s))
  have hT : AnalyticAt ℝ T v0 := frickeRawWordTraceInvariant_analyticAt w A v0
    (fun s i j => hB ((edgeLabelEquiv g).symm s) i j) hcmp.1
  obtain ⟨hcov0, hfh0⟩ := hw m P
  have ht0 := traceSquare_gt_four_of_essential_word_covers R hg hgenus α hα m P.model
    ⟨m.markingMap (e.symm (boundaryBase g).val), β.map m.markingMap.continuous⟩ hfh0
    (FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w)
    (canonicalWord_preserves_halfPlaneCover P w) hcov0
  have ht : 4 < T v0 := by
    change 4 < frickeRawWordTraceInvariant w (A v0)
    rw [hcmp.2]
    exact ht0
  have hmatch (n : MarkedRiemannSurface.{0, 0} R)
      (hn : finiteFrickeCoordinates hA (TeichmullerSpace.mk n) ∈ U) :
      T (finiteFrickeCoordinates hA (TeichmullerSpace.mk n)) =
        (Matrix.trace ((FreeGroup.lift (fun s =>
          (chosenCanonicalModel hA n).matrices ((edgeLabelEquiv g).symm s)) w).val)) ^ 2 := by
    let Q := chosenCanonicalModel hA n
    have hs := hn n Q (hAlt n) rfl
    choose d hd hBd using hs
    exact (frickeRawWordTraceInvariant_eq_trace_sq w
      (A (finiteFrickeCoordinates hA (TeichmullerSpace.mk n)))
      (fun s => Q.matrices ((edgeLabelEquiv g).symm s))
      (fun s => d ((edgeLabelEquiv g).symm s))
      (fun s => hd ((edgeLabelEquiv g).symm s))
      (fun s => hBd ((edgeLabelEquiv g).symm s))).2
  apply exists_local_analytic_frickeLength_extension_of_word_covers
    R hg hgenus hA hAlt α hα w
    ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m), ⟨TeichmullerSpace.mk m, rfl⟩⟩
    U hU T hT ht hmatch
  intro n _
  let Q := chosenCanonicalModel hA n
  obtain ⟨hcov, hfh⟩ := hw n Q
  exact ⟨⟨n.markingMap (e.symm (boundaryBase g).val), β.map n.markingMap.continuous⟩,
    hfh, canonicalWord_preserves_halfPlaneCover Q w, hcov⟩

/-- On the actual open Fricke image, its zero extension is real analytic near every point. -/
theorem frickeGeodesicLength_zeroExtension_analyticOnNhd
    (α : LiZhongQC.Loop X) (hα : ¬ IsNullHomotopicLoop α) :
    AnalyticOnNhd ℝ
      (fun x : Fin (6 * g - 6) → ℝ => show ℝ from by
        classical
        exact if hx : x ∈ nativeFrickeImage hA then
          frickeGeodesicLength R hg hgenus hA hAlt α ⟨x, hx⟩ else 0)
      (nativeFrickeImage hA) := by
  classical
  intro x hx
  obtain ⟨F, hF, W, hW, hEq⟩ :=
    frickeGeodesicLength_exists_analytic_germ R hg hgenus hA hAlt α hα ⟨x, hx⟩
  apply hF.congr
  filter_upwards [(nativeFrickeImage_domain R hg hgenus hA hAlt).1.mem_nhds hx, hW]
    with y hy hWy
  simpa only [dite_eq_left hy] using hEq ⟨y, hy⟩ hWy

end LowDimensionalTopology.Geometry.Teichmuller
