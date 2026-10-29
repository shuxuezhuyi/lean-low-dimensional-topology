/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNThreeBlockEmbedding
public import LowDimensionalTopology.Geometry.Teichmuller.FrickeMarkedLengthSpectrumEmbedding

/-!
# Original three-block classes and the complete length spectrum

The full period circles of the same selected original geodesics define
essential unoriented free classes. Their actual spectrum evaluations equal
the prescribed three-block map. The same geometric premises therefore give
a finite spectrum evaluation and the full positive spectrum proper embedding.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

private theorem exists_essential_circle_of_geodesic
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (q : OriginalClosedGeodesic M)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ∃ c : EssentialSimpleCircle X,
      LiZhongQC.FreelyHomotopic (circleRepresentativeLoop c.val) q.toLoop := by
  let := R.compactSpace
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  have hcont : Continuous (q.periodic.lift : AddCircle (1 : ℝ) → X) :=
    continuous_coinduced_dom.2 q.continuous
  let c : C(Circle, X) :=
    ⟨fun z => q.periodic.lift (e.symm z), hcont.comp e.symm.continuous⟩
  have hexp (t : unitInterval) : e ((t : ℝ) : AddCircle (1 : ℝ)) = Circle.expLoop t := by
    dsimp only [e]
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, Circle.expLoop_apply]
    simp only [div_one]
  have hfree : LiZhongQC.FreelyHomotopic (circleRepresentativeLoop c) q.toLoop := by
    apply LiZhongQC.s30b_fh_of_eq
    intro t
    change q.periodic.lift (e.symm (Circle.expLoop t)) = q.curve (t : ℝ)
    simpa only [← hexp t, e.symm_apply_apply] using q.periodic.lift_coe (t : ℝ)
  have hnon : ¬ c.Nullhomotopic := by
    intro hc
    obtain ⟨x, hx⟩ := circleRepresentativeLoop_null_of_null hc
    exact q.not_isNullHomotopicLoop
      ⟨x, LiZhongQC.s30b_fh_trans (LiZhongQC.s30b_fh_symm hfree) hx⟩
  exact ⟨⟨c, hq.comp e.symm.injective, hnon⟩, hfree⟩

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

private theorem fricke_length_eq_of_freelyHomotopic
    {α β : LiZhongQC.Loop X} (h : LiZhongQC.FreelyHomotopic α β)
    (t : nativeFrickeImage hA) :
    frickeGeodesicLength R hg hgenus hA hAlt α t =
      frickeGeodesicLength R hg hgenus hA hAlt β t := by
  let := nativeFrickeTopology hA
  have hcongr (u : TeichmullerSpace.{0, 0} R) :
      markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α u =
        markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus β u := by
    refine Quotient.inductionOn u ?_
    intro m
    exact congrArg ENNReal.toReal (LiZhongQC.s30b_fhl_congr _
      (LiZhongQC.s30b_fh_map m.markingMap.continuous h))
  exact hcongr ((nativeFrickeHomeomorph hA hAlt).symm t)

variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
variable (D₀ : OriginalFNRealization M inc) (T : OriginalFNThreeBlockData D₀)

/-- The actual three blocks supply finite evaluations of the same complete
positive spectrum, with the original full-period free classes preserved. -/
theorem nativeFiniteLengthEmbedding_of_originalFNThreeBlock
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)
    (hConvex : Unproved.Teichmuller.OriginalFNTransverseTwistLengthConvexity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hLocal : Unproved.Teichmuller.OriginalFNTransverseOtherTwistsInvariant
      R hg hgenus hA hAlt D₀ T φ Θ)
    (hShift : Unproved.Teichmuller.OriginalFNSignedDehnLengthShift
      R hg hgenus hA hAlt D₀ T φ Θ) :
    Unproved.Teichmuller.NativeFiniteLengthEmbedding
      R (Nat.succ_le_of_lt hg) hgenus hA hAlt := by
  classical
  let := R.compactSpace
  let J := originalFNThreeBlockIndex g hg
  have hsimple (i : Fin (3 * g - 3) ⊕ (Fin (3 * g - 3) ⊕ Fin (3 * g - 3))) :
      Function.Injective ((T.blockGeodesic i).periodic.lift : AddCircle (1 : ℝ) → X) := by
    cases i with
    | inl j => exact D₀.simple j
    | inr i =>
        cases i with
        | inl j => exact T.tau0_simple j
        | inr j => exact T.tau1_simple j
  choose cs hcs using fun k : Fin (9 * g - 9) =>
    exists_essential_circle_of_geodesic R M (T.blockGeodesic (J k)) (hsimple (J k))
  let classes : Fin (9 * g - 9) → EssentialSimpleFreeClass X := fun k => (cs k).freeClass
  let f : nativeFrickeImage hA → (Fin (9 * g - 9) → Set.Ioi (0 : ℝ)) :=
    fun t k => frickeMarkedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus hA hAlt t (classes k)
  have hmap : f = originalFNThreeBlockLengthMap R hg hgenus hA hAlt D₀ T := by
    funext t k
    apply Subtype.ext
    change (frickeMarkedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus hA hAlt t
      (cs k).freeClass : ℝ) =
        frickeGeodesicLength R hg hgenus hA hAlt (T.blockGeodesic (J k)).toLoop t
    rw [frickeMarkedLengthSpectrum_apply]
    exact fricke_length_eq_of_freelyHomotopic R hg hgenus hA hAlt (hcs k) t
  refine ⟨classes, ?_⟩
  change Topology.IsEmbedding f ∧ IsProperMap f
  rw [hmap]
  exact originalFNThreeBlockLengthMap_properEmbedding R hg hgenus hA hAlt D₀ T
    hU φ Θ hφ hΘ hRigid hRealize hConvex hLocal hShift

/-- The complete original positive marked spectrum is a proper embedding
under the same given three-block data and the same geometric premises. -/
theorem frickeMarkedLengthSpectrum_properEmbedding_of_originalFNThreeBlock
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)
    (hConvex : Unproved.Teichmuller.OriginalFNTransverseTwistLengthConvexity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hLocal : Unproved.Teichmuller.OriginalFNTransverseOtherTwistsInvariant
      R hg hgenus hA hAlt D₀ T φ Θ)
    (hShift : Unproved.Teichmuller.OriginalFNSignedDehnLengthShift
      R hg hgenus hA hAlt D₀ T φ Θ) :
    Topology.IsEmbedding
      (frickeMarkedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus hA hAlt) ∧
      IsProperMap (frickeMarkedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus hA hAlt) := by
  exact frickeMarkedLengthSpectrum_properEmbedding_of_nativeFiniteLengthEmbedding
    R (Nat.succ_le_of_lt hg) hgenus hA hAlt
    (nativeFiniteLengthEmbedding_of_originalFNThreeBlock R hg hgenus hA hAlt D₀ T
      hU φ Θ hφ hΘ hRigid hRealize hConvex hLocal hShift)

end LowDimensionalTopology.Geometry.Teichmuller
