module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalFrickeImage
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalModelCutChange

/-!
# Unique original canonical Fricke vectors

Every actual prescribed realization transports a supplied normalized model
through its one common path. Changing the cut at the original point keeps
the same matrices, so the literal vector is unique. Equivalence invariance
uses the existing comparison of actual marked quotients and its injectivity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

private def nativeOfOriginalRealization {g : ℕ}
    (B N : OriginalGeneratorMarkedSurface g)
    (F : SmoothSurfaceEquiv B.surface.toRiemannSurface N.surface.toRiemannSurface)
    (hF : PreservesComplexOrientation B.surface.toRiemannAtlas
      N.surface.toRiemannAtlas F.toHomeomorph) :
    MarkedRiemannSurface.{0, 0} B.surface where
  carrier := N.carrier
  topology := N.topology
  surface := N.surface
  marking := F
  orientation_preserving := hF

private theorem nativeVector_eq_of_originalRealization
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable B.surface hg D.polygon)
    (N : OriginalGeneratorMarkedSurface g) (v : Fin (6 * g - 6) → ℝ)
    (hv : IsOriginalCanonicalFrickeVector hg N v)
    (F : SmoothSurfaceEquiv B.surface.toRiemannSurface N.surface.toRiemannSurface)
    (hF : PreservesComplexOrientation B.surface.toRiemannAtlas
      N.surface.toRiemannAtlas F.toHomeomorph)
    (c : Path (F.toHomeomorph B.point) N.point)
    (hc : ∀ i : Fin g × Fin 2,
      FundamentalGroup.fundamentalGroupMulEquivOfPath c
        (FundamentalGroup.map
          (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
          B.point (B.classes i)) = N.classes i) :
    finiteFrickeCoordinates hA
      (TeichmullerSpace.mk (nativeOfOriginalRealization B N F hF)) = v := by
  obtain ⟨E, hE, P, hPv⟩ := hv
  let P₀ := chosenCanonicalModel hA (nativeOfOriginalRealization B N F hF)
  obtain ⟨_L, Q, _hL, _hL₀, _hL₁, _hModel, hMatrices⟩ :=
    NormalizedCanonicalFuchsianModel.exists_transportOriginalCanonicalPath
      hg B N D hD E hE F hF c hc P₀
  have hData : Q.firstBookCoordinates = P₀.firstBookCoordinates := by
    exact congrArg (fun A : Fin g × Fin 2 → RealSL => fun i : Fin (g - 1) =>
      let positiveLift := fun b : Fin 2 =>
        let M := A (NormalizedCanonicalFuchsianModel.firstBookIndex i, b)
        if 0 < M 1 0 then M else -M
      (bookMatrixCoordinates (positiveLift 0), bookMatrixCoordinates (positiveLift 1))) hMatrices
  have hQP : Q.firstBookCoordinates = P.firstBookCoordinates :=
    Q.firstBookCoordinates_eq_of_equivalent P
      (MarkedRiemannSurface.equivalent_refl (MarkedRiemannSurface.refl N.surface))
  calc
    finiteFrickeCoordinates hA
        (TeichmullerSpace.mk (nativeOfOriginalRealization B N F hF)) =
        flattenFirstBookData P₀.firstBookCoordinates := finiteFrickeCoordinates_eq_model hA P₀
    _ = flattenFirstBookData Q.firstBookCoordinates := congrArg flattenFirstBookData hData.symm
    _ = flattenFirstBookData P.firstBookCoordinates := congrArg flattenFirstBookData hQP
    _ = v := hPv

private theorem comparison_mk_eq_of_originalRealization
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (hTransport : Unproved.Teichmuller.OriginalCanonicalFamilyMarkingTransport hg B)
    (N : OriginalGeneratorMarkedSurface g)
    (F : SmoothSurfaceEquiv B.surface.toRiemannSurface N.surface.toRiemannSurface)
    (hF : PreservesComplexOrientation B.surface.toRiemannAtlas
      N.surface.toRiemannAtlas F.toHomeomorph)
    (c : Path (F.toHomeomorph B.point) N.point)
    (hc : ∀ i : Fin g × Fin 2,
      FundamentalGroup.fundamentalGroupMulEquivOfPath c
        (FundamentalGroup.map
          (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
          B.point (B.classes i)) = N.classes i) :
    originalGeneratorComparison hg B hTransport
      (TeichmullerSpace.mk (nativeOfOriginalRealization B N F hF)) =
        OriginalGeneratorTeichmullerSpace.mk N := by
  change OriginalGeneratorTeichmullerSpace.mk
      (originalGeneratorMarkedTarget hg B hTransport (nativeOfOriginalRealization B N F hF)) =
    OriginalGeneratorTeichmullerSpace.mk N
  apply Quotient.sound
  apply OriginalGeneratorMarkedSurface.equivalent_symm
  refine ⟨Homeomorph.refl N.carrier, RiemannAnalyticMap.id _, c, ?_⟩
  intro i
  change FundamentalGroup.fundamentalGroupMulEquivOfPath c
    (FundamentalGroup.map (ContinuousMap.id N.carrier) (F.toHomeomorph B.point)
      (FundamentalGroup.map
        (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
        B.point (B.classes i))) = N.classes i
  rw [FundamentalGroup.map_id]
  change FundamentalGroup.fundamentalGroupMulEquivOfPath c
    (FundamentalGroup.map
      (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
      B.point (B.classes i)) = N.classes i
  exact hc i

/-- Every original geometrically marked surface has exactly one literal
vector under the supplied prescribed realization and native model inputs. -/
theorem existsUnique_originalCanonicalFrickeVector
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (hRealize : Unproved.Teichmuller.OriginalGeneratorPrescribedPositiveSmoothRealization hg B)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable B.surface hg D.polygon)
    (N : OriginalGeneratorMarkedSurface g) :
    ∃! v : Fin (6 * g - 6) → ℝ, IsOriginalCanonicalFrickeVector hg N v := by
  obtain ⟨E, hE⟩ : HasOriginalCanonicalCut N.surface g
      (lt_trans Nat.zero_lt_one hg) N.point N.classes := by
    cases g with
    | zero => omega
    | succ n => exact N.canonical
  obtain ⟨F, hF, c, hc⟩ := hRealize N
  let P₀ := chosenCanonicalModel hA (nativeOfOriginalRealization B N F hF)
  obtain ⟨_L, P, _hL, _hL₀, _hL₁, _hModel, _hMatrices⟩ :=
    NormalizedCanonicalFuchsianModel.exists_transportOriginalCanonicalPath
      hg B N D hD E hE F hF c hc P₀
  refine ⟨flattenFirstBookData P.firstBookCoordinates, ⟨E, hE, P, rfl⟩, ?_⟩
  intro w hw
  obtain ⟨E', hE', P', hP'⟩ := hw
  obtain ⟨Q, _hModel, _hLift, hMatrices⟩ :=
    NormalizedCanonicalFuchsianModel.exists_changeOriginalCanonicalCut
      hg N E E' (hE.trans hE'.symm) P
  have hData : Q.firstBookCoordinates = P.firstBookCoordinates := by
    exact congrArg (fun A : Fin g × Fin 2 → RealSL => fun i : Fin (g - 1) =>
      let positiveLift := fun b : Fin 2 =>
        let M := A (NormalizedCanonicalFuchsianModel.firstBookIndex i, b)
        if 0 < M 1 0 then M else -M
      (bookMatrixCoordinates (positiveLift 0), bookMatrixCoordinates (positiveLift 1))) hMatrices
  have hQP : Q.firstBookCoordinates = P'.firstBookCoordinates :=
    Q.firstBookCoordinates_eq_of_equivalent P'
      (MarkedRiemannSurface.equivalent_refl (MarkedRiemannSurface.refl N.surface))
  calc
    w = flattenFirstBookData P'.firstBookCoordinates := hP'.symm
    _ = flattenFirstBookData Q.firstBookCoordinates := congrArg flattenFirstBookData hQP.symm
    _ = flattenFirstBookData P.firstBookCoordinates := congrArg flattenFirstBookData hData

/-- The actual original equivalence preserves the unique literal vectors.
The weak smooth-transport interface is derived from the one geometry input. -/
theorem originalCanonicalFrickeVector_eq_of_equivalent
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport
      B.surface hg B.point D)
    (hRealize : Unproved.Teichmuller.OriginalGeneratorPrescribedPositiveSmoothRealization hg B)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable B.surface hg D.polygon)
    {M N : OriginalGeneratorMarkedSurface g} (hMN : M.Equivalent N)
    {v w : Fin (6 * g - 6) → ℝ}
    (hv : IsOriginalCanonicalFrickeVector hg M v)
    (hw : IsOriginalCanonicalFrickeVector hg N w) : v = w := by
  let hTransport := originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport
    hg B D hD hGeom
  obtain ⟨F, hF, c, hc⟩ := hRealize M
  obtain ⟨G, hG, d, hd⟩ := hRealize N
  have hM := comparison_mk_eq_of_originalRealization hg B hTransport M F hF c hc
  have hN := comparison_mk_eq_of_originalRealization hg B hTransport N G hG d hd
  have hclasses : TeichmullerSpace.mk (nativeOfOriginalRealization B M F hF) =
      TeichmullerSpace.mk (nativeOfOriginalRealization B N G hG) := by
    apply (originalGeneratorComparison_bijective hg B hTransport hRealize).1
    exact hM.trans ((Quotient.sound hMN).trans hN.symm)
  have hMv := nativeVector_eq_of_originalRealization hg B D hD hA M v hv F hF c hc
  have hNw := nativeVector_eq_of_originalRealization hg B D hD hA N w hw G hG d hd
  exact hMv.symm.trans ((congrArg (finiteFrickeCoordinates hA) hclasses).trans hNw)

end LowDimensionalTopology.Geometry.Teichmuller
