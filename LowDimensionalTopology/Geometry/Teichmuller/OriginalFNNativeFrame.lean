module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNNativeRegularity
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothFormInterior
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The native coordinate frame of the same original FN map

The fields are the public pullbacks of the constant coordinate directions by
the actual marked length and rescaled twist map. Their native derivative is
the corresponding unit, and their value retains the inverse Jacobian formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0,0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3*g-3) → ℂ
local notation "F" => (Fin (3*g-3) → ℝ) × (Fin (3*g-3) → ℝ)
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, F)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "c" => nativeWeilPeterssonCoordinateChart
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)

variable
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3*g-3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3*g-3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0,0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D₁ : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D₁)
      (j : Fin (3*g-3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m,rfl⟩⟩ j = D₁.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)

local notation "FN" => originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "K" => FN ∘ OpenPartialHomeomorph.symm c
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize

local notation "J" => Fin (3*g-3) ⊕ Fin (3*g-3)
local notation "b" => (fun a : J => match a with
  | Sum.inl j => (Pi.single j (1 : ℝ), (0 : Fin (3*g-3) → ℝ))
  | Sum.inr j => ((0 : Fin (3*g-3) → ℝ), Pi.single j (1 : ℝ)))

/-- The same original FN map pulls back the constant coordinate directions to
native smooth fields, with the genuine unit derivative and inverse Jacobian. -/
theorem exists_same_originalFN_native_coordinate_frame (hCompat : Compat) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ContMDiff RI FI ∞ FN ∧
    (∀ q : T, (mfderiv RI FI FN q).IsInvertible) ∧
    ∃ frame : J → FormInterior.SmoothVectorField RI (M := T),
      (∀ a q, frame a q = VectorField.mpullback RI FI FN
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b a)) q) ∧
      (∀ a q, frame a q = (D q).symm ((fderiv ℝ K (c q)).inverse (b a))) ∧
      (∀ a q, (NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q))
        (mfderiv RI FI FN q (frame a q)) = b a) := by
  let := C
  let : IsManifold RI ω T := realManifold
  have hreg := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  have hFN : FN = K ∘ c := by
    funext q
    change FN q = FN ((c).symm (c q))
    rw [(c).left_inv (mem_chart_source E q)]
  have hchain (q : T) : mvfderiv RI FN q =
      (fderiv ℝ K (c q)).comp (D q).toContinuousLinearMap := by
    have hsource : q ∈ (c).source := mem_chart_source E q
    have htarget : c q ∈ (c).target := (c).map_source hsource
    have hc := contMDiffOn_chart (I := RI) (n := ∞) (x := basePoint R)
    change ContMDiffOn RI RI ∞ c (c).source at hc
    have hcAt : MDifferentiableAt RI RI c q :=
      (hc.contMDiffAt ((c).open_source.mem_nhds hsource)).mdifferentiableAt (by simp)
    have hci := contMDiffOn_chart_symm (I := RI) (n := ∞) (x := basePoint R)
    change ContMDiffOn RI RI ∞ (c).symm (c).target at hci
    have hciAt : MDifferentiableAt RI RI (c).symm (c q) :=
      (hci.contMDiffAt ((c).open_target.mem_nhds htarget)).mdifferentiableAt (by simp)
    have hKm : MDifferentiableAt RI FI K (c q) :=
      ((hreg.1 ((c).symm (c q))).mdifferentiableAt (by simp)).comp (c q) hciAt
    have hD : (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c q)).toContinuousLinearMap.comp
        (mfderiv RI RI c q) = (D q).toContinuousLinearMap := by
      change mfderiv RI RI (extChartAt RI (basePoint R)) q = (D q).toContinuousLinearMap
      have htriv :
          (trivializationAt E (TangentSpace RI) (basePoint R)).continuousLinearMapAt ℝ q =
            (D q).toContinuousLinearMap :=
        nativeWeilPeterssonRealTangentCoordinateEquiv_trivialization
          R hp hg hgenus hΓ hfree hsmooth (basePoint R) q
      have ht := TangentBundle.continuousLinearMapAt_trivializationAt (I := RI)
        (show q ∈ (chartAt E (basePoint R)).source from mem_chart_source E q)
      exact ht.symm.trans htriv
    have h := mvfderiv_comp q hKm hcAt
    rw [mvfderiv_eq_fderiv (𝕜 := ℝ) (f := K) (x := c q)] at h
    simpa only [← hFN, ContinuousLinearMap.comp_assoc, hD] using h
  let B : J → ∀ y : F, TangentSpace FI y := fun a y =>
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b a)
  have hB (a : J) : ContMDiff FI (FI).tangent ∞
      (fun y : F => (⟨y, B a y⟩ : TangentBundle FI F)) := by
    exact contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hPB (a : J) : ContMDiff RI (RI).tangent ∞
      (fun q : T => (⟨q, VectorField.mpullback RI FI FN (B a) q⟩ : TangentBundle RI T)) := by
    exact (hB a).mpullback_vectorField hreg.1 hreg.2 (by simp)
  let frame : J → FormInterior.SmoothVectorField RI (M := T) :=
    fun a => ⟨VectorField.mpullback RI FI FN (B a), hPB a⟩
  have hvalue (a : J) (q : T) :
      frame a q = (D q).symm ((fderiv ℝ K (c q)).inverse (b a)) := by
    change (mfderiv RI FI FN q).inverse
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q)).symm (b a)) = _
    have h := congrArg (fun L : TangentSpace RI q →L[ℝ] F => L.inverse (b a)) (hchain q)
    simpa only [mvfderiv, ContinuousLinearMap.inverse_equiv_comp,
      ContinuousLinearMap.inverse_comp_equiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using h
  have hunit (a : J) (q : T) :
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q))
        (mfderiv RI FI FN q (frame a q)) = b a := by
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q))
      (mfderiv RI FI FN q ((mfderiv RI FI FN q).inverse
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q)).symm (b a)))) = b a
    rw [(hreg.2 q).self_apply_inverse]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q)).apply_symm_apply (b a)
  exact ⟨hreg.1, hreg.2, frame, (by intro a q; rfl), hvalue, hunit⟩

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
