module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNNativeSmoothInverse
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangentTrivialization
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Native regularity of the same original FN map

The supplied smooth local inverses give smoothness and an invertible actual
native differential for the literal original length and twist map. Only
existing chart, derivative and continuous-linear-map operations are used.
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

private theorem originalFN_normed_regular_and_isInvertible
    (hCompat : Compat) (z : E) (hz : z ∈ (c).target) :
    ContDiffAt ℝ ∞ K z ∧ (fderiv ℝ K z).IsInvertible := by
  let := C
  rcases hCompat z hz with ⟨f, hzf, _, hfK, hf, hfinv⟩
  have hfAt : ContDiffAt ℝ ∞ (f : E → F) z :=
    hf.contDiffAt (f.open_source.mem_nhds hzf)
  have hfinvAt : ContDiffAt ℝ ∞ (f.symm : F → E) (f z) :=
    hfinv.contDiffAt (f.open_target.mem_nhds (f.map_source hzf))
  have hKe : K =ᶠ[𝓝 z] (f : E → F) := by
    filter_upwards [f.open_source.mem_nhds hzf] with y hy
    exact (hfK y hy).symm
  have hleft : (f.symm ∘ f) =ᶠ[𝓝 z] (id : E → E) := by
    filter_upwards [f.open_source.mem_nhds hzf] with y hy
    exact f.left_inv hy
  have hright : ((f : E → F) ∘ f.symm) =ᶠ[𝓝 (f z)] (id : F → F) := by
    filter_upwards [f.open_target.mem_nhds (f.map_source hzf)] with y hy
    exact f.right_inv hy
  have hBA : (fderiv ℝ f.symm (f z)).comp (fderiv ℝ (f : E → F) z) =
      ContinuousLinearMap.id ℝ E := by
    have hc := fderiv_comp z (hfinvAt.differentiableAt (by simp))
      (hfAt.differentiableAt (by simp))
    exact hc.symm.trans (by simpa only [fderiv_id] using hleft.fderiv_eq (𝕜 := ℝ))
  have hfAt' : ContDiffAt ℝ ∞ (f : E → F) (f.symm (f z)) := by
    simpa only [f.left_inv hzf] using hfAt
  have hAB : (fderiv ℝ (f : E → F) z).comp (fderiv ℝ f.symm (f z)) =
      ContinuousLinearMap.id ℝ F := by
    have hc := fderiv_comp (f z) (hfAt'.differentiableAt (by simp))
      (hfinvAt.differentiableAt (by simp))
    rw [f.left_inv hzf] at hc
    exact hc.symm.trans (by simpa only [fderiv_id] using hright.fderiv_eq (𝕜 := ℝ))
  refine ⟨hfAt.congr_of_eventuallyEq hKe, ?_⟩
  rw [hKe.fderiv_eq (𝕜 := ℝ)]
  exact ContinuousLinearMap.IsInvertible.of_inverse hAB hBA

/-- The same FN map is smooth and its genuine native differential is
invertible at every original marked point under the supplied local inverses. -/
theorem sameOriginalFN_native_regular_and_isInvertible (hCompat : Compat) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ContMDiff RI FI ∞ FN ∧ ∀ q : T, (mfderiv RI FI FN q).IsInvertible := by
  let := C
  let : IsManifold RI ω T := realManifold
  have hchart (q : T) : ContMDiffAt RI RI ∞ c q := by
    change ContMDiffAt RI RI ∞ (extChartAt RI (basePoint R)) q
    exact contMDiffAt_extChartAt' (mem_chart_source E q)
  have hreg (q : T) : ContDiffAt ℝ ∞ K (c q) ∧ (fderiv ℝ K (c q)).IsInvertible :=
    originalFN_normed_regular_and_isInvertible R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat (c q)
      ((c).map_source (mem_chart_source E q))
  have hFN : FN = K ∘ c := by
    funext q
    change FN q = FN ((c).symm (c q))
    rw [(c).left_inv (mem_chart_source E q)]
  have hs : ContMDiff RI FI ∞ FN := by
    intro q
    rw [hFN]
    exact (hreg q).1.comp_contMDiffAt (hchart q)
  refine ⟨hs, ?_⟩
  intro q
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
  have hKm : MDifferentiableAt RI FI K (c q) :=
    (hreg q).1.contMDiffAt.mdifferentiableAt (by simp)
  have hchain : mvfderiv RI FN q = (fderiv ℝ K (c q)).comp (D q).toContinuousLinearMap := by
    have h := mvfderiv_comp q hKm ((hchart q).mdifferentiableAt (by simp))
    rw [mvfderiv_eq_fderiv (𝕜 := ℝ) (f := K) (x := c q)] at h
    simpa only [← hFN, ContinuousLinearMap.comp_assoc, hD] using h
  have hi : ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q)).toContinuousLinearMap.comp
      (mfderiv RI FI FN q)).IsInvertible := by
    change (mvfderiv RI FN q).IsInvertible
    rw [hchain]
    exact (hreg q).2.comp (ContinuousLinearMap.isInvertible_equiv (f := D q))
  exact (ContinuousLinearMap.isInvertible_equiv_comp
    (e := NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q))).mp hi

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
