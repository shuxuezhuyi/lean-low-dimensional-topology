module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNNativeFrame
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNTwistCurve
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothFormInterior
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The same inverse-coordinate FN curve with unit length parameter

The actual positive lengths and full real angle branch fix the pointwise
inverse-coordinate curve. Its rescaled native FN coordinates are the exact
unit affine line. Native regularity uses only the supplied same-map inverses.
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


local notation "Fpos" => (Fin (3*g-3) → Set.Ioi (0 : ℝ)) × (Fin (3*g-3) → ℝ)

/-- The existing original FN homeomorphism, used only as a pointwise equivalence. -/
def sameOriginalFNPointwiseEquiv : T ≃ Fpos := by
  let := nativeFrickeTopology hA
  let F₀ := originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
  exact ((nativeFrickeHomeomorph hA hAlt).trans
    ((originalFNRealCoordinateMap_isHomeomorph R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize).homeomorph F₀)).toEquiv

local notation "H" => sameOriginalFNPointwiseEquiv R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize

private def fnLengthRescale (v : Fpos) : F :=
  ((fun j => (v.1 j : ℝ)), fun j => (v.1 j : ℝ) / (2 * Real.pi) * v.2 j)

private theorem fnLengthRescale_injective : Function.Injective (fnLengthRescale (g := g)) := by
  intro a b hab
  have hl : a.1 = b.1 := by
    funext j
    exact Subtype.ext (congrFun (congrArg Prod.fst hab) j)
  apply Prod.ext hl
  funext j
  have ht := congrFun (congrArg Prod.snd hab) j
  change (a.1 j : ℝ) / (2 * Real.pi) * a.2 j =
    (b.1 j : ℝ) / (2 * Real.pi) * b.2 j at ht
  rw [← hl] at ht
  exact mul_left_cancel₀
    (div_ne_zero (ne_of_gt (a.1 j).property) (mul_ne_zero (by norm_num) Real.pi_ne_zero)) ht

private theorem nativeFN_eq_rescale_pointwise (q : T) :
    FN q = fnLengthRescale (H q) := by
  rw [originalFNNativeRescaledCoordinateMap_eq_original R hg hgenus hA hAlt D₀ Θ q]
  rfl

include hU φ hφ hΘ hRigid hRealize in
/-- Equality of all literal native lengths and rescaled twists fixes the same marked point. -/
theorem sameOriginalFN_native_injective : Function.Injective FN := by
  intro q r hqr
  apply (H).injective
  apply fnLengthRescale_injective
  simpa only [← nativeFN_eq_rescale_pointwise R hg hgenus hA hAlt D₀
    hU φ Θ hφ hΘ hRigid hRealize] using hqr

/-- The seam-side sign for the same inverse-coordinate twisting parameter. -/
def originalFNUnitSideSign (side : Fin 2) : ℝ := if side = 0 then 1 else -1

/-- The actual inverse-coordinate curve, parameterized by signed cuff length. -/
def sameOriginalFNUnitCurve (a : T) (j : Fin (3*g-3)) (side : Fin 2) (t : ℝ) : T :=
  (H).symm ((H a).1, Function.update (H a).2 j
    ((H a).2 j + originalFNUnitSideSign side * (2 * Real.pi / ((H a).1 j : ℝ)) * t))

local notation "sigma" => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize
local notation "unitTwist" => (fun j : Fin (3*g-3) =>
  ((0 : Fin (3*g-3) → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ)))

/-- The same unit curve starts at its original marked point and has its exact
affine native length/twist coordinate line for all real parameters. -/
theorem sameOriginalFN_unitCurve_native_coordinates
    (a : T) (j : Fin (3*g-3)) (side : Fin 2) :
    sigma a j side 0 = a ∧
      ∀ t : ℝ, FN (sigma a j side t) =
        FN a + (originalFNUnitSideSign side * t) • unitTwist j := by
  classical
  have horigin : sigma a j side 0 = a := by
    apply (H).injective
    simp only [sameOriginalFNUnitCurve, mul_zero, add_zero, (H).apply_symm_apply,
      Function.update_eq_self]
  refine ⟨horigin, ?_⟩
  intro t
  rw [nativeFN_eq_rescale_pointwise R hg hgenus hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize,
    nativeFN_eq_rescale_pointwise R hg hgenus hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize]
  rw [sameOriginalFNUnitCurve, (H).apply_symm_apply]
  apply Prod.ext
  · funext k
    simp only [fnLengthRescale, Prod.fst_add, Prod.smul_fst,
      smul_zero, add_zero]
  · funext k
    by_cases hkj : k = j
    · subst k
      simp only [fnLengthRescale, Function.update_self, Prod.snd_add, Prod.smul_snd,
        Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      field_simp [ne_of_gt ((H a).1 j).property, Real.pi_ne_zero]
    · simp only [fnLengthRescale, Function.update_of_ne hkj, Prod.snd_add,
        Prod.smul_snd, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hkj,
        smul_eq_mul, mul_zero, add_zero]

/-- The same literal unit curve is natively smooth and its actual native
velocity is the signed pullback of the unit twist-coordinate direction. -/
theorem sameOriginalFN_unitCurve_native_twistDerivative (hCompat : Compat) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (a : T) (j : Fin (3*g-3)) (side : Fin 2),
      sigma a j side 0 = a ∧
      (∀ t : ℝ, FN (sigma a j side t) =
        FN a + (originalFNUnitSideSign side * t) • unitTwist j) ∧
      ContMDiffAt 𝓘(ℝ) RI ∞ (sigma a j side) 0 ∧
      HasDerivAt (fun t : ℝ => c (sigma a j side t))
        (D a (originalFNUnitSideSign side • VectorField.mpullback RI FI FN
          (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) a)) 0 := by
  classical
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  intro a j side
  have hcoord := sameOriginalFN_unitCurve_native_coordinates R hg hgenus hA hAlt D₀
    hU φ Θ hφ hΘ hRigid hRealize a j side
  let sign := originalFNUnitSideSign side
  let line : ℝ → F := fun t => FN a + (sign * t) • unitTwist j
  have hline : ContDiff ℝ ∞ line :=
    contDiff_const.add ((contDiff_const.mul contDiff_id).smul contDiff_const)
  have hline0 : line 0 = FN a := by simp only [line, mul_zero, zero_smul, add_zero]
  have hca : c a ∈ (c).target := (c).map_source (mem_chart_source E a)
  rcases hCompat (c a) hca with ⟨f, hfa, hsource, hfK, hf, hfinv⟩
  have hleft : (c).symm (c a) = a := (c).left_inv (mem_chart_source E a)
  have hfvalue : f (c a) = FN a := by
    rw [hfK (c a) hfa]
    change FN ((c).symm (c a)) = FN a
    rw [hleft]
  have hlineTarget : line 0 ∈ f.target := by
    rw [hline0, ← hfvalue]
    exact f.map_source hfa
  have hnearTarget : ∀ᶠ t in 𝓝 (0 : ℝ), line t ∈ f.target :=
    hline.continuous.continuousAt (f.open_target.mem_nhds hlineTarget)
  have hinv0 : f.symm (line 0) = c a := by
    rw [hline0, ← hfvalue]
    exact f.left_inv hfa
  have hnear : sigma a j side =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => (c).symm (f.symm (line t))) := by
    filter_upwards [hnearTarget] with t ht
    apply sameOriginalFN_native_injective R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize
    rw [hcoord.2 t]
    change line t = K (f.symm (line t))
    rw [← hfK (f.symm (line t)) (f.map_target ht), f.right_inv ht]
  have hmodel : ContDiffAt ℝ ∞ (fun t : ℝ => f.symm (line t)) 0 :=
    (hfinv.contDiffAt (f.open_target.mem_nhds hlineTarget)).comp 0 hline.contDiffAt
  have hcinv : ContMDiffAt RI RI ∞ (c).symm (c a) := by
    have h := contMDiffOn_chart_symm (I := RI) (n := ∞) (x := basePoint R)
    change ContMDiffOn RI RI ∞ (c).symm (c).target at h
    exact h.contMDiffAt ((c).open_target.mem_nhds hca)
  have hcinv0 : ContMDiffAt RI RI ∞ (c).symm (f.symm (line 0)) := by
    rw [hinv0]
    exact hcinv
  have hsigma : ContMDiffAt 𝓘(ℝ) RI ∞ (sigma a j side) 0 :=
    (hcinv0.comp 0 hmodel.contMDiffAt).congr_of_eventuallyEq hnear
  have hc (q : T) : ContMDiffAt RI RI ∞ c q := by
    change ContMDiffAt RI RI ∞ (extChartAt RI (basePoint R)) q
    exact contMDiffAt_extChartAt' (mem_chart_source E q)
  have hsc : ContDiffAt ℝ ∞ (fun t : ℝ => c (sigma a j side t)) 0 :=
    ((hc (sigma a j side 0)).comp 0 hsigma).contDiffAt
  have hKnear : K =ᶠ[𝓝 (c a)] (f : E → F) := by
    filter_upwards [f.open_source.mem_nhds hfa] with y hy
    exact (hfK y hy).symm
  have hK : ContDiffAt ℝ ∞ K (c a) :=
    (hf.contDiffAt (f.open_source.mem_nhds hfa)).congr_of_eventuallyEq hKnear
  rcases exists_same_originalFN_native_coordinate_frame R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat with
    ⟨hFN, hInvertible, frame, hframe, hinverse, hunit⟩
  have hFN_eq : FN = K ∘ c := by
    funext q
    change FN q = FN ((c).symm (c q))
    rw [(c).left_inv (mem_chart_source E q)]
  have hD : (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c a)).toContinuousLinearMap.comp
      (mfderiv RI RI c a) = (D a).toContinuousLinearMap := by
    change mfderiv RI RI (extChartAt RI (basePoint R)) a = (D a).toContinuousLinearMap
    have htriv :
        (trivializationAt E (TangentSpace RI) (basePoint R)).continuousLinearMapAt ℝ a =
          (D a).toContinuousLinearMap :=
      nativeWeilPeterssonRealTangentCoordinateEquiv_trivialization
        R hp hg hgenus hΓ hfree hsmooth (basePoint R) a
    have ht := TangentBundle.continuousLinearMapAt_trivializationAt (I := RI)
      (show a ∈ (chartAt E (basePoint R)).source from mem_chart_source E a)
    exact ht.symm.trans htriv
  have hchain : mvfderiv RI FN a =
      (fderiv ℝ K (c a)).comp (D a).toContinuousLinearMap := by
    have h := mvfderiv_comp a (hK.contMDiffAt.mdifferentiableAt (by simp))
      ((hc a).mdifferentiableAt (by simp))
    rw [mvfderiv_eq_fderiv (𝕜 := ℝ) (f := K) (x := c a)] at h
    simpa only [← hFN_eq, ContinuousLinearMap.comp_assoc, hD] using h
  let Xj : TangentSpace RI a := VectorField.mpullback RI FI FN
    (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) a
  have hXunit : mvfderiv RI FN a Xj = unitTwist j := by
    have h := hunit (Sum.inr j) a
    rw [hframe (Sum.inr j) a] at h
    exact h
  let v := deriv (fun t : ℝ => c (sigma a j side t)) 0
  have hKcurve : HasFDerivAt K (fderiv ℝ K (c a)) (c (sigma a j side 0)) := by
    rw [hcoord.1]
    exact (hK.differentiableAt (by simp)).hasFDerivAt
  have hNcurve := hKcurve.comp_hasDerivAt (0 : ℝ)
    (hsc.differentiableAt (by simp)).hasDerivAt
  have heqcurve : K ∘ (fun t : ℝ => c (sigma a j side t)) = line := by
    funext t
    change K (c (sigma a j side t)) = line t
    exact (congrFun hFN_eq (sigma a j side t)).symm.trans (hcoord.2 t)
  rw [heqcurve] at hNcurve
  have hlineDeriv : HasDerivAt line (sign • unitTwist j) 0 := by
    simpa only [line, one_mul, mul_one, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).const_mul sign).smul_const (unitTwist j)).const_add (FN a)
  have hNv : fderiv ℝ K (c a) v = sign • unitTwist j := hNcurve.unique hlineDeriv
  refine ⟨hcoord.1, hcoord.2, hsigma, ?_⟩
  apply (hsc.differentiableAt (by simp)).hasDerivAt.congr_deriv
  change v = D a (sign • Xj)
  apply (D a).symm.injective
  rw [(D a).symm_apply_apply]
  apply (hInvertible a).injective
  apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN a)).injective
  change mvfderiv RI FN a ((D a).symm v) = mvfderiv RI FN a (sign • Xj)
  calc
    mvfderiv RI FN a ((D a).symm v) = fderiv ℝ K (c a) v := by
      rw [hchain]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
    _ = sign • unitTwist j := hNv
    _ = mvfderiv RI FN a (sign • Xj) := by rw [map_smul, hXunit]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
