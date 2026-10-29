module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNUnitNativeTwist
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalWeilPeterssonFormCartan
public import Mathlib.Tactic.Abel

/-!
# The actual signed unit FN family in the native atlas

The same inverse-coordinate curves form a jointly smooth family with their
literal signed pullback field as generator. The original WP pullback-time
Lie derivative and its given Cartan identity use this particular family.
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
local notation "TI" => ModelWithCorners.prod 𝓘(ℝ) RI
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "c" => nativeWeilPeterssonCoordinateChart
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
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
local notation "sigma" => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize
local notation "unitTwist" => (fun j : Fin (3*g-3) =>
  ((0 : Fin (3*g-3) → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ)))

/-- The actual signed unit family has its exact additive parameter law. -/
theorem sameOriginalFN_unitCurve_add
    (a : T) (j : Fin (3*g-3)) (side : Fin 2) (s t : ℝ) :
    sigma a j side (s + t) = sigma (sigma a j side t) j side s := by
  apply sameOriginalFN_native_injective R hg hgenus hA hAlt D₀
    hU φ Θ hφ hΘ hRigid hRealize
  rw [(sameOriginalFN_unitCurve_native_coordinates R hg hgenus hA hAlt D₀
    hU φ Θ hφ hΘ hRigid hRealize a j side).2 (s + t),
    (sameOriginalFN_unitCurve_native_coordinates R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize (sigma a j side t) j side).2 s,
    (sameOriginalFN_unitCurve_native_coordinates R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize a j side).2 t]
  simp only [mul_add, add_smul]
  abel

/-- The same-map inverse germs make this particular family jointly smooth. -/
theorem sameOriginalFN_unitCurve_jointSmooth (hCompat : Compat)
    (j : Fin (3*g-3)) (side : Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ContMDiff TI RI ∞ (fun z : ℝ × T => sigma z.2 j side z.1) := by
  let := C
  let : IsManifold RI ω T := realManifold
  have hreg := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  let line : ℝ × T → F := fun z =>
    FN z.2 + (originalFNUnitSideSign side * z.1) • unitTwist j
  have hline : ContMDiff TI FI ∞ line :=
    (hreg.1.comp contMDiff_snd).add
      ((contMDiff_const.mul contMDiff_fst).smul contMDiff_const)
  intro z
  let q := sigma z.2 j side z.1
  have hca : c q ∈ (c).target := (c).map_source (mem_chart_source E q)
  rcases hCompat (c q) hca with ⟨f, hfa, hsource, hfK, hf, hfinv⟩
  have hfvalue : f (c q) = FN q := by
    rw [hfK (c q) hfa]
    change FN ((c).symm (c q)) = FN q
    rw [(c).left_inv (mem_chart_source E q)]
  have hlineValue : line z = FN q :=
    ((sameOriginalFN_unitCurve_native_coordinates R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize z.2 j side).2 z.1).symm
  have hlineTarget : line z ∈ f.target := by
    rw [hlineValue, ← hfvalue]
    exact f.map_source hfa
  have hnearTarget : ∀ᶠ w in 𝓝 z, line w ∈ f.target :=
    hline.continuous.continuousAt (f.open_target.mem_nhds hlineTarget)
  have hinv : f.symm (line z) = c q := by
    rw [hlineValue, ← hfvalue]
    exact f.left_inv hfa
  have hnear : (fun w : ℝ × T => sigma w.2 j side w.1) =ᶠ[𝓝 z]
      (fun w : ℝ × T => (c).symm (f.symm (line w))) := by
    filter_upwards [hnearTarget] with w hw
    apply sameOriginalFN_native_injective R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize
    rw [(sameOriginalFN_unitCurve_native_coordinates R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize w.2 j side).2 w.1]
    change line w = K (f.symm (line w))
    rw [← hfK (f.symm (line w)) (f.map_target hw), f.right_inv hw]
  have hmodel : ContMDiffAt TI RI ∞ (fun w : ℝ × T => f.symm (line w)) z :=
    (hfinv.contDiffAt (f.open_target.mem_nhds hlineTarget)).comp_contMDiffAt (hline z)
  have hcinv : ContMDiffAt RI RI ∞ (c).symm (f.symm (line z)) := by
    rw [hinv]
    have h := contMDiffOn_chart_symm (I := RI) (n := ∞) (x := basePoint R)
    change ContMDiffOn RI RI ∞ (c).symm (c).target at h
    exact h.contMDiffAt ((c).open_target.mem_nhds hca)
  exact (hcinv.comp z hmodel).congr_of_eventuallyEq hnear

/-- The native field is the signed literal pullback of the raw unit twist. -/
def sameOriginalFNSignedTwistField (hCompat : Compat)
    (j : Fin (3*g-3)) (side : Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    FormInterior.SmoothVectorField RI (M := T) := by
  let := C
  let : IsManifold RI ω T := realManifold
  have hreg := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  let B : ∀ y : F, TangentSpace FI y :=
    fun y => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)
  have hB : ContMDiff FI (FI).tangent ∞
      (fun y : F => (⟨y, B y⟩ : TangentBundle FI F)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hPB : ContMDiff RI (RI).tangent ∞
      (fun q : T => (⟨q, VectorField.mpullback RI FI FN B q⟩ : TangentBundle RI T)) :=
    hB.mpullback_vectorField hreg.1 hreg.2 (by simp)
  exact originalFNUnitSideSign side •
    (⟨VectorField.mpullback RI FI FN B, hPB⟩ : FormInterior.SmoothVectorField RI (M := T))

local notation "W" => sameOriginalFNSignedTwistField R hp hg hgenus hΓ hfree hsmooth
  hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize

private theorem sameOriginalFNSignedTwistField_coordinate (hCompat : Compat)
    (j : Fin (3*g-3)) (side : Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ q : T, mvfderiv RI FN q (W hCompat j side q) =
      originalFNUnitSideSign side • unitTwist j := by
  let := C
  let : IsManifold RI ω T := realManifold
  have hreg := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  intro q
  have hW : W hCompat j side q = originalFNUnitSideSign side •
      VectorField.mpullback RI FI FN
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) q := by
    simp only [sameOriginalFNSignedTwistField, ContMDiffSection.coe_smul,
      ContMDiffSection.coeFn_mk, Pi.smul_apply]
  rw [hW, map_smul]
  congr 1
  change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q))
    ((mfderiv RI FI FN q) ((mfderiv RI FI FN q).inverse
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q)).symm (unitTwist j)))) = unitTwist j
  rw [(hreg.2 q).self_apply_inverse, ContinuousLinearEquiv.apply_symm_apply]

set_option maxHeartbeats 800000 in
private theorem sameOriginalFN_unitCurve_native_coordinate_velocity (hCompat : Compat)
    (j : Fin (3*g-3)) (side : Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (t : ℝ) (a : T),
      mvfderiv RI FN (sigma a j side t)
        (mfderiv 𝓘(ℝ) RI (sigma a j side) t
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1)) =
            originalFNUnitSideSign side • unitTwist j := by
  let := C
  let : IsManifold RI ω T := realManifold
  have hreg := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  have hjoint := sameOriginalFN_unitCurve_jointSmooth R hp hg hgenus hΓ hfree hsmooth
    hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat j side
  intro t a
  have hcurve : ContMDiff 𝓘(ℝ) RI ∞ (sigma a j side) := by
    simpa only [Function.comp_def] using
      (hjoint.comp (I := 𝓘(ℝ)) (I' := TI) (I'' := RI)
        (f := fun s : ℝ => (s, a))
        ((contMDiff_id (I := 𝓘(ℝ)) (M := ℝ) (n := ∞)).prodMk
          (show ContMDiff 𝓘(ℝ) RI ∞ (fun _ : ℝ => a) from
            contMDiff_const)))
  have hNcurve : HasDerivAt (FN ∘ sigma a j side)
      (originalFNUnitSideSign side • unitTwist j) t := by
    have heq : FN ∘ sigma a j side = (fun s : ℝ =>
        FN a + (originalFNUnitSideSign side * s) • unitTwist j) :=
      funext (sameOriginalFN_unitCurve_native_coordinates R hg hgenus hA hAlt D₀
        hU φ Θ hφ hΘ hRigid hRealize a j side).2
    rw [heq]
    simpa only [one_mul, mul_one, id_eq] using
      (((hasDerivAt_id t).const_mul (originalFNUnitSideSign side)).smul_const
        (unitTwist j)).const_add (FN a)
  let q : T := sigma a j side t
  let v : TangentSpace RI q := mfderiv 𝓘(ℝ) RI (sigma a j side) t
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1)
  calc
    mvfderiv RI FN q v = mvfderiv 𝓘(ℝ) (FN ∘ sigma a j side) t
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1) :=
      (mvfderiv_comp_apply (I := RI) (I' := 𝓘(ℝ))
        (f := sigma a j side) (g := FN) t
        ((hreg.1 q).mdifferentiableAt (by simp))
        ((hcurve t).mdifferentiableAt (by simp))
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1)).symm
    _ = originalFNUnitSideSign side • unitTwist j := by
      rw [mvfderiv_eq_fderiv]
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply,
        fderiv_apply_one_eq_deriv] using hNcurve.deriv

/-- The actual time derivative at every parameter is the same signed field. -/
theorem sameOriginalFN_unitCurve_native_generator (hCompat : Compat)
    (j : Fin (3*g-3)) (side : Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (t : ℝ) (a : T),
      mfderiv 𝓘(ℝ) RI (sigma a j side) t
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1) =
          W hCompat j side (sigma a j side t) := by
  let := C
  let : IsManifold RI ω T := realManifold
  have hreg := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  intro t a
  let q : T := sigma a j side t
  let v : TangentSpace RI q := mfderiv 𝓘(ℝ) RI (sigma a j side) t
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1)
  let w : TangentSpace RI q := W hCompat j side q
  have hv : mvfderiv RI FN q v = originalFNUnitSideSign side • unitTwist j :=
    sameOriginalFN_unitCurve_native_coordinate_velocity R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat j side t a
  have hw : mvfderiv RI FN q w = originalFNUnitSideSign side • unitTwist j :=
    sameOriginalFNSignedTwistField_coordinate R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat j side q
  have hcoordinates : mvfderiv RI FN q v = mvfderiv RI FN q w := hv.trans hw.symm
  have htangent : mfderiv RI FI FN q v = mfderiv RI FI FN q w :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q)).injective hcoordinates
  exact (hreg.2 q).injective htangent

/-- This exact family supplies all the inputs of the original local-flow interface. -/
theorem sameOriginalFN_unitCurve_localFlowData (hCompat : Compat)
    (j : Fin (3*g-3)) (side : Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    let Φ : ℝ → T → T := fun t a => sigma a j side t
    (∀ r ∈ (⊤ : TopologicalSpace.Opens T), Φ 0 r = r) ∧
    (∀ s ∈ Ioo (-1 : ℝ) 1, ∀ t ∈ Ioo (-1 : ℝ) 1,
      ∀ r ∈ (⊤ : TopologicalSpace.Opens T), s + t ∈ Ioo (-1 : ℝ) 1 →
        Φ t r ∈ (⊤ : TopologicalSpace.Opens T) → Φ (s + t) r = Φ s (Φ t r)) ∧
    ContMDiffOn TI RI ∞ (fun z : ℝ × T => Φ z.1 z.2)
      (Ioo (-1 : ℝ) 1 ×ˢ ((⊤ : TopologicalSpace.Opens T) : Set T)) ∧
    (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ r ∈ (⊤ : TopologicalSpace.Opens T),
      mfderiv 𝓘(ℝ) RI (fun s : ℝ => Φ s r) t
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1) = W hCompat j side (Φ t r)) := by
  let := C
  let : IsManifold RI ω T := realManifold
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    exact (sameOriginalFN_unitCurve_native_coordinates R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize r j side).1
  · intro s hs t ht r hr hst htr
    exact sameOriginalFN_unitCurve_add R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize r j side s t
  · exact (sameOriginalFN_unitCurve_jointSmooth R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat j side).contMDiffOn
  · intro t ht r hr
    exact sameOriginalFN_unitCurve_native_generator R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat j side t r

/-- The original WP pullback-time derivative along this actual signed FN family. -/
def sameOriginalFNUnitWPLieDerivative (hCompat : Compat)
    (j : Fin (3*g-3)) (side : Fin 2) (q : T) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    TangentSpace RI q [⋀^Fin 2]→L[ℝ] ℝ := by
  let := C
  let : IsManifold RI ω T := realManifold
  have h := sameOriginalFN_unitCurve_localFlowData R hp hg hgenus hΓ hfree hsmooth
    hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat j side
  exact nativeWeilPeterssonFormLieDerivativeAlong R hp hg hgenus hΓ hfree hsmooth
    q ⊤ (by trivial) 1 (by norm_num) (fun t a => sigma a j side t)
      (W hCompat j side) h.1 h.2.1 h.2.2.1 h.2.2.2

/-- The existing Cartan evaluation identity applies to this exact family and field. -/
theorem sameOriginalFN_unitCurve_cartan_evaluation
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hCompat : Compat) (j : Fin (3*g-3)) (side : Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (Y Z : FormInterior.SmoothVectorField RI (M := T)),
    let h := sameOriginalFN_unitCurve_localFlowData R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat j side
    Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
      R hp hg hgenus hΓ hfree hsmooth hWP ⊤ 1 (by norm_num)
      (fun t a => sigma a j side t) (W hCompat j side) Y Z
      h.1 h.2.1 h.2.2.1 h.2.2.2 →
    ∀ q : T,
      sameOriginalFNUnitWPLieDerivative R hp hg hgenus hΓ hfree hsmooth
        hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat j side q ![Y q,Z q] =
      mvfderiv RI
        (fun r => nativeWeilPeterssonRealFundamentalForm
          R hp hg hgenus hΓ hfree hsmooth r ![Y r,Z r]) q (W hCompat j side q) -
        nativeWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hfree hsmooth q
          ![VectorField.mlieBracket RI (W hCompat j side) Y q,Z q] -
        nativeWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hfree hsmooth q
          ![Y q,VectorField.mlieBracket RI (W hCompat j side) Z q] := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro Y Z h hCartan q
  exact hCartan.2 q (by trivial)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
