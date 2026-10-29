module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNReferenceTwistShear
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookUnitCurve
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangentTrivialization
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceWeilPeterssonCoordinates
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Actual book FN covector shear under the fixed deformed reference map

The supplied original book-left labels are retained on the actual deformed
reference. The derived all-point real twist values are differentiated in
the two actual native Bers charts. Every original tangent is transported
by the actual reference-coordinate derivative and the actual D/DY maps.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami TeichmullerSpace
open NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0}) (ν : Ball Γ)

local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "eν" => deformedTargetMarking R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "Aν" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν
local notation "hP" => canonicalHandleGroupPresentation g
local notation "T" => TeichmullerSpace R
local notation "T₁" => TeichmullerSpace Y
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "C₁" => canonicalComplexChartedSpace Y hg hY hP hΔ hfY hpY hsmooth

variable
    (F : SmoothSurfaceEquiv R.toRiemannSurface
      (deformedNativeSurface R hgenus hΓ hp ν).toRiemannSurface)
    (hF : PreservesComplexOrientation R.toRiemannAtlas
      (deformedNativeSurface R hgenus hΓ hp ν).toRiemannAtlas F.toHomeomorph)
    (hmark : ContinuousMap.Homotopic (_root_.toContinuousMap F.toHomeomorph)
      (_root_.toContinuousMap (deformedTargetMarking R hgenus hΓ hp ν)))

local notation "mν" =>
  (MarkedRiemannSurface.mk (R := R)
    (carrier := LiZhongQC.ClosedRS.carrier (deformedTargetSource R hgenus hΓ hp ν))
    (topology := LiZhongQC.ClosedRS.topologicalSpace (deformedTargetSource R hgenus hΓ hp ν)) (surface := Y)
    (marking := F)
    (orientation_preserving := hF) : MarkedRiemannSurface R)

variable {e : X ≃ₜ PolygonQuotient g}
    {e₁ : (deformedTargetSource R hgenus hΓ hp ν).carrier ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (D₀ : OriginalFNRealization M inc)
    {N : HyperbolicSurfaceModel (deformedNativeSurface R hgenus hΓ hp ν).toRiemannSurface}
    (D₁ : OriginalFNRealization N inc)
    (t₀₁ : OriginalFNMarkedTransport (R := R) (M := M) (inc := inc) D₀
      (MarkedRiemannSurface.mk (R := R)
        (carrier := LiZhongQC.ClosedRS.carrier (deformedTargetSource R hgenus hΓ hp ν))
        (topology := LiZhongQC.ClosedRS.topologicalSpace (deformedTargetSource R hgenus hΓ hp ν))
        (surface := deformedNativeSurface R hgenus hΓ hp ν)
        (marking := F) (orientation_preserving := hF) : MarkedRiemannSurface R)
      (N := N) D₁)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hA₁ : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable
      (deformedNativeSurface R hgenus hΓ hp ν) hg e₁)
    (A₁ : OriginalFNGeometricFamily hA₁ D₁)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (φ₁ : C(nativeFrickeImage hA₁, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (Θ₁ : C(nativeFrickeImage hA₁, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (k : MarkedRiemannSurface.{0, 0} R)
      (P : HyperbolicSurfaceModel k.surface.toRiemannSurface)
      (D : OriginalFNRealization P inc) (_t : OriginalFNMarkedTransport D₀ k D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk k),
        ⟨TeichmullerSpace.mk k, rfl⟩⟩ j = D.phase j)
    (hφ₁ : ∀ (k : MarkedRiemannSurface.{0, 0} (deformedNativeSurface R hgenus hΓ hp ν))
      (P : HyperbolicSurfaceModel k.surface.toRiemannSurface)
      (D : OriginalFNRealization P inc) (_t : OriginalFNMarkedTransport D₁ k D)
      (j : Fin (3 * g - 3)),
      φ₁ ⟨finiteFrickeCoordinates hA₁ (TeichmullerSpace.mk k),
        ⟨TeichmullerSpace.mk k, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hΘ₁ : ∀ j, Circle.exp ∘ (fun t => Θ₁ t j) = fun t => φ₁ t j)

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "V" => (I → ℝ) × (I → ℝ)
local notation "RI" => 𝓘(ℝ, E)
local notation "VI" => 𝓘(ℝ, V)
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "BC₁" => bersCoordinates Y hg hY hP hΔ hfY hpY
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "DY" => nativeWeilPeterssonRealTangentCoordinateEquiv Y hpY hg hY hΔ hfY hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "chart₁" => nativeWeilPeterssonCoordinateChart Y hpY hg hY hΔ hfY hsmooth
local notation "f" => deformedReferenceWeilPeterssonCoordinateMap R hp hg hgenus hΓ ν

private theorem actualFN_chart_differential
    (G : T → V) (a : T) (hG : letI := C; MDifferentiableAt RI VI G a) :
    letI := C
    DifferentiableAt ℝ (G ∘ (chart (basePoint R)).symm) (BC a) ∧
      ∀ u : E, fderiv ℝ (G ∘ (chart (basePoint R)).symm) (BC a) u =
        mvfderiv RI G a ((D a).symm u) := by
  let := C
  let : IsManifold RI ω T := Topology.IsOpenEmbedding.isManifold_singleton
    («I» := RI) (n := ω)
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)
  let c := chart (basePoint R)
  have hs : a ∈ c.source := mem_chart_source E a
  have ht : BC a ∈ c.target := c.map_source hs
  have hleft : c.symm (BC a) = a := c.left_inv hs
  have hDsymm : (D a).symm.toContinuousLinearMap = mfderiv RI RI c.symm (BC a) := by
    have hcoord : (c : T → E) a = BC a :=
      congrFun (nativeWeilPeterssonCoordinateChart_coe
        R hp hg hgenus hΓ hfree hsmooth (basePoint R)) a
    rw [← hcoord]
    rw [← nativeWeilPeterssonRealTangentCoordinateEquiv_symmL
      R hp hg hgenus hΓ hfree hsmooth (basePoint R) a]
    have h := TangentBundle.symmL_trivializationAt («I» := RI)
      (x₀ := basePoint R) (x := a) hs
    simpa only [c, nativeWeilPeterssonCoordinateChart, extChartAt_coe_symm, extChartAt_coe,
      modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe, Function.comp_id,
      Function.id_comp, Set.range_id, mfderivWithin_univ] using h
  have hc : MDifferentiableAt RI RI c.symm (BC a) := by
    have h := contMDiffOn_chart_symm («I» := RI) (n := ∞) (x := basePoint R)
    change ContMDiffOn RI RI ∞ c.symm c.target at h
    exact (h.contMDiffAt (c.open_target.mem_nhds ht)).mdifferentiableAt (by simp)
  have hG' : MDifferentiableAt RI VI G (c.symm (BC a)) := by
    simpa only [hleft] using hG
  refine ⟨(hG'.comp (BC a) hc).differentiableAt, ?_⟩
  intro u
  have h := mvfderiv_comp_apply (BC a) hG' hc
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (BC a)).symm u)
  rw [mvfderiv_eq_fderiv] at h
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [hleft, ← hDsymm] at h
  exact h

private def actualFNReferenceShear (n : I → ℤ) : V →L[ℝ] V :=
  let P := ContinuousLinearMap.fst ℝ (I → ℝ) (I → ℝ)
  let Q := ContinuousLinearMap.snd ℝ (I → ℝ) (I → ℝ)
  let B : (I → ℝ) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi fun j =>
    (n j : ℝ) • (ContinuousLinearMap.proj j : (I → ℝ) →L[ℝ] ℝ)
  P.prod (Q + B.comp P)

variable
    (hAlt : ∀ k : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA k))
    (hAlt₁ : ∀ k : MarkedRiemannSurface.{0, 0}
      (deformedNativeSurface R hgenus hΓ hp ν),
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA₁ k))
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (hU₁ : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic
      (deformedNativeSurface R hgenus hΓ hp ν) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) hA₁ hAlt₁ D₁)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity R hg hgenus hA hAlt D₀ φ Θ)
    (hRigid₁ : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      (deformedNativeSurface R hgenus hΓ hp ν) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) hA₁ hAlt₁ D₁ φ₁ Θ₁)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize₁ : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      (deformedNativeSurface R hgenus hΓ hp ν) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) hA₁ hAlt₁ D₁ φ₁ Θ₁)
    (hCompat : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize)
    (hCompat₁ : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
      (deformedNativeSurface R hgenus hΓ hp ν)
      (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν)
      (And.left (deformedGroup_spec hΓ ν))
      (deformedNativeSurface_actsFreely R hgenus hΓ hp ν)
      hsmooth hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁)
    (hBook : Unproved.Teichmuller.OriginalFNBookLeftCopyTransport D₀)

local notation "left" => Classical.choose hBook
local notation "Nraw" => originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "Nraw₁" => originalFNNativeRescaledCoordinateMap Y hg hY hA₁ hAlt₁ D₁ Θ₁
local notation "Nbook" => originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ left
local notation "Nbook₁" => originalFNBookNativeCoordinateMap Y hg hY hA₁ hAlt₁ D₁ Θ₁ left

include hmark t₀₁ hCompat hCompat₁ in
/-- The actual fixed reference derivative has the derived integer covector
shear on the SAME geometrically specified book-left coordinates, for every
original point and original real tangent vector. -/
theorem exists_originalFN_deformed_reference_book_covector_shear :
    letI := C
    letI := C₁
    ∃ n : I → ℤ, ∀ (q : T) (v : TangentSpace RI q),
      (mvfderiv RI Nbook₁ (Aν q)
        ((DY (Aν q)).symm (fderiv ℝ f (BC q) (D q v)))).1 = (mvfderiv RI Nbook q v).1 ∧
      ∀ j, (mvfderiv RI Nbook₁ (Aν q)
        ((DY (Aν q)).symm (fderiv ℝ f (BC q) (D q v)))).2 j =
          (mvfderiv RI Nbook q v).2 j + (n j : ℝ) * (mvfderiv RI Nbook q v).1 j := by
  classical
  let := C
  let := C₁
  let : IsManifold RI ω T := Topology.IsOpenEmbedding.isManifold_singleton
    («I» := RI) (n := ω)
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)
  let : IsManifold RI ω T₁ := Topology.IsOpenEmbedding.isManifold_singleton
    («I» := RI) (n := ω)
    (canonicalBersCoordinates_isOpenEmbedding Y hg hY hP hΔ hfY hpY hsmooth)
  obtain ⟨n, hn⟩ := originalFN_deformed_reference_native_twist_shear
    R hp hg hgenus hΓ hfree hsmooth ν F hF hmark
      D₀ D₁ t₀₁ hA hA₁ (Classical.choose hU₁) φ φ₁ Θ Θ₁ hφ hφ₁ hΘ hΘ₁ hAlt hAlt₁
  let nb : I → ℤ := fun j => if left j = 0 then n j else -n j
  let S := actualFNReferenceShear (g := g) nb
  let Sign := originalFNBookCoordinateSignEquiv left
  have heq := originalFNBookNativeCoordinateMap_eq R hg hgenus hA hAlt D₀ Θ left
  have heq₁ := originalFNBookNativeCoordinateMap_eq Y hg hY hA₁ hAlt₁ D₁ Θ₁ left
  have hreg := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  have hreg₁ := sameOriginalFN_native_regular_and_isInvertible
    Y hpY hg hY hΔ hfY hsmooth hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ hCompat₁
  have hsmoothBook : ContMDiff RI VI ∞ Nbook := by
    rw [heq]
    exact Sign.toContinuousLinearMap.contMDiff.comp hreg.1
  have hsmoothBook₁ : ContMDiff RI VI ∞ Nbook₁ := by
    rw [heq₁]
    exact Sign.toContinuousLinearMap.contMDiff.comp hreg₁.1
  have hvalue (q : T) : Nbook₁ (Aν q) = S (Nbook q) := by
    rw [heq, heq₁]
    apply Prod.ext
    · exact (hn q).1
    · funext j
      change originalFNBookSideSign (left j) * (Nraw₁ (Aν q)).2 j =
        originalFNBookSideSign (left j) * (Nraw q).2 j + (nb j : ℝ) * (Nraw q).1 j
      rw [(hn q).2 j]
      by_cases h : left j = 0 <;> simp [nb, originalFNBookSideSign, h]; ring
  let c := chart (basePoint R)
  let c₁ := chart₁ (basePoint Y)
  let G := Nbook ∘ c.symm
  let G₁ := Nbook₁ ∘ c₁.symm
  have hchart (z : E) (hz : z ∈ c.target) : G₁ (f z) = S (G z) := by
    have hzq : BC (c.symm z) = z := c.right_inv hz
    have hfz : f z = BC₁ (Aν (c.symm z)) := by
      calc
        f z = f (BC (c.symm z)) := congrArg f hzq.symm
        _ = BC₁ (Aν (c.symm z)) :=
          deformedReferenceWeilPeterssonCoordinateMap_point R hp hg hgenus hΓ hfree ν (c.symm z)
    have hinv : c₁.symm (BC₁ (Aν (c.symm z))) = Aν (c.symm z) := by
      have hcoord₁ : (c₁ : T₁ → E) (Aν (c.symm z)) = BC₁ (Aν (c.symm z)) :=
        congrFun (nativeWeilPeterssonCoordinateChart_coe
          Y hpY hg hY hΔ hfY hsmooth (basePoint Y)) (Aν (c.symm z))
      rw [← hcoord₁]
      exact c₁.left_inv (mem_chart_source E (Aν (c.symm z)))
    change Nbook₁ (c₁.symm (f z)) = S (Nbook (c.symm z))
    rw [hfz, hinv]
    exact hvalue (c.symm z)
  refine ⟨nb, fun q v => ?_⟩
  have hx : BC q ∈ c.target := c.map_source (mem_chart_source E q)
  have hpoint : f (BC q) = BC₁ (Aν q) :=
    deformedReferenceWeilPeterssonCoordinateMap_point R hp hg hgenus hΓ hfree ν q
  have hdata := actualFN_chart_differential R hp hg hgenus hΓ hfree hsmooth
    Nbook q ((hsmoothBook q).mdifferentiableAt (by simp))
  have hdata₁ := actualFN_chart_differential Y hpY hg hY hΔ hfY hsmooth
    Nbook₁ (Aν q) ((hsmoothBook₁ (Aν q)).mdifferentiableAt (by simp))
  have hf : DifferentiableAt ℝ f (BC q) :=
    ((deformedReferenceWeilPeterssonCoordinateMap_analytic
      R hp hg hgenus hΓ hfree hsmooth ν).1 (BC q) hx).differentiableAt.restrictScalars ℝ
  have hG₁ : DifferentiableAt ℝ G₁ (f (BC q)) := by
    rw [hpoint]
    exact hdata₁.1
  have hnear : G₁ ∘ f =ᶠ[𝓝 (BC q)] (S : V → V) ∘ G := by
    filter_upwards [c.open_target.mem_nhds hx] with z hz
    exact hchart z hz
  have hfd := hnear.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp (BC q) hG₁ hf,
    fderiv_comp (BC q) S.differentiableAt hdata.1, S.hasFDerivAt.fderiv] at hfd
  have h := congrArg (fun L : E →L[ℝ] V => L (D q v)) hfd
  change fderiv ℝ G₁ (f (BC q)) (fderiv ℝ f (BC q) (D q v)) =
    S (fderiv ℝ G (BC q) (D q v)) at h
  rw [hpoint, hdata₁.2, hdata.2] at h
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  refine ⟨?_, fun j => ?_⟩
  · simpa [S, actualFNReferenceShear] using congrArg (fun z : V => z.1) h
  · simpa [S, actualFNReferenceShear] using congrArg (fun z : V => z.2 j) h

end LowDimensionalTopology.Geometry.Teichmuller
