module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalLengthReferenceChange
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceWeilPeterssonCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangentTrivialization
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The actual marked length differential under the deformed reference change

The original and deformed scalar functions use the same full marked loop.
Their proved equality on marked targets and the actual analytic inverse
reference coordinates give regularity at the deformed origin. The chain
rule transports the genuine real covector by the actual reference derivative
in the existing finite Bers charts, without a WP or FN duality premise.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3 * g - 3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "c" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)

private theorem native_scalar_chart_data
    (l : T → ℝ) (a : T) (hl : letI := C; MDifferentiableAt RI 𝓘(ℝ) l a) :
    letI := C
    DifferentiableAt ℝ (l ∘ (c).symm) (c a) ∧
      ∀ w : E, fderiv ℝ (l ∘ (c).symm) (c a) w =
        mfderiv RI 𝓘(ℝ) l a ((D a).symm w) := by
  let := C
  let : IsManifold RI ω T := realManifold
  have hsource : a ∈ (c).source := mem_chart_source E a
  have htarget : c a ∈ (c).target := (c).map_source hsource
  have hleft : (c).symm (c a) = a := (c).left_inv hsource
  have hDsymm : (D a).symm.toContinuousLinearMap = mfderiv RI RI (c).symm (c a) := by
    rw [← nativeWeilPeterssonRealTangentCoordinateEquiv_symmL
      R hp hg hgenus hΓ hfree hsmooth (basePoint R) a]
    have h := TangentBundle.symmL_trivializationAt (I := RI)
      (x₀ := basePoint R) (x := a) hsource
    simpa only [nativeWeilPeterssonCoordinateChart, extChartAt_coe_symm, extChartAt_coe,
      modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe, Function.comp_id,
      Function.id_comp, Set.range_id, mfderivWithin_univ] using h
  have hsymm : MDifferentiableAt RI RI (c).symm (c a) := by
    have h := contMDiffOn_chart_symm (I := RI) (n := ∞) (x := basePoint R)
    change ContMDiffOn RI RI ∞ (c).symm (c).target at h
    exact (h.contMDiffAt ((c).open_target.mem_nhds htarget)).mdifferentiableAt (by simp)
  have hl' : MDifferentiableAt RI 𝓘(ℝ) l ((c).symm (c a)) := by
    simpa only [hleft] using hl
  refine ⟨(hl'.comp (c a) hsymm).differentiableAt, ?_⟩
  intro w
  have h := mvfderiv_comp_apply (c a) hl' hsymm
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (c a)).symm w)
  rw [mvfderiv_eq_fderiv (𝕜 := ℝ) (f := l ∘ (c).symm) (x := c a)] at h
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [hleft, ← hDsymm] at h
  exact h

private theorem native_scalar_mdiff_of_chart
    (l : T → ℝ) (a : T)
    (hl : DifferentiableAt ℝ (l ∘ (c).symm) (c a)) :
    letI := C
    MDifferentiableAt RI 𝓘(ℝ) l a := by
  let := C
  let : IsManifold RI ω T := realManifold
  have hc : MDifferentiableAt RI RI c a :=
    (mdifferentiable_chart (I := RI) (basePoint R)).mdifferentiableAt (mem_chart_source E a)
  have h := hl.mdifferentiableAt.comp a hc
  apply h.congr_of_eventuallyEq
  exact Eventually.of_forall fun q =>
    (congrArg l ((c).left_inv (show q ∈ (c).source from mem_chart_source E q))).symm

variable (ν : Ball Γ)

local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "hgY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "eY" => deformedTargetMarking R hgenus hΓ hp ν
local notation "CY" => canonicalComplexChartedSpace Y hg hgY hP hΔ hfY hpY hsmooth
local notation "BCY" => bersCoordinates Y hg hgY hP hΔ hfY hpY
local notation "cY" => nativeWeilPeterssonCoordinateChart Y hpY hg hgY hΔ hfY hsmooth (basePoint Y)
local notation "DY" => nativeWeilPeterssonRealTangentCoordinateEquiv Y hpY hg hgY hΔ hfY hsmooth
local notation "a" => coefficientProjectionBall R hg hgenus hP hΓ hfree hp ν
local notation "Aν" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν
local notation "f" => deformedReferenceWeilPeterssonCoordinateMap R hp hg hgenus hΓ ν
local notation "qInv" => deformedReferenceWeilPeterssonInverseCoordinateMap R hp hg hgenus hΓ ν

/-- Existing length regularity on the original surface gives regularity at
the actual deformed origin. Its real differential is transported by the
actual reference-coordinate derivative on every original tangent vector. -/
theorem marked_length_deformedReference_differential
    (α : LiZhongQC.Loop X)
    (hLength : letI := C; MDifferentiableAt RI 𝓘(ℝ)
      (markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α) a) :
    letI := C
    letI := CY
    let αY : LiZhongQC.Loop (deformedTargetSource R hgenus hΓ hp ν).carrier :=
      ⟨eY α.1, α.2.map (eY).continuous⟩
    let lY := markedGeodesicLength Y (Nat.succ_le_of_lt hg) hgY αY
    MDifferentiableAt RI 𝓘(ℝ) lY (basePoint Y) ∧
      ∀ v : TangentSpace RI a,
        mfderiv RI 𝓘(ℝ) lY (basePoint Y)
            ((DY (basePoint Y)).symm (fderiv ℝ f (BC a) (D a v))) =
          mfderiv RI 𝓘(ℝ)
            (markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α) a v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := (Y).toRiemannAtlas.toChartedSpace
  let := C
  let := CY
  let : IsManifold RI ω T := realManifold
  let : IsManifold RI ω (TeichmullerSpace Y) :=
    Topology.IsOpenEmbedding.isManifold_singleton (I := RI) (n := ω)
      (canonicalBersCoordinates_isOpenEmbedding Y hg hgY hP hΔ hfY hpY hsmooth)
  let αY : LiZhongQC.Loop (deformedTargetSource R hgenus hΓ hp ν).carrier :=
    ⟨eY α.1, α.2.map (eY).continuous⟩
  let l := markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α
  let lY := markedGeodesicLength Y (Nat.succ_le_of_lt hg) hgY αY
  let G : E → ℝ := l ∘ (c).symm
  let GY : E → ℝ := lY ∘ (cY).symm
  let x : E := BC a
  have hRdata := native_scalar_chart_data R hp hg hgenus hΓ hfree hsmooth l a hLength
  have hGR : DifferentiableAt ℝ G x := by
    simpa only [G, x, nativeWeilPeterssonCoordinateChart_coe] using hRdata.1
  have hx : x ∈ (c).target := (c).map_source (mem_chart_source E a)
  have hzero : (0 : E) ∈ (cY).target := by
    simpa only [nativeWeilPeterssonCoordinateChart_coe, bersCoordinates_basePoint] using
      (cY).map_source (mem_chart_source E (basePoint Y))
  have hmaps := deformedReferenceWeilPeterssonCoordinateMap_domains
    R hp hg hgenus hΓ hfree hsmooth ν
  have hana := deformedReferenceWeilPeterssonCoordinateMap_analytic
    R hp hg hgenus hΓ hfree hsmooth ν
  have hqzero : qInv (0 : E) = x := by
    simpa only [x, coefficientProjection_ball] using
      deformedReferenceWeilPeterssonInverseCoordinateMap_zero R hp hg hgenus hΓ hfree hsmooth ν
  have hcenter : f x = 0 := by
    simpa only [x, coefficientProjection_ball] using
      deformedReferenceWeilPeterssonCoordinateMap_center R hp hg hgenus hΓ hfree ν
  have hscalar (y : E) (hy : y ∈ (cY).target) : GY y = G (qInv y) := by
    have hq : qInv y ∈ (c).target := hmaps.2.1 hy
    have hAy : Aν ((c).symm (qInv y)) = (cY).symm y := by
      apply (canonicalBersCoordinates_isOpenEmbedding Y hg hgY hP hΔ hfY hpY hsmooth).injective
      calc
        BCY (Aν ((c).symm (qInv y))) = f (BC ((c).symm (qInv y))) :=
          (deformedReferenceWeilPeterssonCoordinateMap_point
            R hp hg hgenus hΓ hfree ν ((c).symm (qInv y))).symm
        _ = f (qInv y) := congrArg f ((c).right_inv hq)
        _ = y := hmaps.2.2.2 y hy
        _ = BCY ((cY).symm y) := ((cY).right_inv hy).symm
    have h := markedGeodesicLength_referenceChangeEquiv R Y hg hgenus hgY
      eY (deformedTargetMarking_nativeQC R hp hgenus hΓ ν) α ((c).symm (qInv y))
    change lY (Aν ((c).symm (qInv y))) = l ((c).symm (qInv y)) at h
    rw [hAy] at h
    exact h
  have hGRzero : DifferentiableAt ℝ G (qInv 0) := by rw [hqzero]; exact hGR
  have hGY : DifferentiableAt ℝ GY 0 := by
    have h := hGRzero.comp 0 ((hana.2 0 hzero).differentiableAt.restrictScalars ℝ)
    apply h.congr_of_eventuallyEq
    filter_upwards [(cY).open_target.mem_nhds hzero] with y hy
    exact hscalar y hy
  have hLengthY : MDifferentiableAt RI 𝓘(ℝ) lY (basePoint Y) :=
    native_scalar_mdiff_of_chart Y hpY hg hgY hΔ hfY hsmooth lY (basePoint Y) (by
      simpa only [nativeWeilPeterssonCoordinateChart_coe, bersCoordinates_basePoint] using hGY)
  have hYdata := native_scalar_chart_data Y hpY hg hgY hΔ hfY hsmooth lY (basePoint Y) hLengthY
  have hevent : (fun z : E => GY (f z)) =ᶠ[𝓝 x] G := by
    filter_upwards [(c).open_target.mem_nhds hx] with z hz
    exact (hscalar (f z) (hmaps.1 hz)).trans (congrArg G (hmaps.2.2.1 z hz))
  have hGYcenter : DifferentiableAt ℝ GY (f x) := by rw [hcenter]; exact hGY
  have hderiv := hevent.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp x hGYcenter ((hana.1 x hx).differentiableAt.restrictScalars ℝ),
    hcenter] at hderiv
  refine ⟨hLengthY, ?_⟩
  intro v
  have htarget :
      fderiv ℝ GY 0 (fderiv ℝ f x (D a v)) =
        (mfderiv RI 𝓘(ℝ) lY (basePoint Y)
          ((DY (basePoint Y)).symm (fderiv ℝ f x (D a v))) : ℝ) := by
    simpa only [GY, nativeWeilPeterssonCoordinateChart_coe, bersCoordinates_basePoint] using
      hYdata.2 (fderiv ℝ f x (D a v))
  have hchain : fderiv ℝ GY 0 (fderiv ℝ f x (D a v)) =
      fderiv ℝ G x (D a v) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun L : E →L[ℝ] ℝ => L (D a v)) hderiv
  have hsource : fderiv ℝ G x (D a v) = (mfderiv RI 𝓘(ℝ) l a v : ℝ) := by
    simpa only [G, x, nativeWeilPeterssonCoordinateChart_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hRdata.2 (D a v)
  exact htarget.symm.trans (hchain.trans hsource)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
