module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonFundamentalForm

/-!
# The actual native and group real WP forms under the same real differential

The unchanged normalized-lift equivalence is read in the actual real Bers
charts. The coordinate chain rule identifies its genuine real differential,
and the existing definition of the group two-form gives the full pullback.
No tangent operator, pairing or normalization premise is supplied.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "T" => TeichmullerSpace R
local notation "TG" => LiZhongQC.TeichGamma Γ
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "G" => gammaBersCoordinates R hg hgenus hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "gcoord" => gammaWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ
local notation "ncoord" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "nativeForm" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "groupForm" => gammaWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hsmooth
local instance : Nonempty TG := ⟨LiZhongQC.TeichGamma.origin Γ⟩

/-- The same normalized-lift map is smooth in both actual real Bers charts. -/
theorem canonicalGammaDiffeomorph_real_contMDiff_bothDirections :
    letI := C; letI := mΓ; letI := CG
    ContMDiff RI RI ω D ∧ ContMDiff RI RI ω (D).symm := by
  let := C; let := mΓ; let := CG
  have hBC := canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth
  have hG := gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp
  have hc : ContMDiff RI RI ω BC := contMDiff_isOpenEmbedding hBC
  have hgc : ContMDiff RI RI ω G := contMDiff_isOpenEmbedding hG
  constructor
  · have hcomp : ContMDiff RI RI ω (G ∘ D) := hc.congr (fun a => by
      change BC ((D).symm (D a)) = BC a
      rw [(D).symm_apply_apply])
    exact hcomp.of_comp_isOpenEmbedding hG
  · have hcomp : ContMDiff RI RI ω (BC ∘ (D).symm) := hgc
    exact hcomp.of_comp_isOpenEmbedding hBC

/-- The actual inverse real manifold differential gives the real coordinate square. -/
theorem gammaWeilPeterssonRealTangentCoordinateEquiv_comp_inverseDifferential (a : TG) :
    letI := C; letI := mΓ; letI := CG
    (ncoord ((D).symm a)).toContinuousLinearMap.comp
      (mfderiv RI RI (D).symm a) = (gcoord a).toContinuousLinearMap := by
  let := C; let := mΓ; let := CG
  have hc : MDifferentiableAt RI RI BC ((D).symm a) :=
    ContMDiff.mdifferentiableAt (contMDiff_isOpenEmbedding (I := RI) (n := ω)
      (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth))
      (by decide)
  have hd : MDifferentiableAt RI RI (D).symm a :=
    (canonicalGammaDiffeomorph_real_contMDiff_bothDirections
      R hp hg hgenus hΓ hsmooth).2.mdifferentiableAt (by decide)
  apply ContinuousLinearMap.ext
  intro v
  have hn := nativeWeilPeterssonRealTangentCoordinateEquiv_apply
    R hp hg hgenus hΓ hfree hsmooth ((D).symm a) (mfderiv RI RI (D).symm a v)
  have hgroup := gammaWeilPeterssonRealTangentCoordinateEquiv_apply R hp hg hgenus hΓ a v
  have hcomp := mfderiv_comp_apply a hc hd v
  exact hn.trans ((congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (G a))
    hcomp.symm).trans hgroup.symm)

/-- The full original real WP two-form is pulled back by that same actual real differential. -/
theorem gammaWeilPeterssonRealFundamentalForm_eq_native_pullback (a : TG) :
    letI := C; letI := mΓ; letI := CG
    (nativeForm ((D).symm a)).compContinuousLinearMap (mfderiv RI RI (D).symm a) =
      groupForm a := by
  let := C; let := mΓ; let := CG
  have hc := gammaWeilPeterssonRealTangentCoordinateEquiv_comp_inverseDifferential
    R hp hg hgenus hΓ hsmooth a
  have hmap (v : TangentSpace RI a) :
      mfderiv RI RI (D).symm a v = (ncoord ((D).symm a)).symm (gcoord a v) := by
    apply (ncoord ((D).symm a)).injective
    have hv := congrArg (fun A : TangentSpace RI a →L[ℝ] E => A v) hc
    exact hv.trans ((ncoord ((D).symm a)).apply_symm_apply (gcoord a v)).symm
  apply ContinuousAlternatingMap.ext
  intro v
  change nativeForm ((D).symm a) (fun i => mfderiv RI RI (D).symm a (v i)) =
    nativeForm ((D).symm a) (fun i => (ncoord ((D).symm a)).symm (gcoord a (v i)))
  exact congrArg (nativeForm ((D).symm a)) (funext fun i => hmap (v i))

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
