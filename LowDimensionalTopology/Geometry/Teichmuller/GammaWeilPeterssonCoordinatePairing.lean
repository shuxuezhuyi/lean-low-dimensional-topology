module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonCorePullback
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRealTangentForm

/-! The same original WP pairing in actual group and native Bers coordinates. -/

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
local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ,E)
local notation "TG" => LiZhongQC.TeichGamma Γ
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "G" => gammaBersCoordinates R hg hgenus hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "gchart" => gammaWeilPeterssonCoordinateChart R hp hg hgenus hΓ
local notation "gcoord" => gammaWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ
local notation "nchart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "ncoord" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "HG" => gammaWeilPeterssonCore R hp hg hgenus hΓ hsmooth
local notation "HN" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local instance : Nonempty TG := ⟨LiZhongQC.TeichGamma.origin Γ⟩

/-- The one actual inverse-differential coordinate square needed for the WP values. -/
theorem gammaWeilPeterssonCoordinateEquiv_comp_inverseDifferential (a : TG) :
    letI := C; letI := mΓ; letI := CG
    (ncoord ((D).symm a)).toContinuousLinearMap.comp
      (mfderiv TI TI (D).symm a) = (gcoord a).toContinuousLinearMap := by
  let := C; let := mΓ; let := CG
  have hc : MDifferentiableAt TI TI BC ((D).symm a) :=
    ContMDiff.mdifferentiableAt (contMDiff_isOpenEmbedding (I := TI) (n := ω)
      (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth))
      (by decide)
  have hd : MDifferentiableAt TI TI (D).symm a :=
    (D).symm.contMDiff.mdifferentiableAt (by decide)
  apply ContinuousLinearMap.ext
  intro v
  have hn := nativeWeilPeterssonCoordinateEquiv_apply R hp hg hgenus hΓ hfree hsmooth
    ((D).symm a) (mfderiv TI TI (D).symm a v)
  have hgroup := gammaWeilPeterssonCoordinateEquiv_apply R hp hg hgenus hΓ a v
  have hccomp := mfderiv_comp_apply a hc hd v
  exact hn.trans ((congrArg (NormedSpace.fromTangentSpace (𝕜 := ℂ) (G a))
    hccomp.symm).trans hgroup.symm)

/-- The actual group and native chart targets are the same original Bers domain. -/
theorem gammaWeilPeterssonCoordinateChart_target_eq_native (a : TG) :
    letI := C; letI := mΓ; letI := CG
    (gchart a).target = (nchart ((D).symm a)).target := by
  let := C; let := mΓ; let := CG
  have hr : range G = range BC := by
    ext t
    constructor
    · rintro ⟨q, rfl⟩; exact ⟨(D).symm q, rfl⟩
    · rintro ⟨b, rfl⟩; exact ⟨D b, congrArg BC ((D).symm_apply_apply b)⟩
  change (Topology.IsOpenEmbedding.toOpenPartialHomeomorph G
      (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)).target =
    (Topology.IsOpenEmbedding.toOpenPartialHomeomorph BC
      (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)).target
  simpa only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hr

/-- Only on the genuine target, the two actual inverse chart points correspond. -/
theorem gammaWeilPeterssonCoordinateChart_symm_native (a : TG) (t : E) :
    letI := C; letI := mΓ; letI := CG
    t ∈ (gchart a).target →
      (D).symm ((gchart a).symm t) = (nchart ((D).symm a)).symm t := by
  let := C; let := mΓ; let := CG
  intro ht
  let nc := nchart ((D).symm a)
  have hq : (D).symm ((gchart a).symm t) ∈ nc.source :=
    mem_chart_source E ((D).symm ((gchart a).symm t))
  have hc : nc ((D).symm ((gchart a).symm t)) = t := (gchart a).right_inv ht
  exact (nc.left_inv hq).symm.trans (congrArg nc.symm hc)

/-- Both inverse coordinate frames evaluate the same original selected Hermitian form. -/
theorem gammaWeilPeterssonCoordinateInner_eq_native (a : TG) (v w : E) :
    letI := C; letI := mΓ; letI := CG
    (HG a).inner ((gcoord a).symm w) ((gcoord a).symm v) =
      (HN ((D).symm a)).inner
        ((ncoord ((D).symm a)).symm w) ((ncoord ((D).symm a)).symm v) := by
  let := C; let := mΓ; let := CG
  have hc := gammaWeilPeterssonCoordinateEquiv_comp_inverseDifferential
    R hp hg hgenus hΓ hsmooth a
  have hi (z : E) : mfderiv TI TI (D).symm a ((gcoord a).symm z) =
      (ncoord ((D).symm a)).symm z := by
    apply (ncoord ((D).symm a)).injective
    have hz := congrArg (fun A : TangentSpace TI a →L[ℂ] E => A ((gcoord a).symm z)) hc
    exact (hz.trans ((gcoord a).apply_symm_apply z)).trans
      ((ncoord ((D).symm a)).apply_symm_apply z).symm
  exact (gammaWeilPeterssonCore_inner_eq_nativeCore R hp hg hgenus hΓ hsmooth a
    ((gcoord a).symm v) ((gcoord a).symm w)).trans
      (congrArg₂ ((HN ((D).symm a)).inner) (hi w) (hi v))

/-- The literal group pairing has the English value of the existing native model form. -/
theorem gammaWeilPeterssonRealModelForm_coordinate (a : TG) (v w : E) :
    letI := C; letI := mΓ; letI := CG
    2 * ((HG a).inner ((gcoord a).symm w) ((gcoord a).symm v)).re =
      nativeWeilPeterssonRealModelForm R hp hg hgenus hΓ hfree hsmooth ((D).symm a) v w := by
  let := C; let := mΓ; let := CG
  calc
    _ = 2 * ((HN ((D).symm a)).inner
        ((ncoord ((D).symm a)).symm w) ((ncoord ((D).symm a)).symm v)).re :=
      congrArg (fun z : ℂ => 2 * z.re)
        (gammaWeilPeterssonCoordinateInner_eq_native R hp hg hgenus hΓ hsmooth a v w)
    _ = _ := (nativeWeilPeterssonRealModelForm_apply R hp hg hgenus hΓ hfree hsmooth
      ((D).symm a) v w).symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
