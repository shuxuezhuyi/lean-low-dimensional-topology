module

public import LowDimensionalTopology.Geometry.Teichmuller.HarmonicPeterssonCore
public import LowDimensionalTopology.Unproved.Teichmuller.SamePointPeterssonIntegralNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.SourceFuchsianRegions
public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceGammaChange
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport NativePetersson
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

local notation "TI" => 𝓘(ℂ, Fin (3*g-3) → ℂ)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "βB" => coefficientProjectionBall R hg hgenus hP hΓ hfree hp
local notation "E" => gammaEquiv R hg hgenus hP hΓ hfree hp
local notation "Y" => deformedNativeSurface R hgenus hΓ hp
local notation "pY" => deformedTargetCover R hgenus hΓ hp
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree

/-- On every actual marked-surface tangent fibre the source integral gives a
positive Hermitian form, with the same value for every original coefficient and region. -/
theorem exists_nativeWeilPeterssonFamily
    (hnat : Unproved.Teichmuller.SamePointPeterssonIntegralNaturality R hp hg hgenus hΓ hfree) :
    letI := C
    ∃ H : ∀ a : TeichmullerSpace.{u,u} R, InnerProductSpace.Core ℂ (TangentSpace TI a),
      ∀ (ν : Ball Γ)
        (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
        (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
        (v w : TangentSpace TI (β ν.val)),
        (H (β ν.val)).inner w v = WeilPetersson.beltramiPairing F
          (TH ν P F hF hsmooth v).val.val (TH ν P F hF hsmooth w).val.val := by
  let := C
  choose P F hF using (fun ν : Ball Γ => exists_deformedHalfPlaneFundamentalRegion R hgenus hΓ hp ν)
  have hβ : ∀ a : TeichmullerSpace.{u,u} R, ∃ ν : Ball Γ, β ν.val = a := by
    intro a
    obtain ⟨ν, hν⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp a
    exact ⟨ν, (coefficientProjection_ball R hg hgenus hΓ hfree hp ν).trans hν⟩
  choose s hs using hβ
  let T (ν : Ball Γ) := TH ν (P ν) (F ν) (hF ν) hsmooth
  let A (a : TeichmullerSpace.{u,u} R) :=
    (canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth (hs a).symm).trans (T (s a))
  let H (a : TeichmullerSpace.{u,u} R) := pullbackHermitianCore
    (harmonicHermitianCore (Y (s a)) (P (s a)) (pY (s a)) (hpY (s a)) (F (s a)) (hF (s a))) (A a)
  refine ⟨H, ?_⟩
  intro ν P₀ F₀ hF₀ v w
  let a := β ν.val
  have hpoint : βB ν = βB (s a) :=
    (coefficientProjection_ball R hg hgenus hΓ hfree hp ν).symm.trans
      ((hs a).symm.trans (coefficientProjection_ball R hg hgenus hΓ hfree hp (s a)))
  let K := nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν (s a) hpoint
    P₀ F₀ hF₀ (P (s a)) (F (s a)) (hF (s a))
  have hv := nonzeroTangentHarmonicEquiv_natural R hp hg hgenus hΓ hfree hsmooth
    ν (s a) hpoint P₀ F₀ hF₀ (P (s a)) (F (s a)) (hF (s a)) v
  have hw := nonzeroTangentHarmonicEquiv_natural R hp hg hgenus hΓ hfree hsmooth
    ν (s a) hpoint P₀ F₀ hF₀ (P (s a)) (F (s a)) (hF (s a)) w
  change K (TH ν P₀ F₀ hF₀ hsmooth v) = A a v at hv
  change K (TH ν P₀ F₀ hF₀ hsmooth w) = A a w at hw
  change (harmonicHermitianCore (Y (s a)) (P (s a)) (pY (s a)) (hpY (s a))
    (F (s a)) (hF (s a))).inner (A a w) (A a v) = _
  rw [harmonicHermitianCore_inner, ← hv, ← hw]
  exact (hnat ν (s a) hpoint P₀ F₀ hF₀ (P (s a)) (F (s a)) (hF (s a))
    (TH ν P₀ F₀ hF₀ hsmooth v) (TH ν P₀ F₀ hF₀ hsmooth w)).symm

/-- The same normalized-lift equivalence is biholomorphic for the actual
canonical native atlas and the existing original group Bers atlas. -/
def canonicalGammaDiffeomorph :
    letI := C
    letI := mΓ
    letI := CG
    Diffeomorph TI TI (TeichmullerSpace.{u,u} R) (LiZhongQC.TeichGamma Γ) ω := by
  letI := C
  letI := mΓ
  letI := CG
  letI : Nonempty (LiZhongQC.TeichGamma Γ) := ⟨LiZhongQC.TeichGamma.origin Γ⟩
  let BC := bersCoordinates R hg hgenus hP hΓ hfree hp
  let G := gammaBersCoordinates R hg hgenus hΓ hfree hp
  let e := E
  have hBC := canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth
  have hG := gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp
  have hc : ContMDiff TI TI ω BC := contMDiff_isOpenEmbedding hBC
  have hgC : ContMDiff TI TI ω G := contMDiff_isOpenEmbedding hG
  refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · have hcomp : ContMDiff TI TI ω (G ∘ e) := hc.congr (fun a => by
      change BC (e.symm (e a)) = BC a
      rw [e.symm_apply_apply])
    exact hcomp.of_comp_isOpenEmbedding hG
  · have hcomp : ContMDiff TI TI ω (BC ∘ e.symm) := hgC
    exact hcomp.of_comp_isOpenEmbedding hBC

local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth

/-- Its value on each original coefficient is the literal original group class. -/
theorem canonicalGammaDiffeomorph_projection (ν : Ball Γ) :
    letI := C
    letI := mΓ
    letI := CG
    D (β ν.val) = gammaCoefficientProjectionBall ν := by
  let := C
  let := mΓ
  let := CG
  rw [coefficientProjection_ball]
  change E ((E).symm (gammaCoefficientProjectionBall ν)) = _
  exact (E).apply_symm_apply _

/-- The original T(Gamma) tangent family has the source integral in every
coefficient and region. Transport is the actual inverse differential of the
same normalized-lift biholomorphism, on all original group tangent vectors. -/
theorem exists_gammaWeilPeterssonFamily
    (hnat : Unproved.Teichmuller.SamePointPeterssonIntegralNaturality R hp hg hgenus hΓ hfree) :
    letI := C
    letI := mΓ
    letI := CG
    ∃ H : ∀ q : LiZhongQC.TeichGamma Γ, InnerProductSpace.Core ℂ (TangentSpace TI q),
      ∀ (ν : Ball Γ)
        (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
        (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
        (v w : TangentSpace TI (D (β ν.val))),
        let J := canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
          ((D).symm_apply_apply (β ν.val))
        let L := (D).symm.mfderivToContinuousLinearEquiv (by decide) (D (β ν.val))
        (H (D (β ν.val))).inner w v = WeilPetersson.beltramiPairing F
          (TH ν P F hF hsmooth (J (L v))).val.val
          (TH ν P F hF hsmooth (J (L w))).val.val := by
  let := C
  let := mΓ
  let := CG
  obtain ⟨N, hN⟩ := exists_nativeWeilPeterssonFamily R hp hg hgenus hΓ hfree hsmooth hnat
  let H (q : LiZhongQC.TeichGamma Γ) := pullbackHermitianCore (N ((D).symm q))
    ((D).symm.mfderivToContinuousLinearEquiv (by decide) q)
  refine ⟨H, ?_⟩
  intro ν P F hF v w
  let L := (D).symm.mfderivToContinuousLinearEquiv (by decide) (D (β ν.val))
  change (N ((D).symm (D (β ν.val)))).inner (L w) (L v) =
    WeilPetersson.beltramiPairing F
      (TH ν P F hF hsmooth (L v)).val.val (TH ν P F hF hsmooth (L w)).val.val
  rw [(D).symm_apply_apply]
  exact hN ν P F hF _ _

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
