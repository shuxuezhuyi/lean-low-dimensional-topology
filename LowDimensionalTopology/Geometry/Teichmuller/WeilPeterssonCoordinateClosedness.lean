module

public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceWeilPeterssonCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonSmoothForm

/-!
# Closedness of the original WP form on the full original Gamma Bers target

The conditional theorem retains the original chosen WP integral form and its
actual coordinate inverse. The new integral-variation input ranges only over
the actual deformed references of the one fixed compact original surface.
The local smoothness input is required only for that original surface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "hP" => canonicalHandleGroupPresentation g

section Native
variable (hfree : LiZhongQC.ActsFreely Γ)
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "U" => PartialEquiv.target (PartialHomeomorph.toPartialEquiv
  (OpenPartialHomeomorph.toPartialHomeomorph (chart (basePoint R))))
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

/-- The actual native coordinate form is closed everywhere on its full open
Bers target. Variation at R has not been promoted to variation at other surfaces. -/
theorem nativeWeilPeterssonCoordinateForm_closed_of_harmonicVariation
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hnat : Unproved.Teichmuller.DeformedReferenceHarmonicNaturality
      R hp hg hgenus hΓ hfree hsmooth)
    (hvariation : ∀ ν : Ball Γ,
      Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
        (deformedNativeSurface R hgenus hΓ hp ν)
        (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hg
        (deformedNativeSurface_hasGenus R hgenus hΓ hp ν)
        (deformedGroup_spec hΓ ν).1
        (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0}) :
    ∀ t ∈ U, extDerivWithin Ω U t = 0 := by
  intro t ht
  have htrange : t ∈ range BC := by
    rwa [← nativeWeilPeterssonCoordinateChart_target_eq_range
      R hp hg hgenus hΓ hfree hsmooth (basePoint R)]
  obtain ⟨a, rfl⟩ := htrange
  obtain ⟨ν, hν⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp a
  have hνa : β ν.val = a :=
    (coefficientProjection_ball R hg hgenus hΓ hfree hp ν).trans hν
  rw [← hνa] at ht ⊢
  let Y := deformedNativeSurface R hgenus hΓ hp ν
  let hY := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
  let hpY := deformedNativeSurface_uniformization R hgenus hΓ hp ν
  let hΔ := (deformedGroup_spec hΓ ν).1
  let hfY := deformedNativeSurface_actsFreely R hgenus hΓ hp ν
  let ΩY := nativeWeilPeterssonFundamentalRealCoordinateForm
    Y hpY hg hY hΔ hfY hsmooth (basePoint Y)
  let f := deformedReferenceWeilPeterssonCoordinateMap R hp hg hgenus hΓ ν
  have hcenter : f (BC (β ν.val)) = 0 :=
    deformedReferenceWeilPeterssonCoordinateMap_center R hp hg hgenus hΓ hfree ν
  have hΩY : DifferentiableAt ℝ ΩY 0 :=
    differentiableAt_deformedWeilPeterssonCoordinateForm_zero
      R hp hg hgenus hΓ hfree hsmooth ν hWP hnat
  have hzeroY : extDeriv ΩY 0 = 0 :=
    extDeriv_nativeWeilPeterssonBaseCoordinateForm_zero
      Y hpY hg hY hΔ hfY hsmooth (hvariation ν) hjets hΩY
  obtain ⟨V, hVo, hVν, _, hV⟩ := nativeWeilPeterssonCoordinateForm_deformedReference_local_pullback
    R hp hg hgenus hΓ hfree hsmooth ν hnat
  have heq : Ω =ᶠ[𝓝 (BC (β ν.val))]
      (fun t => (ΩY (f t)).compContinuousLinearMap (fderiv ℝ f t)) := by
    filter_upwards [hVo.mem_nhds hVν] with t ht
    exact hV t ht
  have hf : ContDiffAt ℝ ∞ f (BC (β ν.val)) :=
    ((deformedReferenceWeilPeterssonCoordinateMap_analytic
      R hp hg hgenus hΓ hfree hsmooth ν).1 _ ht).restrictScalars.contDiffAt
  have hΩY' : DifferentiableAt ℝ ΩY (f (BC (β ν.val))) := by
    rwa [hcenter]
  have hz : extDeriv Ω (BC (β ν.val)) = 0 := calc
    _ = extDeriv (fun t => (ΩY (f t)).compContinuousLinearMap (fderiv ℝ f t))
        (BC (β ν.val)) := heq.extDeriv_eq
    _ = (extDeriv ΩY (f (BC (β ν.val)))).compContinuousLinearMap
        (fderiv ℝ f (BC (β ν.val))) := extDeriv_pullback hΩY' hf (by simp)
    _ = 0 := by
      rw [hcenter, hzeroY]
      apply ContinuousAlternatingMap.ext
      intro v
      simp
  simpa only [extDerivWithin, extDeriv,
    fderivWithin_of_isOpen (chart (basePoint R)).open_target ht] using hz
end Native

local notation "TG" => LiZhongQC.TeichGamma Γ
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "G" => gammaBersCoordinates R hg hgenus hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "gchart" => gammaWeilPeterssonCoordinateChart R hp hg hgenus hΓ
local notation "nchart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "nΩ" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "a₀" => LiZhongQC.TeichGamma.origin Γ
local instance : Nonempty TG := ⟨a₀⟩

/-- The original full Gamma WP form in the original actual global Bers chart. -/
def gammaWeilPeterssonGlobalCoordinateForm (t : E) : E [⋀^Fin 2]→L[ℝ] ℝ := by
  let := mΓ; let := CG
  exact gammaWeilPeterssonFundamentalModelForm R hp hg hgenus hΓ hsmooth ((gchart a₀).symm t)

local notation "ΩΓ" => gammaWeilPeterssonGlobalCoordinateForm R hp hg hgenus hΓ hsmooth

/-- These coefficients are exactly the original group Core's English-normalized
pairing in its actual inverse Bers differential. -/
theorem gammaWeilPeterssonGlobalCoordinateForm_apply (t : E) :
    letI := C; letI := mΓ; letI := CG
    ∀ v : Fin 2 → E,
      ΩΓ t v = -2 * ((gammaWeilPeterssonCore R hp hg hgenus hΓ hsmooth
        ((gchart a₀).symm t)).inner
          ((gammaWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ
            ((gchart a₀).symm t)).symm (v 1))
          ((gammaWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ
            ((gchart a₀).symm t)).symm (v 0))).im := by
  let := C; let := mΓ; let := CG
  exact gammaWeilPeterssonFundamentalModelForm_apply R hp hg hgenus hΓ hsmooth
    ((gchart a₀).symm t)

/-- The domain used for closedness is the entire range of the original Gamma
Bers map, exactly the target of its original singleton chart. -/
theorem gammaWeilPeterssonCoordinateChart_target_eq_range :
    letI := mΓ; letI := CG
    (gchart a₀).target = range G := by
  let := mΓ; let := CG
  change (Topology.IsOpenEmbedding.toOpenPartialHomeomorph G
    (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)).target = _
  exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target _ _

/-- The whole original Gamma coordinate form agrees on its actual domain
with the same original native form, via the proved genuine coordinate square. -/
theorem gammaWeilPeterssonGlobalCoordinateForm_eq_native :
    letI := C; letI := mΓ; letI := CG
    EqOn ΩΓ nΩ (range G) := by
  let := C; let := mΓ; let := CG
  intro t ht
  have ht' : t ∈ (gchart a₀).target := by
    rwa [gammaWeilPeterssonCoordinateChart_target_eq_range]
  have h := gammaWeilPeterssonFundamentalModelForm_coordinates R hp hg hgenus hΓ hsmooth
    a₀ ((gchart a₀).symm t)
  rw [(gchart a₀).right_inv ht'] at h
  exact h

/-- Full coordinate closedness for the original Gamma form, conditional
on the explicit independent harmonic and analytic inputs. The local coefficient
smoothness premise is only at the one fixed original compact R. -/
theorem gammaWeilPeterssonGlobalCoordinateForm_closed_of_harmonicVariation
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hnat : Unproved.Teichmuller.DeformedReferenceHarmonicNaturality
      R hp hg hgenus hΓ hfree hsmooth)
    (hvariation : ∀ ν : Ball Γ,
      Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
        (deformedNativeSurface R hgenus hΓ hp ν)
        (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hg
        (deformedNativeSurface_hasGenus R hgenus hΓ hp ν)
        (deformedGroup_spec hΓ ν).1
        (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0}) :
    letI := C; letI := mΓ; letI := CG
    ∀ t ∈ range G, extDerivWithin ΩΓ (range G) t = 0 := by
  let := C; let := mΓ; let := CG
  have hU : range G = (nchart (basePoint R)).target := by
    rw [← gammaWeilPeterssonCoordinateChart_target_eq_range]
    exact gammaWeilPeterssonCoordinateChart_target_eq_native R hp hg hgenus hΓ hsmooth a₀
  intro t ht
  rw [extDerivWithin_congr'
    (gammaWeilPeterssonGlobalCoordinateForm_eq_native R hp hg hgenus hΓ hsmooth) ht, hU]
  exact nativeWeilPeterssonCoordinateForm_closed_of_harmonicVariation
    R hp hg hgenus hΓ hsmooth hfree hWP hnat hvariation hjets t (hU ▸ ht)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
