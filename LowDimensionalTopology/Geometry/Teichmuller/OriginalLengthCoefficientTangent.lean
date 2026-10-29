module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeGeneralEndpointLengthPetersson
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjectionDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangentTrivialization
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The original length differential on an actual coefficient tangent

The original coefficient projection, its actual Bers chart and the real
tangent fibre retain the same direction. The endpoint-series first variation
therefore evaluates the genuine manifold differential of the same length.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Bundle Set Filter
open scoped UpperHalfPlane Manifold ContDiff Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "T" => TeichmullerSpace R
local notation "B" => Space Γ
local notation "E" => Fin (3 * g - 3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "W" => weightedLinearBersCoordinates R hg hgenus hP hΓ hp
local notation "b" => basePoint R
local notation "c" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth b
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "r" => nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "lengthOf" => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)

/-- The same original projection derivative, viewed as a real tangent, has
exactly its proved original weighted Bers coordinates. -/
theorem nativeRealCoefficientTangent_coordinates (μ : B) :
    letI := C
    D b ((r b).symm (mfderiv 𝓘(ℂ, B) TI β 0 μ)) =
      W (BersWeighted.automorphicIntegralOperator hΓ μ) := by
  let := C
  change W (canonicalBaseTangentEquiv R hg hgenus hP hΓ hfree hp hsmooth
    (mfderiv 𝓘(ℂ, B) TI β 0 μ)) = _
  rw [canonicalBaseTangentEquiv_mfderiv_coefficientProjection]

/-- The actual real length differential on an original coefficient-projection
tangent is the literal endpoint Petersson pairing for that same covering. -/
theorem marked_length_mfderiv_coefficient_direction
    (α : LiZhongQC.Loop X) (A : Deck) (hAΓ : A ∈ Γ)
    (hcov : LiZhongQC.Covers p A α)
    (hA : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (hLength : letI := C; MDifferentiableAt RI 𝓘(ℝ) (lengthOf α) b)
    (μ : B) :
    letI := C
    let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
      (Subgroup.zpowers (Hyperbolic.realSLMobius A))
    let CA := Quotient (QuotientGroup.rightRel SA)
    ∀ (ρ : CA → Γ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
      ∀ (F : Set ℂ), LiZhongQC.IsFundamentalDomainH Γ F →
        let Θ : ℂ → ℂ := fun z => ∑' u : CA,
          GeodesicSeries.seed (Hyperbolic.hHyperbolicAxis A hA ht)
              (LiZhongQC.h36p_m (ρ u).val z) *
            (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2
        mfderiv RI 𝓘(ℝ) (lengthOf α) b
            ((r b).symm (mfderiv 𝓘(ℂ, B) TI β 0 μ)) =
          (2 / Real.pi) * (LiZhongQC.beltramiPairing F
            (planeRepresentative μ.val) Θ).re := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  intro ρ hρ F hF
  have hsource : b ∈ (c).source := mem_chart_source E b
  have htarget : c b ∈ (c).target := (c).map_source hsource
  have hleft : (c).symm (c b) = b := (c).left_inv hsource
  have hDsymm : (D b).symm.toContinuousLinearMap = mfderiv RI RI (c).symm (c b) := by
    rw [← nativeWeilPeterssonRealTangentCoordinateEquiv_symmL
      R hp hg hgenus hΓ hfree hsmooth b b]
    have h := TangentBundle.symmL_trivializationAt (I := RI)
      (x₀ := b) (x := b) hsource
    simpa only [nativeWeilPeterssonCoordinateChart, extChartAt_coe_symm, extChartAt_coe,
      modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe, Function.comp_id,
      Function.id_comp, Set.range_id, mfderivWithin_univ] using h
  have hsymm : MDifferentiableAt RI RI (c).symm (c b) := by
    have h := contMDiffOn_chart_symm (I := RI) (n := ∞) (x := b)
    change ContMDiffOn RI RI ∞ (c).symm (c).target at h
    exact (h.contMDiffAt ((c).open_target.mem_nhds htarget)).mdifferentiableAt (by simp)
  have hLength' : MDifferentiableAt RI 𝓘(ℝ) (lengthOf α) ((c).symm (c b)) := by
    simpa only [hleft] using hLength
  have hfd (w : E) :
      fderiv ℝ (lengthOf α ∘ (c).symm) (c b) w =
        mfderiv RI 𝓘(ℝ) (lengthOf α) b ((D b).symm w) := by
    have h := mvfderiv_comp_apply (c b) hLength' hsymm
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (c b)).symm w)
    rw [mvfderiv_eq_fderiv (𝕜 := ℝ) (f := lengthOf α ∘ (c).symm) (x := c b)] at h
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [hleft, ← hDsymm] at h
    exact h
  have hscalar : DifferentiableAt ℝ (lengthOf α ∘ (c).symm) (c b) :=
    (hLength'.comp (c b) hsymm).differentiableAt
  have hline : HasDerivAt (fun t : ℂ => t • μ) μ 0 := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have heq : (fun t : ℂ => t⁻¹ • (((0 : ℂ) + t) • μ - (0 : ℂ) • μ))
        =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ => μ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := by simpa using ht
      simp only [zero_add, zero_smul, sub_zero, smul_smul, inv_mul_cancel₀ ht', one_smul]
    exact (Filter.tendsto_congr' heq).mpr tendsto_const_nhds
  have hcurve : HasDerivAt (fun t : ℝ => BC (β ((t : ℂ) • μ)))
      (W (BersWeighted.automorphicIntegralOperator hΓ μ)) 0 := by
    have h := (hasFDerivAt_coefficientProjection_coordinates
      R hg hgenus hP hΓ hfree hp).comp_hasDerivAt_of_eq
        (0 : ℂ) hline (by simp only [zero_smul])
    apply hasDerivAt_pi.mpr
    intro k
    have hk' : HasDerivAt (fun t : ℂ => BC (β (t • μ)) k)
        ((W (BersWeighted.automorphicIntegralOperator hΓ μ)) k) (0 : ℂ) := by
      let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
      exact (hasDerivAt_pi.mp h) k
    simpa only [Complex.ofReal_zero] using hk'.comp_ofReal
  have hscalar' : DifferentiableAt ℝ (lengthOf α ∘ (c).symm)
      (BC (β ((0 : ℂ) • μ))) := by
    simpa only [zero_smul, coefficientProjection_zero,
      nativeWeilPeterssonCoordinateChart_coe] using hscalar
  have hd : HasDerivAt
      (fun t : ℝ => lengthOf α (β ((t : ℂ) • μ)))
      (fderiv ℝ (lengthOf α ∘ (c).symm) (c b)
        (W (BersWeighted.automorphicIntegralOperator hΓ μ))) 0 := by
    have h := hscalar'.hasFDerivAt.comp_hasDerivAt 0 hcurve
    rw [zero_smul, coefficientProjection_zero] at h
    apply h.congr_of_eventuallyEq
    exact Eventually.of_forall fun t => congrArg (lengthOf α)
      (coefficientProjection_eq_chartSymm R hg hgenus hP hΓ hfree hp hsmooth ((t : ℂ) • μ))
  have hvariation := marked_length_hasDerivAt_general_endpoint_petersson
    R hg hgenus hΓ hp α A hAΓ hcov hA ht μ ρ hρ F hF
  have he := hd.unique hvariation
  rw [hfd] at he
  have htangent : (D b).symm (W (BersWeighted.automorphicIntegralOperator hΓ μ)) =
      (r b).symm (mfderiv 𝓘(ℂ, B) TI β 0 μ) := by
    apply (D b).injective
    rw [ContinuousLinearEquiv.apply_symm_apply,
      nativeRealCoefficientTangent_coordinates]
  rw [htangent] at he
  exact he

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
