module

public import LowDimensionalTopology.Geometry.Teichmuller.WolpertLengthDuality
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The original length-duality identity in actual real Bers coordinates

The coordinate contraction uses the original WP form and the actual inverse
chart differential. Its scalar value is the genuine derivative of the same
marked length in that chart, under the supplied native length-duality identity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3*g-3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "c" => nativeWeilPeterssonCoordinateChart
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "ωWP" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "lengthOf" => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)

/-- Native length duality becomes the derivative of the same actual marked
length in the original real Bers chart, with its full coefficient one. -/
theorem nativeWP_contraction_coordinates_eq_lengthDeriv
    (α : LiZhongQC.Loop X) (q : T) (v : letI := C; TangentSpace RI q)
    (hLength : letI := C; MDifferentiableAt RI 𝓘(ℝ) (lengthOf α) q)
    (hDual : WolpertLengthDualityAt
      R hp hg hgenus hΓ hfree hsmooth q α v) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ w : E, (Ω (c q)).curryLeft (D q v) ![w] =
      fderiv ℝ (lengthOf α ∘ (c).symm) (c q) w := by
  let := C
  let : IsManifold RI ω T := realManifold
  have hsource : q ∈ (c).source := mem_chart_source E q
  have htarget : c q ∈ (c).target := (c).map_source hsource
  have hleft : (c).symm (c q) = q := (c).left_inv hsource
  have hDsymm : (D q).symm.toContinuousLinearMap = mfderiv RI RI (c).symm (c q) := by
    rw [← nativeWeilPeterssonRealTangentCoordinateEquiv_symmL
      R hp hg hgenus hΓ hfree hsmooth (basePoint R) q]
    have h := TangentBundle.symmL_trivializationAt (I := RI)
      (x₀ := basePoint R) (x := q) hsource
    simpa only [nativeWeilPeterssonCoordinateChart, extChartAt_coe_symm, extChartAt_coe,
      modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe, Function.comp_id,
      Function.id_comp, Set.range_id, mfderivWithin_univ] using h
  have hsymm : MDifferentiableAt RI RI (c).symm (c q) := by
    have h := contMDiffOn_chart_symm (I := RI) (n := ∞) (x := basePoint R)
    change ContMDiffOn RI RI ∞ (c).symm (c).target at h
    exact (h.contMDiffAt ((c).open_target.mem_nhds htarget)).mdifferentiableAt (by simp)
  have hLength' : MDifferentiableAt RI 𝓘(ℝ) (lengthOf α) ((c).symm (c q)) := by
    simpa only [hleft] using hLength
  have hfd (w : E) : @Eq ℝ
      (fderiv ℝ (lengthOf α ∘ (c).symm) (c q) w)
      (mfderiv RI 𝓘(ℝ) (lengthOf α) q ((D q).symm w)) := by
    have h := mvfderiv_comp_apply (c q) hLength' hsymm
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (c q)).symm w)
    rw [mvfderiv_eq_fderiv (𝕜 := ℝ) (f := lengthOf α ∘ (c).symm) (x := c q)] at h
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [hleft, ← hDsymm] at h
    exact h
  change (∀ z : TangentSpace RI q,
    ωWP q ![v,z] = mfderiv RI 𝓘(ℝ) (lengthOf α) q z) at hDual
  intro w
  change Ω (c q) ![D q v,w] = fderiv ℝ (lengthOf α ∘ (c).symm) (c q) w
  rw [hfd w]
  rw [nativeWeilPeterssonFundamentalRealCoordinateForm_apply, hleft]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  exact hDual ((D q).symm w)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
