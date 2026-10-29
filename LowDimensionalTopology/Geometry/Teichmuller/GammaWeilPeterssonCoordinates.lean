module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaRealTangent

/-! Actual Bers tangent coordinates on the full original group Teichmuller space. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle
open scoped UpperHalfPlane Manifold ContDiff
namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)
local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "TG" => LiZhongQC.TeichGamma Γ
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "G" => gammaBersCoordinates R hg hgenus hΓ hfree hp
local notation "realify" => gammaRealComplexTangentEquiv R hp hg hgenus hΓ
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω) (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)
local instance : Nonempty TG := ⟨LiZhongQC.TeichGamma.origin Γ⟩

/-- The actual singleton group Bers chart, with its original topology. -/
def gammaWeilPeterssonCoordinateChart (a : TG) :
    letI := mΓ; OpenPartialHomeomorph TG E := by
  let := mΓ; let := CG
  exact chartAt E a

/-- The model-coordinate equivalence is the actual complex Bers differential. -/
def gammaWeilPeterssonCoordinateEquiv (a : TG) :
    letI := mΓ; letI := CG; TangentSpace TI a ≃L[ℂ] E := by
  let := mΓ; let := CG
  exact { toFun := fun v => v, invFun := fun v => v
          left_inv := fun _ => rfl, right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl
          continuous_toFun := continuous_id, continuous_invFun := continuous_id }

theorem gammaWeilPeterssonCoordinateEquiv_apply (a : TG) :
    letI := mΓ; letI := CG
    ∀ v : TangentSpace TI a,
      gammaWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ a v =
        (NormedSpace.fromTangentSpace (𝕜 := ℂ) (G a)) (mfderiv TI TI G a v) := by
  let := mΓ; let := CG
  let : IsManifold TI ω TG := gammaBers_isManifold R hg hgenus hΓ hfree hp
  intro v
  change v = mfderiv TI TI (extChartAt TI a) a v
  rw [mfderiv_extChartAt_self]
  rfl

local notation "coord" => gammaWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ

/-- The same original coordinates on the actual real tangent fibre. -/
def gammaWeilPeterssonRealTangentCoordinateEquiv (a : TG) :
    letI := mΓ; letI := CG; TangentSpace RI a ≃L[ℝ] E := by
  let := mΓ; let := CG
  let L : TangentSpace TI a ≃L[ℝ] E :=
    { (coord a).toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := (coord a).continuous
      continuous_invFun := (coord a).symm.continuous }
  exact (realify a).trans L

local notation "realCoord" => gammaWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ

theorem gammaWeilPeterssonRealTangentCoordinateEquiv_apply (a : TG) :
    letI := mΓ; letI := CG
    ∀ v : TangentSpace RI a,
      realCoord a v = (NormedSpace.fromTangentSpace (𝕜 := ℝ) (G a))
        (mfderiv RI RI G a v) := by
  let := mΓ; let := CG
  intro v
  exact (gammaWeilPeterssonCoordinateEquiv_apply R hp hg hgenus hΓ a (realify a v)).trans
    (gammaRealComplexTangentEquiv_coordinate_apply R hp hg hgenus hΓ a v)

/-- Forward actual real tangent trivialization. -/
theorem gammaWeilPeterssonRealTangentCoordinateEquiv_trivialization (a q : TG) :
    letI := mΓ; letI := CG; letI : IsManifold RI ω TG := realManifold
    (trivializationAt E (TangentSpace RI) a).continuousLinearMapAt ℝ q =
      (realCoord q).toContinuousLinearMap := by
  let := mΓ; let := CG; let : IsManifold RI ω TG := realManifold
  have ht := TangentBundle.continuousLinearMapAt_trivializationAt (I := RI)
    (show q ∈ (chartAt E a).source from mem_chart_source E q)
  apply ContinuousLinearMap.ext
  intro v
  have hc : realCoord q v = mfderiv RI RI (extChartAt RI a) q v :=
    gammaWeilPeterssonRealTangentCoordinateEquiv_apply R hp hg hgenus hΓ q v
  exact (congrArg (fun A : TangentSpace RI q →L[ℝ] E => A v) ht).trans hc.symm

/-- Inverse actual real tangent trivialization. -/
theorem gammaWeilPeterssonRealTangentCoordinateEquiv_symmL (a q : TG) :
    letI := mΓ; letI := CG; letI : IsManifold RI ω TG := realManifold
    (trivializationAt E (TangentSpace RI) a).symmL ℝ q =
      (realCoord q).symm.toContinuousLinearMap := by
  let := mΓ; let := CG; let : IsManifold RI ω TG := realManifold
  let e := trivializationAt E (TangentSpace RI) a
  have hq : q ∈ e.baseSet := mem_chart_source E q
  have ht := gammaWeilPeterssonRealTangentCoordinateEquiv_trivialization R hp hg hgenus hΓ a q
  apply ContinuousLinearMap.ext
  intro v
  apply (realCoord q).injective
  have he : realCoord q (e.symmL ℝ q v) = v :=
    (congrArg (fun A : TangentSpace RI q →L[ℝ] E => A (e.symmL ℝ q v)) ht).symm.trans
      (e.continuousLinearMapAt_symmL hq v)
  exact he.trans ((realCoord q).apply_symm_apply v).symm
end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
