module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonCore
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Same-point realification on the original full group Teichmuller space. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
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

/-- The source's real and holomorphic tangent identification on all original T(Gamma). -/
def gammaRealComplexTangentEquiv (a : TG) :
    letI := mΓ
    letI := CG
    TangentSpace RI a ≃L[ℝ] TangentSpace TI a := by
  let := mΓ
  let := CG
  exact
    { toFun := fun v => v, invFun := fun v => v
      left_inv := fun _ => rfl, right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl
      continuous_toFun := continuous_id, continuous_invFun := continuous_id }

/-- Both actual group Bers differentials give the same model-coordinate value. -/
theorem gammaRealComplexTangentEquiv_coordinate_apply (a : TG) :
    letI := mΓ
    letI := CG
    ∀ v : TangentSpace RI a,
      (NormedSpace.fromTangentSpace (𝕜 := ℂ) (G a))
        (mfderiv TI TI G a (gammaRealComplexTangentEquiv R hp hg hgenus hΓ a v)) =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (G a)) (mfderiv RI RI G a v) := by
  let := mΓ
  let := CG
  let : Nonempty TG := ⟨LiZhongQC.TeichGamma.origin Γ⟩
  let : IsManifold TI ω TG := gammaBers_isManifold R hg hgenus hΓ hfree hp
  let : IsManifold RI ω TG :=
    (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp).isManifold_singleton
  intro v
  change mfderiv TI TI (extChartAt TI a) a
    (gammaRealComplexTangentEquiv R hp hg hgenus hΓ a v) = mfderiv RI RI (extChartAt RI a) a v
  rw [mfderiv_extChartAt_self, mfderiv_extChartAt_self]
  rfl
end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
