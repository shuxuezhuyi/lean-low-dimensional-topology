module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonLocalCoefficients

/-!
# Same-point realification in the existing native Bers atlas

The real and complex self-models use the same charted space and model carrier.
The final identity compares their actual chart differentials at the same point.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp

/-- The canonical scalar restriction at the same point of the same native atlas. -/
def nativeRealComplexTangentEquiv (a : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace RI a ≃L[ℝ] TangentSpace TI a := by
  let := C
  exact
    { toFun := fun v => v
      invFun := fun v => v
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }

/-- This same-fibre identification intertwines the actual real Bers differential
with the already constructed actual complex Bers tangent coordinates. -/
theorem nativeRealComplexTangentEquiv_coordinate_apply (a : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v : TangentSpace RI a,
      nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth a
          (nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth a v) =
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (BC a)) (mfderiv RI RI BC a v) := by
  let := C
  let : IsManifold TI ω (TeichmullerSpace.{0,0} R) :=
    canonicalComplex_isManifold R hg hgenus hP hΓ hfree hp hsmooth
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) :=
    (canonicalBersCoordinates_isOpenEmbedding
      R hg hgenus hP hΓ hfree hp hsmooth).isManifold_singleton
  intro v
  rw [nativeWeilPeterssonCoordinateEquiv_apply]
  change mfderiv TI TI (extChartAt TI a) a
      (nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth a v) =
    mfderiv RI RI (extChartAt RI a) a v
  rw [mfderiv_extChartAt_self, mfderiv_extChartAt_self]
  rfl

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
