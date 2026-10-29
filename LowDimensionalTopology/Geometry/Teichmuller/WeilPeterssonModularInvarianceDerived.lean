module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonModularInvariance
public import LowDimensionalTopology.Geometry.Teichmuller.MarkingHarmonicNaturalityProof

/-! Original WP pairing invariance from the proved marking harmonic law. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "TI" => 𝓘(ℂ, Fin (3*g-3) → ℂ)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "H" => gammaWeilPeterssonCore R hp hg hgenus hΓ hsmooth

/-- Every original full modular class preserves the original WP form under QC smoothing. -/
theorem gammaWeilPeterssonCore_upperModular_invariant_of_smoothing :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := C
    letI := mΓ
    letI := CG
    ∀ (γ : QCNormalizerModular.ModularGroup hp) (a : LiZhongQC.TeichGamma Γ)
      (v w : TangentSpace TI a),
      let A := upperModularRepresentation R hg hgenus hΓ hp γ
      (H (A a)).inner (mfderiv TI TI A a w) (mfderiv TI TI A a v) =
        (H a).inner w v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := C
  let := mΓ
  let := CG
  intro γ a v w
  exact gammaWeilPeterssonCore_upperModular_invariant R hp hg hgenus hΓ hsmooth
    (markingPrecompositionHarmonicNaturality_of_smoothing R hp hg hgenus hΓ hsmooth) γ a v w

/-- The same original full modular action preserves the twice-real-part WP pairing. -/
theorem gammaWeilPeterssonRealPairing_upperModular_invariant_of_smoothing :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := C
    letI := mΓ
    letI := CG
    ∀ (γ : QCNormalizerModular.ModularGroup hp) (a : LiZhongQC.TeichGamma Γ)
      (v w : TangentSpace TI a),
      let A := upperModularRepresentation R hg hgenus hΓ hp γ
      2 * ((H (A a)).inner (mfderiv TI TI A a w) (mfderiv TI TI A a v)).re =
        2 * ((H a).inner w v).re := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := C
  let := mΓ
  let := CG
  intro γ a v w
  exact gammaWeilPeterssonRealPairing_upperModular_invariant R hp hg hgenus hΓ hsmooth
    (markingPrecompositionHarmonicNaturality_of_smoothing R hp hg hgenus hΓ hsmooth) γ a v w

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
