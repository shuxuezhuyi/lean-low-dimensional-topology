module

public import LowDimensionalTopology.Unproved.Teichmuller.MarkingPrecompositionHarmonicNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiHermitianRealMobius
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizerModularIsometry

/-!
# Weil–Petersson invariance under the original full modular group

Conditional on the separately named harmonic-coefficient naturality bridge,
these statements concern the original complete integral family and the
original all-QC modular action, using its actual manifold differential.
The English real pairing is twice the real part of the same form.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
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
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "H" => gammaWeilPeterssonCore R hp hg hgenus hΓ hsmooth
local notation "T" => gammaWeilPeterssonTangentHarmonicEquiv R hp hg hgenus hΓ hsmooth

/-- Equality of the actual base point transports the same original Hermitian
form by the genuine equality cast, without adding a new invariance assumption. -/
theorem gammaWeilPeterssonCore_pointEq :
    letI := C
    letI := mΓ
    letI := CG
    ∀ {a b : LiZhongQC.TeichGamma Γ} (_h : a = b) (v w : TangentSpace TI a),
      (H b).inner (tangentSpaceCast TI a b w) (tangentSpaceCast TI a b v) =
        (H a).inner w v := by
  let := C
  let := mΓ
  let := CG
  intro a b h v w
  subst b
  rfl

/-- Changing the marking preserves the original WP form once the actual
harmonic-coefficient differential law has been supplied. -/
theorem gammaWeilPeterssonCore_reference_invariant
    (hnat : Unproved.Teichmuller.MarkingPrecompositionHarmonicNaturality
      R hp hg hgenus hΓ hsmooth) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := C
    letI := mΓ
    letI := CG
    ∀ (f : SourceQCModular.Aut X) (a : LiZhongQC.TeichGamma Γ) (v w : TangentSpace TI a),
      let A := referenceGammaEquiv R R hg hgenus hgenus f.val f.property hΓ hΓ hp hp
      (H (A a)).inner (mfderiv TI TI A a w) (mfderiv TI TI A a v) = (H a).inner w v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := C
  let := mΓ
  let := CG
  intro f a
  obtain ⟨ν, hν⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp ((D).symm a)
  have ha : D (β ν.val) = a := by
    rw [coefficientProjection_ball, hν, (D).apply_symm_apply]
  rw [← ha]
  intro v w
  let A := referenceGammaEquiv R R hg hgenus hgenus f.val f.property hΓ hΓ hp hp
  obtain ⟨P, F, hF⟩ := exists_deformedHalfPlaneFundamentalRegion R hgenus hΓ hp ν
  obtain ⟨ν', M, hpoint, P', hF', c, hc, hcover, ht⟩ := hnat f ν P F hF
  let J := tangentSpaceCast TI (A (D (β ν.val))) (D (β ν'.val))
  calc
    (H (A (D (β ν.val)))).inner
        (mfderiv TI TI A (D (β ν.val)) w) (mfderiv TI TI A (D (β ν.val)) v) =
        (H (D (β ν'.val))).inner
          (J (mfderiv TI TI A (D (β ν.val)) w))
          (J (mfderiv TI TI A (D (β ν.val)) v)) :=
      (gammaWeilPeterssonCore_pointEq R hp hg hgenus hΓ hsmooth hpoint _ _).symm
    _ = WeilPetersson.beltramiPairing ((fun z : ℍ => M • z) ⁻¹' F)
        (pullback M (T ν P F hF v).val.val) (pullback M (T ν P F hF w).val.val) := by
      rw [gammaWeilPeterssonCore_integral R hp hg hgenus hΓ hsmooth ν' P' _ hF', ht v, ht w]
    _ = WeilPetersson.beltramiPairing F (T ν P F hF v).val.val (T ν P F hF w).val.val :=
      WeilPetersson.beltramiPairing_realMobiusPullback M F hF.1.measurableSet _ _
    _ = (H (D (β ν.val))).inner w v :=
      (gammaWeilPeterssonCore_integral R hp hg hgenus hΓ hsmooth ν P F hF v w).symm

/-- The complete original WP form is preserved by every class in the actual
quotient of all QC surface automorphisms by free homotopy. -/
theorem gammaWeilPeterssonCore_modular_invariant
    (hnat : Unproved.Teichmuller.MarkingPrecompositionHarmonicNaturality
      R hp hg hgenus hΓ hsmooth) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := C
    letI := mΓ
    letI := CG
    ∀ (γ : SourceQCModular.ModularGroup X) (a : LiZhongQC.TeichGamma Γ)
      (v w : TangentSpace TI a),
      let A := gammaModularRepresentation R hg hgenus hΓ hp γ
      (H (A a)).inner (mfderiv TI TI A a w) (mfderiv TI TI A a v) = (H a).inner w v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := C
  let := mΓ
  let := CG
  intro γ
  refine Quotient.inductionOn γ ?_
  intro f a v w
  have hA : (gammaModularRepresentation R hg hgenus hΓ hp (⟦f⟧ : SourceQCModular.ModularGroup X) :
      LiZhongQC.TeichGamma Γ → LiZhongQC.TeichGamma Γ) =
      (referenceGammaEquiv R R hg hgenus hgenus f.val f.property hΓ hΓ hp hp :
        LiZhongQC.TeichGamma Γ → LiZhongQC.TeichGamma Γ) :=
    congrArg (fun e : Equiv.Perm (LiZhongQC.TeichGamma Γ) =>
      (e : LiZhongQC.TeichGamma Γ → LiZhongQC.TeichGamma Γ))
      (gammaModularRepresentation_mk R hg hgenus hΓ hp f)
  have hInv := congrArg (fun A : LiZhongQC.TeichGamma Γ → LiZhongQC.TeichGamma Γ =>
    (H (A a)).inner (mfderiv TI TI A a w) (mfderiv TI TI A a v) = (H a).inner w v) hA
  exact hInv.mpr
    (gammaWeilPeterssonCore_reference_invariant R hp hg hgenus hΓ hsmooth hnat f a v w)

/-- Every original full normalizer class preserves the original group WP form,
under the explicit harmonic-coefficient bridge and existing QC smoothing. -/
theorem gammaWeilPeterssonCore_upperModular_invariant
    (hnat : Unproved.Teichmuller.MarkingPrecompositionHarmonicNaturality
      R hp hg hgenus hΓ hsmooth) :
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
      (H (A a)).inner (mfderiv TI TI A a w) (mfderiv TI TI A a v) = (H a).inner w v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := C
  let := mΓ
  let := CG
  intro γ a v w
  exact gammaWeilPeterssonCore_modular_invariant R hp hg hgenus hΓ hsmooth hnat
    (QCNormalizerModular.modularEquiv hp γ) a v w

/-- The original full normalizer action preserves the English twice-real-part
pairing on every original group tangent fibre. -/
theorem gammaWeilPeterssonRealPairing_upperModular_invariant
    (hnat : Unproved.Teichmuller.MarkingPrecompositionHarmonicNaturality
      R hp hg hgenus hΓ hsmooth) :
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
  exact congrArg (fun z : ℂ => 2 * z.re)
    (gammaWeilPeterssonCore_upperModular_invariant R hp hg hgenus hΓ hsmooth hnat γ a v w)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
