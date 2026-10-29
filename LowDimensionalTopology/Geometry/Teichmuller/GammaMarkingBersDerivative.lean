module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkingMobiusDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonCoordinatePairing

/-! The original marking differential and the original harmonic tangent frame. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff
namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami BersWeighted NormalizedCoefficientTransport
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)
local notation "TI" => 𝓘(ℂ, Fin (3*g-3) → ℂ)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "E" => gammaEquiv R hg hgenus hP hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "GC" => gammaBersCoordinates R hg hgenus hΓ hfree hp
local notation "W" => weightedLinearBersCoordinates R hg hgenus hP hΓ hp
local notation "coord" => gammaWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ

variable (f : letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    SourceQCModular.Aut X) (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p f.val w) (ρ : Ball Γ) (N₀ : Deck)
    (hN₀ : ∀ z : ℍ, normalizedUpperEquiv ρ z = N₀ • w z)
local notation "A" => referenceGammaEquiv R R hg hgenus hgenus f.val f.property hΓ hΓ hp hp
local notation "G" => givenReferenceBersMap hp hp hΓ f.val w hw ρ N₀ hN₀

/-- The actual full Γ action has the whole-point original Bers diagram. -/
theorem referenceGammaEquiv_bersCoordinates (a : LiZhongQC.TeichGamma Γ) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    GC (A a) = W (G ((W).symm (GC a))) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  have h := referenceChangeEquiv_bersCoordinates R R hg hgenus hgenus f.val f.property
    hΓ hΓ hp hp w hw ρ N₀ hN₀ ((E).symm a)
  change BC ((E).symm ((E)
    (referenceChangeEquiv R R hg hgenus hgenus f.val f.property ((E).symm a)))) = _
  rw [(E).symm_apply_apply]
  exact h

/-- The weighted frame square uses the original Γ atlas and actual mfderiv;
the model codomain identification is the genuine fromTangentSpace map. -/
theorem referenceGammaEquiv_mfderiv_weighted (a : LiZhongQC.TeichGamma Γ) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := mΓ; letI := CG
    ∀ v : TangentSpace TI a,
      (W).symm (coord (A a) (mfderiv TI TI A a v)) =
        fderiv ℂ G ((W).symm (GC a)) ((W).symm (coord a v)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := mΓ; let := CG
  let : IsManifold TI ω (LiZhongQC.TeichGamma Γ) :=
    gammaBers_isManifold R hg hgenus hΓ hfree hp
  let : Nonempty (LiZhongQC.TeichGamma Γ) := ⟨LiZhongQC.TeichGamma.origin Γ⟩
  intro v
  let Z : (Fin (3*g-3) → ℂ) → (Fin (3*g-3) → ℂ) := fun z => W (G ((W).symm z))
  have hmem : (W).symm (GC a) ∈ coefficientBersImage hΓ := by
    obtain ⟨ν, rfl⟩ := gammaCoefficientProjectionBall_surjective R hg hgenus hΓ hfree hp a
    change (W).symm (BC (coefficientProjectionBall R hg hgenus hP hΓ hfree hp ν)) ∈ _
    rw [coefficientProjectionBall_coordinates, ContinuousLinearEquiv.symm_apply_apply]
    exact (mem_coefficientBersImage_iff_coefficient hΓ _).mpr ⟨ν, rfl⟩
  have hG := ((givenReferenceBersMap_analytic_bothDirections R R hg hgenus hΓ hΓ hp hp
    f.val w hw ρ N₀ hN₀).1 _ hmem).differentiableAt
  have hZ : HasFDerivAt Z
      (((W).toContinuousLinearMap.comp (fderiv ℂ G ((W).symm (GC a)))).comp
        (W).symm.toContinuousLinearMap) (GC a) :=
    ((W).toContinuousLinearMap.hasFDerivAt.comp _ hG.hasFDerivAt).comp _
      (W).symm.toContinuousLinearMap.hasFDerivAt
  have hGC : MDifferentiableAt TI TI GC a :=
    (contMDiff_isOpenEmbedding (n := ω)
      (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)).mdifferentiableAt (by decide)
  have hGCA : MDifferentiableAt TI TI GC (A a) :=
    (contMDiff_isOpenEmbedding (n := ω)
      (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp)).mdifferentiableAt (by decide)
  have hA := (referenceGammaEquiv_contMDiff_bothDirections R R hg hgenus hgenus
    f.val f.property hΓ hΓ hp hp w hw).1.mdifferentiableAt (x := a) (by decide)
  have heq : GC ∘ A = Z ∘ GC :=
    funext (referenceGammaEquiv_bersCoordinates R hp hg hgenus hΓ f w hw ρ N₀ hN₀)
  have hl := mfderiv_comp_apply a hGCA hA v
  have hr := mfderiv_comp_apply a hZ.differentiableAt.mdifferentiableAt hGC v
  have hc := hl.symm.trans
    ((congrArg (fun F => mfderiv TI TI F a v) heq).trans hr)
  rw [hZ.hasMFDerivAt.mfderiv] at hc
  have hsrc := gammaWeilPeterssonCoordinateEquiv_apply R hp hg hgenus hΓ a v
  have htgt := gammaWeilPeterssonCoordinateEquiv_apply R hp hg hgenus hΓ (A a)
    (mfderiv TI TI A a v)
  apply (W).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change coord a v = mfderiv TI TI GC a v at hsrc
  change coord (A a) (mfderiv TI TI A a v) =
    mfderiv TI TI GC (A a) (mfderiv TI TI A a v) at htgt
  exact htgt.trans (hc.trans (by
    change W (fderiv ℂ G ((W).symm (GC a)) ((W).symm (mfderiv TI TI GC a v))) = _
    rw [← hsrc]))

variable (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "T" => gammaWeilPeterssonTangentHarmonicEquiv R hp hg hgenus hΓ hsmooth

/-- Equality transport preserves the same actual original Γ coordinate frame. -/
theorem gammaWeilPeterssonCoordinateEquiv_pointEq :
    letI := mΓ; letI := CG
    ∀ {a b : LiZhongQC.TeichGamma Γ} (_h : a = b) (v : TangentSpace TI a),
      coord b (tangentSpaceCast TI a b v) = coord a v := by
  let := mΓ; let := CG
  intro a b h v
  subst b
  rfl

/-- The original Γ tangent-to-harmonic map has the literal AW coefficient
formula in its actual Bers frame, for every genuine region choice. -/
theorem gammaWeilPeterssonTangentHarmonicEquiv_val_eq_ahlforsWeill
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    letI := C; letI := mΓ; letI := CG
    ∀ v : TangentSpace TI (D (β ν.val)),
      (T ν P F hF v).val.val =
        (ahlforsWeill ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm
          ((W).symm (coord (D (β ν.val)) v)))).val := by
  let := C; let := mΓ; let := CG
  intro v
  let a := D (β ν.val)
  let u := mfderiv TI TI (D).symm a v
  let j := canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
    ((D).symm_apply_apply (β ν.val))
  let K := canonicalBersTangentEquiv R hg hgenus hP hΓ hfree hp hsmooth
  have hframe : K (β ν.val) (j u) = (W).symm (coord a v) := by
    have he := canonicalBersTangentEquiv_pointEq R hp hg hgenus hΓ hfree hsmooth
      ((D).symm_apply_apply (β ν.val)) u
    have hc := congrArg (fun L : TangentSpace TI a →L[ℂ] (Fin (3*g-3) → ℂ) => L v)
      (gammaWeilPeterssonCoordinateEquiv_comp_inverseDifferential R hp hg hgenus hΓ hsmooth a)
    apply (W).injective
    calc
      W (K (β ν.val) (j u)) = W (K ((D).symm a) u) := congrArg (fun q => W q) he
      _ = nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth ((D).symm a) u := rfl
      _ = coord a v := hc
      _ = W ((W).symm (coord a v)) := ((W).apply_symm_apply _).symm
  let L := (D).symm.mfderivToContinuousLinearEquiv (by decide) a
  have hL : L v = u :=
    congrArg
      (fun L₀ : TangentSpace TI a →L[ℂ] TangentSpace TI ((D).symm a) => L₀ v)
      ((D).symm.mfderivToContinuousLinearEquiv_coe (by decide))
  dsimp only [gammaWeilPeterssonTangentHarmonicEquiv, ContinuousLinearEquiv.trans_apply]
  change (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth (j (L v))).val.val = _
  rw [hL, nonzeroTangentHarmonicEquiv_apply, hframe]
  exact congrArg Subtype.val (NativePetersson.harmonicDerivativeEquiv_symm_val_eq_ahlforsWeill
    (deformedNativeSurface R hgenus hΓ hp ν) P (deformedTargetCover R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) F hF
    (And.left (deformedGroup_spec hΓ ν)) _)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
