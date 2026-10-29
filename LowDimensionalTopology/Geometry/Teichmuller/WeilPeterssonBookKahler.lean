module

public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceHarmonicNaturalityProof
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCoordinateClosedness
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothRealMetric

/-!
# The book's Kähler definition for the same original native WP family

The actual positive smooth metric and actual smooth fundamental form retain
their original Hermitian value. Closedness is expressed in their actual full
Bers chart, including the genuine tangent-bundle coordinate identity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)

local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "H" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree
local notation "coeff" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree
local notation "realify" => nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree
local notation "coord" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree
local notation "realCoord" => nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree
local notation "realBilin" => nativeWeilPeterssonRealBilinForm R hp hg hgenus hΓ hfree
local notation "originalForm" => nativeWeilPeterssonFundamentalForm R hp hg hgenus hΓ hfree
local notation "metric" => nativeWeilPeterssonSmoothRealMetric R hp hg hgenus hΓ hfree
local notation "form" => nativeWeilPeterssonSmoothFundamentalForm R hp hg hgenus hΓ hfree
local notation "coordinates" => nativeWeilPeterssonFundamentalRealCoordinateForm R hp hg hgenus hΓ hfree

/-- The book's criterion for this specific original C-infinity Hermitian WP
family: its actual positive smooth real metric has the original value, its
same smooth form is g(J·,·)=-2 Im h, and that form is closed in its actual
global Bers coordinates. J is multiplication by i under actual realification. -/
def NativeWeilPeterssonIsBookKahler
    (hsmooth0 : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    (hWP0 : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth0) : Prop :=
  letI := C hsmooth0
  letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := Topology.IsOpenEmbedding.isManifold_singleton
    (I := RI) (n := ω)
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth0)
  IsManifold TI ω (TeichmullerSpace.{0,0} R) ∧
  (∀ (a : TeichmullerSpace.{0,0} R) (v w : TangentSpace TI a),
    (starRingEnd ℂ) ((H hsmooth0 a).inner w v) = (H hsmooth0 a).inner v w) ∧
  (∀ (a : TeichmullerSpace.{0,0} R) (v : TangentSpace RI a), v ≠ 0 →
    0 < (metric hsmooth0 hWP0).inner a v v) ∧
  (∀ (a : TeichmullerSpace.{0,0} R) (j k : Fin (3*g-3)),
    ContDiffOn ℝ ∞ (coeff hsmooth0 a j k) (chart hsmooth0 a).target) ∧
  (∀ (a : TeichmullerSpace.{0,0} R) (v : TangentSpace RI a),
    realCoord hsmooth0 a ((realify hsmooth0 a).symm (Complex.I • realify hsmooth0 a v)) =
      Complex.I • realCoord hsmooth0 a v) ∧
  (∀ (a : TeichmullerSpace.{0,0} R) (v w : TangentSpace RI a),
    (metric hsmooth0 hWP0).inner a v w =
        2 * ((H hsmooth0 a).inner (realify hsmooth0 a w) (realify hsmooth0 a v)).re ∧
      form hsmooth0 hWP0 a ![v,w] =
        -2 * ((H hsmooth0 a).inner (realify hsmooth0 a w) (realify hsmooth0 a v)).im ∧
      form hsmooth0 hWP0 a ![v,w] = (metric hsmooth0 hWP0).inner a
        ((realify hsmooth0 a).symm (Complex.I • realify hsmooth0 a v)) w) ∧
  (∀ q : TeichmullerSpace.{0,0} R,
    (form hsmooth0 hWP0 q).compContinuousLinearMap
        ((trivializationAt E (TangentSpace RI) (basePoint R)).symmL ℝ q) =
      coordinates hsmooth0 (basePoint R) (BC q)) ∧
  ∀ t ∈ (chart hsmooth0 (basePoint R)).target,
    extDerivWithin (coordinates hsmooth0 (basePoint R))
      (chart hsmooth0 (basePoint R)).target t = 0

/-- The same original WP Hermitian metric satisfies the book's Kähler
criterion. Reference naturality is supplied by its proved QC construction. -/
theorem nativeWeilPeterssonIsBookKahler_of_harmonicVariation
    (hsmooth0 : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    (hWP0 : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth0)
    (hvariation : ∀ ν : Ball Γ, Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      (deformedNativeSurface R hgenus hΓ hp ν)
      (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) (deformedGroup_spec hΓ ν).1
      (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hsmooth0)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0}) :
    NativeWeilPeterssonIsBookKahler R hp hg hgenus hΓ hfree hsmooth0 hWP0 := by
  let := C hsmooth0
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := Topology.IsOpenEmbedding.isManifold_singleton
    (I := RI) (n := ω)
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth0)
  have hm (a : TeichmullerSpace.{0,0} R) (v w : TangentSpace RI a) :
      (metric hsmooth0 hWP0).inner a v w =
        realBilin hsmooth0 a (realify hsmooth0 a v) (realify hsmooth0 a w) :=
    nativeWeilPeterssonRealTangentForm_apply R hp hg hgenus hΓ hfree hsmooth0 a v w
  have hf (a : TeichmullerSpace.{0,0} R) (v : Fin 2 → TangentSpace RI a) :
      form hsmooth0 hWP0 a v = originalForm hsmooth0 a (fun i => realify hsmooth0 a (v i)) :=
    nativeWeilPeterssonSmoothFundamentalForm_apply R hp hg hgenus hΓ hfree hsmooth0 hWP0 a v
  refine ⟨canonicalComplex_isManifold R hg hgenus hP hΓ hfree hp hsmooth0,
    ?_, ?_, hWP0, ?_, ?_, ?_, ?_⟩
  · exact fun a v w => (H hsmooth0 a).conj_inner_symm v w
  · exact fun a v hv => (metric hsmooth0 hWP0).pos a v hv
  · intro a v
    change coord hsmooth0 a
        (realify hsmooth0 a ((realify hsmooth0 a).symm (Complex.I • realify hsmooth0 a v))) =
      Complex.I • coord hsmooth0 a (realify hsmooth0 a v)
    exact (congrArg (coord hsmooth0 a)
      ((realify hsmooth0 a).apply_symm_apply _)).trans
        (map_smul (coord hsmooth0 a) Complex.I (realify hsmooth0 a v))
  · intro a v w
    refine ⟨nativeWeilPeterssonSmoothRealMetric_inner
      R hp hg hgenus hΓ hfree hsmooth0 hWP0 a v w, ?_, ?_⟩
    · exact (hf a ![v,w]).trans
        (nativeWeilPeterssonFundamentalForm_apply R hp hg hgenus hΓ hfree hsmooth0 a
          (fun i => realify hsmooth0 a (![v,w] i)))
    · have hvec : (fun i => realify hsmooth0 a (![v,w] i)) =
          ![realify hsmooth0 a v, realify hsmooth0 a w] := by
        funext i
        fin_cases i <;> rfl
      calc
        form hsmooth0 hWP0 a ![v,w] =
            originalForm hsmooth0 a ![realify hsmooth0 a v, realify hsmooth0 a w] :=
          (hf a ![v,w]).trans (congrArg (originalForm hsmooth0 a) hvec)
        _ = realBilin hsmooth0 a (Complex.I • realify hsmooth0 a v) (realify hsmooth0 a w) :=
          nativeWeilPeterssonFundamentalForm_eq_realBilinForm
            R hp hg hgenus hΓ hfree hsmooth0 a (realify hsmooth0 a v) (realify hsmooth0 a w)
        _ = (metric hsmooth0 hWP0).inner a
            ((realify hsmooth0 a).symm (Complex.I • realify hsmooth0 a v)) w := by
          exact (congrArg (fun x : TangentSpace TI a =>
            realBilin hsmooth0 a x (realify hsmooth0 a w))
              ((realify hsmooth0 a).apply_symm_apply _).symm).trans
                (hm a ((realify hsmooth0 a).symm (Complex.I • realify hsmooth0 a v)) w).symm
  · intro q
    exact nativeWeilPeterssonRealFundamentalForm_coordinates
      R hp hg hgenus hΓ hfree hsmooth0 (basePoint R) q
  · exact nativeWeilPeterssonCoordinateForm_closed_of_harmonicVariation
      R hp hg hgenus hΓ hsmooth0 hfree hWP0
        (deformedReferenceHarmonicNaturality R hp hg hgenus hΓ hfree hsmooth0) hvariation hjets

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
