module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonMetric
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalBersTangent
public import Mathlib.Algebra.BigOperators.Pi

/-!
# The original Weil–Petersson form in the actual canonical Bers coordinates

Choose the already constructed original tangent-fibre family. Its complete
integral specification is retained below. Coordinate vectors are the inverse
of the actual Bers-chart differential, not an independently chosen frame.
No norm or inner-product-space instance is installed on a tangent fibre.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport NativePetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree

/-- The existing original native WP family, selected with its full integral law. -/
@[instance_reducible] def nativeWeilPeterssonCore :
    letI := C
    ∀ a : TeichmullerSpace.{0,0} R, InnerProductSpace.Core ℂ (TangentSpace TI a) := by
  letI := C
  exact Classical.choose
    (exists_nativeWeilPeterssonFamily_of_smoothing R hp hg hgenus hΓ hfree hsmooth)

/-- The selected family still has the original first-linear integral for every
coefficient, every genuine region and every pair of original tangent vectors. -/
theorem nativeWeilPeterssonCore_integral :
    letI := C
    ∀ (ν : Ball Γ)
      (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
      (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
      (v w : TangentSpace TI (β ν.val)),
      (nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth (β ν.val)).inner w v =
        WeilPetersson.beltramiPairing F
          (TH ν P F hF hsmooth v).val.val (TH ν P F hF hsmooth w).val.val := by
  let := C
  exact Classical.choose_spec
    (exists_nativeWeilPeterssonFamily_of_smoothing R hp hg hgenus hΓ hfree hsmooth)

/-- The actual global Bers chart of the canonical native atlas. -/
def nativeWeilPeterssonCoordinateChart (a : TeichmullerSpace.{0,0} R) :
    OpenPartialHomeomorph (TeichmullerSpace.{0,0} R) E := by
  letI := C
  exact chartAt E a

/-- The canonical atlas uses precisely the already constructed Bers coordinate map. -/
theorem nativeWeilPeterssonCoordinateChart_coe (a : TeichmullerSpace.{0,0} R) :
    (nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth a :
      TeichmullerSpace.{0,0} R → E) =
      bersCoordinates R hg hgenus hP hΓ hfree hp := rfl

/-- All charts of this singleton atlas are the same actual Bers chart. -/
theorem nativeWeilPeterssonCoordinateChart_eq (a b : TeichmullerSpace.{0,0} R) :
    nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth a =
      nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth b := rfl

/-- Coordinate tangent vectors use the actual original chart differential. -/
def nativeWeilPeterssonCoordinateEquiv (a : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace TI a ≃L[ℂ] E := by
  letI := C
  exact (canonicalBersTangentEquiv R hg hgenus hP hΓ hfree hp hsmooth a).trans
    (weightedLinearBersCoordinates R hg hgenus hP hΓ hp)

/-- The coordinate equivalence is the actual differential of the unchanged Bers map. -/
theorem nativeWeilPeterssonCoordinateEquiv_apply (a : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v : TangentSpace TI a,
      nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth a v =
        (NormedSpace.fromTangentSpace (bersCoordinates R hg hgenus hP hΓ hfree hp a))
          (mfderiv TI TI (bersCoordinates R hg hgenus hP hΓ hfree hp) a v) := by
  let := C
  exact canonicalBersTangentEquiv_coordinate_apply R hg hgenus hP hΓ hfree hp hsmooth a

/-- First-linear WP coefficients in the actual native Bers chart, with the
Mathlib Core slots exchanged to match the source's convention. -/
def nativeWeilPeterssonLocalCoefficient (a : TeichmullerSpace.{0,0} R)
    (j k : Fin (3*g-3)) (t : E) : ℂ := by
  letI := C
  let q := (nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth a).symm t
  let K := nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth q
  exact (nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth q).inner
    (K.symm (Pi.single k 1)) (K.symm (Pi.single j 1))

/-- The English normalization is twice the real part of the same original
Hermitian form, evaluated on actual inverse-coordinate tangent vectors. -/
def nativeWeilPeterssonRealCoordinatePairing (a : TeichmullerSpace.{0,0} R)
    (v w : E) (t : E) : ℝ := by
  letI := C
  let q := (nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth a).symm t
  let K := nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth q
  exact 2 * ((nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth q).inner
    (K.symm w) (K.symm v)).re

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
