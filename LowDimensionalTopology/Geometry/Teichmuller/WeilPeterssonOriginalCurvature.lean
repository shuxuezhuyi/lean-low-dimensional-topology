module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonClassicalCurvatureAdapter
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothRealMetric

/-!
# Independent Koszul curvature on the original WP tangent fibres

The following objects use the actual original WP tangent fibres.
The coordinate curvature is defined independently from the real metric by
Koszul and its commutator. We pull it back by the actual real Bers differential.
The metric comparison below identifies that coordinate metric with the original
WP real tangent form, retaining the English normalization `g = 2 Re h`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Bundle
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami
open LowDimensionalTopology.Unproved.Teichmuller

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "K" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "M" => nativeWeilPeterssonCoefficientMatrix
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "B" => nativeWeilPeterssonRealTangentForm R hp hg hgenus hΓ hfree hsmooth

/-- The independent coordinate metric equals the accepted whole WP operator. -/
theorem nativeWeilPeterssonClassicalMetric_eq_operator (x u v : E) :
    FiniteKahlerCoordinateContract.metric M x u v = nativeWeilPeterssonRealCoordinateOperator
      R hp hg hgenus hΓ hfree hsmooth (basePoint R) x u v := by
  rw [nativeWeilPeterssonRealCoordinateOperator_apply,
    nativeWeilPeterssonRealCoordinatePairing_eq_sum]
  unfold FiniteKahlerCoordinateContract.metric FiniteKahlerCoordinateContract.hermitian
  apply congrArg (fun z : ℂ => 2 * z.re)
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change u j * M x j k * conj (v k) = u j * conj (v k) * M x j k
  ring

/-- This is the same original twice-real-part metric at every original point.
The singleton Bers atlas is global; no mapping-class transitivity is used. -/
theorem nativeWeilPeterssonClassicalMetric_eq_original
    (q : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v w : TangentSpace RI q,
      FiniteKahlerCoordinateContract.metric M ((chart (basePoint R)) q) (K q v) (K q w) = B q v w := by
  let := C
  intro v w
  have hq : q ∈ (chart (basePoint R)).source := mem_chart_source E q
  rw [nativeWeilPeterssonClassicalMetric_eq_operator,
    nativeWeilPeterssonRealCoordinateOperator_eq_modelForm,
    (chart (basePoint R)).left_inv hq]
  rfl

/-- The comparison also evaluates the already accepted smooth metric object. -/
theorem nativeWeilPeterssonClassicalMetric_eq_smoothMetric
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) (q : TeichmullerSpace.{0,0} R) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) :=
      Topology.IsOpenEmbedding.isManifold_singleton (I := RI) (n := ω)
        (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
          (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)
    ∀ v w : TangentSpace RI q,
      FiniteKahlerCoordinateContract.metric M ((chart (basePoint R)) q) (K q v) (K q w) =
        (nativeWeilPeterssonSmoothRealMetric R hp hg hgenus hΓ hfree hsmooth hWP).inner q v w := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) :=
    Topology.IsOpenEmbedding.isManifold_singleton (I := RI) (n := ω)
      (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)
  intro v w
  change FiniteKahlerCoordinateContract.metric M ((chart (basePoint R)) q) (K q v) (K q w) =
    B q v w
  exact nativeWeilPeterssonClassicalMetric_eq_original R hp hg hgenus hΓ hfree hsmooth q v w

/-- The original complex structure, using the same actual real coordinates. -/
def nativeWeilPeterssonOriginalJ (q : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace RI q → TangentSpace RI q := by
  let := C
  exact fun v => (K q).symm (Complex.I • K q v)

/-- This J is the original complex structure under the accepted same-point
realification; the complex Bers differential is complex linear. -/
theorem nativeWeilPeterssonOriginalJ_realification (q : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v : TangentSpace RI q,
      nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth q
          (nativeWeilPeterssonOriginalJ R hp hg hgenus hΓ hfree hsmooth q v) =
        Complex.I • nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth q v := by
  let := C
  intro v
  apply (nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth q).injective
  rw [map_smul]
  change K q ((K q).symm (Complex.I • K q v)) = Complex.I • K q v
  exact (K q).apply_symm_apply _

/-- Pullback of the independent real Koszul commutator by the actual Bers
differential, on the original real tangent carrier. -/
def nativeWeilPeterssonOriginalRealCurvature (q : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace RI q → TangentSpace RI q → TangentSpace RI q → TangentSpace RI q := by
  let := C
  exact fun u v w => (K q).symm
    (FiniteKahlerCoordinateContract.realCurvature M ((chart (basePoint R)) q) (K q u) (K q v) (K q w))

/-- The ordinary real trace of `z ↦ R(z,u)v` in the inverse-coordinate real
basis `K⁻¹ e_j, K⁻¹ (i e_j)`, with its actual dual coordinate functionals. -/
def nativeWeilPeterssonOriginalRealRicci (q : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace RI q → TangentSpace RI q → ℝ := by
  let := C
  exact fun u v => FiniteKahlerCoordinateContract.realRicci M ((chart (basePoint R)) q) (K q u) (K q v)

/-- This Ricci is the real trace of the actual pulled-back curvature in the
inverse-coordinate real basis; no orthonormal-coordinate premise occurs. -/
theorem nativeWeilPeterssonOriginalRealRicci_eq_trace
    (q : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ u v : TangentSpace RI q,
      nativeWeilPeterssonOriginalRealRicci R hp hg hgenus hΓ hfree hsmooth q u v =
        ∑ j, (((K q (nativeWeilPeterssonOriginalRealCurvature
            R hp hg hgenus hΓ hfree hsmooth q ((K q).symm (Pi.single j 1)) u v)) j).re +
          ((K q (nativeWeilPeterssonOriginalRealCurvature
            R hp hg hgenus hΓ hfree hsmooth q
              ((K q).symm (Complex.I • (Pi.single j 1 : E))) u v)) j).im) := by
  let := C
  intro u v
  simp only [nativeWeilPeterssonOriginalRealRicci,
    FiniteKahlerCoordinateContract.realRicci, FiniteKahlerCoordinateContract.basis,
    nativeWeilPeterssonOriginalRealCurvature, ContinuousLinearEquiv.apply_symm_apply]

/-- English directional Ricci curvature, normalized for arbitrary directions. -/
def nativeWeilPeterssonBookDirectionalRicci (q : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace RI q → ℝ := by
  let := C
  exact fun v => nativeWeilPeterssonOriginalRealRicci
    R hp hg hgenus hΓ hfree hsmooth q v v / B q v v

/-- The full real scalar is the inverse metric trace of the independent real
Ricci tensor; its coordinate definition uses real metric duality. -/
def nativeWeilPeterssonOriginalRealScalar (q : TeichmullerSpace.{0,0} R) : ℝ :=
  FiniteKahlerCoordinateContract.realScalar M ((chart (basePoint R)) q)

/-- The normalized scalar is half the full real scalar for `g = 2 Re h`. -/
def nativeWeilPeterssonBookScalar (q : TeichmullerSpace.{0,0} R) : ℝ :=
  nativeWeilPeterssonOriginalRealScalar R hp hg hgenus hΓ hfree hsmooth q / 2

/-- Actual real J-plane quotient, with the original real tangent metric and
the independently defined pulled-back Koszul curvature in its numerator. -/
def nativeWeilPeterssonBookHolomorphicSectional (q : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace RI q → ℝ := by
  let := C
  let J := nativeWeilPeterssonOriginalJ R hp hg hgenus hΓ hfree hsmooth q
  let Rm := nativeWeilPeterssonOriginalRealCurvature R hp hg hgenus hΓ hfree hsmooth q
  exact fun v => B q (Rm v (J v) (J v)) v /
    (B q v v * B q (J v) (J v) - (B q v (J v)) ^ 2)

/-- The native J-plane quotient is exactly that of the independent coordinate
metric and Koszul commutator, before invoking any Kähler comparison. -/
theorem nativeWeilPeterssonBookHolomorphicSectional_eq_coordinate
    (q : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v : TangentSpace RI q,
      nativeWeilPeterssonBookHolomorphicSectional R hp hg hgenus hΓ hfree hsmooth q v =
        FiniteKahlerCoordinateContract.metric M ((chart (basePoint R)) q)
          (FiniteKahlerCoordinateContract.realCurvature M ((chart (basePoint R)) q)
            (K q v) (Complex.I • K q v) (Complex.I • K q v)) (K q v) /
        (FiniteKahlerCoordinateContract.metric M ((chart (basePoint R)) q) (K q v) (K q v) *
          FiniteKahlerCoordinateContract.metric M ((chart (basePoint R)) q) (Complex.I • K q v) (Complex.I • K q v) -
          (FiniteKahlerCoordinateContract.metric M ((chart (basePoint R)) q) (K q v) (Complex.I • K q v)) ^ 2) := by
  let := C
  intro v
  unfold nativeWeilPeterssonBookHolomorphicSectional
  simp only [← nativeWeilPeterssonClassicalMetric_eq_original,
    nativeWeilPeterssonOriginalJ, nativeWeilPeterssonOriginalRealCurvature,
    ContinuousLinearEquiv.apply_symm_apply]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
