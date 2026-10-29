module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonOriginalCurvature
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRicciExpressionSignDerived
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSectionalExpressionSign

/-!
# Conditional strict signs for the original WP metric

The classical adapter and original mixed/Ricci results supply the
coordinate comparisons below. The independent finite Kähler comparison is
an explicit classical prerequisite; no sign or curvature identity for the
WP metric is added as an assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate ComplexOrder

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport
open LowDimensionalTopology.Unproved.Teichmuller

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "K" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "M" => nativeWeilPeterssonCoefficientMatrix
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "Q" => nativeWeilPeterssonDirectionalRicciExpression
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "S" => nativeWeilPeterssonHolomorphicSectionalExpression
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "Sc" => nativeWeilPeterssonScalarExpression
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp

private theorem wp_classical_ricciQ_eq (x v : E) :
    FiniteKahlerCoordinateContract.ricciQ M x v = Q v x := by
  simp only [FiniteKahlerCoordinateContract.ricciQ, FiniteKahlerCoordinateContract.ricci,
    nativeWeilPeterssonDirectionalRicciExpression, nativeWeilPeterssonRicciExpression,
    nativeWeilPeterssonClassicalMixed_eq R hp hg hgenus hΓ hfree hsmooth]

private theorem wp_classical_scalar_eq (x : E) :
    FiniteKahlerCoordinateContract.bookScalar M x = Sc x := by
  simp only [FiniteKahlerCoordinateContract.bookScalar, FiniteKahlerCoordinateContract.ricci,
    nativeWeilPeterssonScalarExpression, nativeWeilPeterssonRaisedInverseCoefficient,
    nativeWeilPeterssonRicciExpression,
    nativeWeilPeterssonClassicalMixed_eq R hp hg hgenus hΓ hfree hsmooth]

private theorem wp_classical_lowered_eq (x : E) (j k l m : I) :
    FiniteKahlerCoordinateContract.lowered M x j k l m =
      nativeWeilPeterssonLoweredCurvatureExpression
        R hp hg hgenus hΓ hfree hsmooth (basePoint R) j k l m x := by
  simp only [FiniteKahlerCoordinateContract.lowered,
    nativeWeilPeterssonLoweredCurvatureExpression, nativeWeilPeterssonCoefficientMatrix,
    nativeWeilPeterssonClassicalMixed_eq R hp hg hgenus hΓ hfree hsmooth]

private theorem wp_classical_sectional_eq (x v : E) :
    -(FiniteKahlerCoordinateContract.lower4 M x v v v v).re = (S v x).re := by
  simp only [FiniteKahlerCoordinateContract.lower4,
    nativeWeilPeterssonHolomorphicSectionalExpression, Complex.neg_re,
    wp_classical_lowered_eq R hp hg hgenus hΓ hfree hsmooth]

variable (hclassical : FiniteKahlerCoordinateContract.ClassicalFiniteKahlerCoordinateCurvature)

    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hvariation : ∀ ν : Ball Γ, Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      (deformedNativeSurface R hgenus hΓ hp ν)
      (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) (deformedGroup_spec hΓ ν).1
      (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})

include hclassical hWP hvariation hjets

/-- The original-tangent curvature pullback has the actual native mixed
coefficients, by the independent Koszul comparison already adapted to WP. -/
theorem nativeWeilPeterssonOriginalRealCurvature_coordinate
    (q : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ (u v w : TangentSpace RI q) (j : I),
      (K q (nativeWeilPeterssonOriginalRealCurvature
        R hp hg hgenus hΓ hfree hsmooth q u v w)) j =
        ∑ k, ∑ l, ∑ m, nativeWeilPeterssonMixedCurvatureExpression
          R hp hg hgenus hΓ hfree hsmooth (basePoint R) j k l m ((chart (basePoint R)) q) *
          (K q w) k * ((K q u) l * conj ((K q v) m) - (K q v) l * conj ((K q u) m)) := by
  let := C
  intro u v w j
  have hx := (chart (basePoint R)).map_source (mem_chart_source E q)
  simpa only [nativeWeilPeterssonOriginalRealCurvature,
    ContinuousLinearEquiv.apply_symm_apply] using
      nativeWeilPeterssonRealCurvature_eq_nativeMixed_of_classical
        R hp hg hgenus hΓ hfree hsmooth hclassical hWP hvariation hjets
        ((chart (basePoint R)) q) hx (K q u) (K q v) (K q w) j

/-- The three classical normalizations for the SAME actual matrix. All
classical hypotheses are discharged from the original BookKahler inputs. -/
theorem nativeWeilPeterssonClassicalCurvature_normalizations
    (x : E) (hx : x ∈ (chart (basePoint R)).target) :
    (∀ v : E, FiniteKahlerCoordinateContract.realRicci M x v v = 2 * (Q v x).re) ∧
    (FiniteKahlerCoordinateContract.realScalar M x = 2 * (Sc x).re) ∧
    (∀ v : E, v ≠ 0 →
      FiniteKahlerCoordinateContract.metric M x
          (FiniteKahlerCoordinateContract.realCurvature M x v (Complex.I • v)
            (Complex.I • v)) v /
        (FiniteKahlerCoordinateContract.metric M x v v *
          FiniteKahlerCoordinateContract.metric M x (Complex.I • v) (Complex.I • v) -
          (FiniteKahlerCoordinateContract.metric M x v (Complex.I • v)) ^ 2) =
        (S v x).re / (FiniteKahlerCoordinateContract.hermitian M x v v).re ^ 2) := by
  have hbook := nativeWeilPeterssonIsBookKahler_of_harmonicVariation
    R hp hg hgenus hΓ hfree hsmooth hWP hvariation hjets
  have hcyclic (t : E) (ht : t ∈ (chart (basePoint R)).target) (u v w : E) :
      fderiv ℝ (fun y => FiniteKahlerCoordinateContract.omega M y v w) t u -
        fderiv ℝ (fun y => FiniteKahlerCoordinateContract.omega M y u w) t v +
        fderiv ℝ (fun y => FiniteKahlerCoordinateContract.omega M y u v) t w = 0 := by
    exact wp_classical_cyclic_of_closed R hp hg hgenus hΓ hfree hsmooth
      hWP t ht (hbook.2.2.2.2.2.2.2 t ht) u v w
  have h := hclassical (3*g-3) (chart (basePoint R)).target M
    (chart (basePoint R)).open_target
    (contDiffOn_nativeWeilPeterssonClassicalMatrix R hp hg hgenus hΓ hfree hsmooth hWP)
    (fun t _ => nativeWeilPeterssonCoefficientMatrix_posDef
      R hp hg hgenus hΓ hfree hsmooth (basePoint R) t) hcyclic
  rcases h.2 x hx with ⟨_, _, _, _, _, _, hRic, hScalar, hPlane⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v
    simpa only [wp_classical_ricciQ_eq R hp hg hgenus hΓ hfree hsmooth] using (hRic v).2
  · simpa only [wp_classical_scalar_eq R hp hg hgenus hΓ hfree hsmooth] using hScalar.2
  · intro v hv
    simpa only [wp_classical_sectional_eq R hp hg hgenus hΓ hfree hsmooth] using hPlane v hv

/-- The source directional Ricci is the real Ricci divided by the SAME real
metric; the factors two cancel and no unit-vector assumption is needed. -/
theorem nativeWeilPeterssonBookDirectionalRicci_eq_expression
    (q : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v : TangentSpace RI q,
      nativeWeilPeterssonBookDirectionalRicci R hp hg hgenus hΓ hfree hsmooth q v =
        (Q (K q v) ((chart (basePoint R)) q)).re /
          (FiniteKahlerCoordinateContract.hermitian M ((chart (basePoint R)) q)
            (K q v) (K q v)).re := by
  let := C
  intro v
  have hx := (chart (basePoint R)).map_source (mem_chart_source E q)
  have h := (nativeWeilPeterssonClassicalCurvature_normalizations
    R hp hg hgenus hΓ hfree hsmooth hclassical hWP hvariation hjets _ hx).1 (K q v)
  unfold nativeWeilPeterssonBookDirectionalRicci nativeWeilPeterssonOriginalRealRicci
  rw [h, ← nativeWeilPeterssonClassicalMetric_eq_original]
  unfold FiniteKahlerCoordinateContract.metric
  simp only [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- The English scalar is the real inverse-metric trace divided by two. -/
theorem nativeWeilPeterssonBookScalar_eq_expression (q : TeichmullerSpace.{0,0} R) :
    nativeWeilPeterssonBookScalar R hp hg hgenus hΓ hfree hsmooth q =
      (Sc ((chart (basePoint R)) q)).re := by
  let := C
  have hx := (chart (basePoint R)).map_source (mem_chart_source E q)
  have h := (nativeWeilPeterssonClassicalCurvature_normalizations
    R hp hg hgenus hΓ hfree hsmooth hclassical hWP hvariation hjets _ hx).2.1
  unfold nativeWeilPeterssonBookScalar nativeWeilPeterssonOriginalRealScalar
  rw [h]
  ring

/-- The actual original J-plane quotient is the normalized quartic with its
whole-conjugate lowered coefficient and last-slot interchange unchanged. -/
theorem nativeWeilPeterssonBookHolomorphicSectional_eq_expression
    (q : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ (v : TangentSpace RI q), v ≠ 0 →
      nativeWeilPeterssonBookHolomorphicSectional R hp hg hgenus hΓ hfree hsmooth q v =
        (S (K q v) ((chart (basePoint R)) q)).re /
          (FiniteKahlerCoordinateContract.hermitian M ((chart (basePoint R)) q)
            (K q v) (K q v)).re ^ 2 := by
  let := C
  intro v hv
  have hx := (chart (basePoint R)).map_source (mem_chart_source E q)
  rw [nativeWeilPeterssonBookHolomorphicSectional_eq_coordinate]
  exact (nativeWeilPeterssonClassicalCurvature_normalizations
    R hp hg hgenus hΓ hfree hsmooth hclassical hWP hvariation hjets _ hx).2.2
      (K q v) ((K q).toLinearEquiv.map_ne_zero_iff.mpr hv)

variable (hPV : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation

      R hp hg hgenus hΓ hfree hsmooth)
    (hDiag : Unproved.Teichmuller.WeilPeterssonDiagonalKernelControl
      R hp hg hgenus hΓ hfree hsmooth)

include hPV hDiag

/-- All three strict curvature signs on the fixed original compact Type-0 reference
surface: all three strict signs, under the old analytic inputs and only the
independent book-external finite Kähler comparison. -/
theorem nativeWeilPeterssonBookCurvatures_strictly_negative
    (q : TeichmullerSpace.{0,0} R) :
    letI := C
    (nativeWeilPeterssonBookScalar R hp hg hgenus hΓ hfree hsmooth q < 0) ∧
    ∀ v : TangentSpace RI q, v ≠ 0 →
      nativeWeilPeterssonBookDirectionalRicci R hp hg hgenus hΓ hfree hsmooth q v < 0 ∧
      nativeWeilPeterssonBookHolomorphicSectional R hp hg hgenus hΓ hfree hsmooth q v < 0 := by
  let := C
  obtain ⟨ν, hν⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp q
  have hpoint : β ν.val = q :=
    (coefficientProjection_ball R hg hgenus hΓ hfree hp ν).trans hν
  obtain ⟨P, F, hF⟩ := exists_deformedHalfPlaneFundamentalRegion R hgenus hΓ hp ν
  have hscalar : (Sc ((chart (basePoint R)) q)).re < 0 := by
    rw [← hpoint]
    exact nativeWeilPeterssonScalarExpression_re_neg_derived
      R hp hg hgenus hΓ hfree hsmooth (basePoint R) ν P F hF hPV hDiag
  refine ⟨?_, ?_⟩
  · rw [nativeWeilPeterssonBookScalar_eq_expression
      R hp hg hgenus hΓ hfree hsmooth hclassical hWP hvariation hjets]
    exact hscalar
  · intro v hv
    have hv' : K q v ≠ 0 := (K q).toLinearEquiv.map_ne_zero_iff.mpr hv
    have hricci : (Q (K q v) ((chart (basePoint R)) q)).re < 0 := by
      have h := nativeWeilPeterssonDirectionalRicciExpression_re_neg_derived
        R hp hg hgenus hΓ hfree hsmooth (basePoint R) ν P F hF hPV hDiag (K q v) hv'
      simpa only [hpoint] using h
    have hsectional : (S (K q v) ((chart (basePoint R)) q)).re < 0 := by
      have h := nativeWeilPeterssonSectionalExpression_re_neg
        R hp hg hgenus hΓ hfree hsmooth hPV (basePoint R) ν P F hF hDiag (K q v) hv'
      simpa only [hpoint] using h
    have hh : 0 < (FiniteKahlerCoordinateContract.hermitian M
        ((chart (basePoint R)) q) (K q v) (K q v)).re := by
      have hpmetric := nativeWeilPeterssonRealTangentForm_pos
        R hp hg hgenus hΓ hfree hsmooth q v hv
      rw [← nativeWeilPeterssonClassicalMetric_eq_original] at hpmetric
      unfold FiniteKahlerCoordinateContract.metric at hpmetric
      linarith
    constructor
    · rw [nativeWeilPeterssonBookDirectionalRicci_eq_expression
        R hp hg hgenus hΓ hfree hsmooth hclassical hWP hvariation hjets]
      exact div_neg_of_neg_of_pos hricci hh
    · rw [nativeWeilPeterssonBookHolomorphicSectional_eq_expression
        R hp hg hgenus hΓ hfree hsmooth hclassical hWP hvariation hjets q v hv]
      exact div_neg_of_neg_of_pos hsectional (pow_pos hh 2)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
