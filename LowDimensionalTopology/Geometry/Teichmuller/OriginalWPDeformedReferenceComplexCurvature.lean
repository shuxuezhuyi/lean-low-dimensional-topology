module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalWPDeformedReferenceRealCurvature
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonClassicalCurvatureAdapter
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSourceKernels

/-!
# Finite complex extraction under the actual reference change

The existing classical mixed-coordinate comparison recovers the complex
lowered contraction from four real metric-curvature pairings. The actual
inverse coordinate map transports closedness of the fixed original form,
so the original variation family suffices on the actual target as well.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport
open Unproved.Teichmuller

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "hP" => canonicalHandleGroupPresentation g
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "U" => PartialEquiv.target (PartialHomeomorph.toPartialEquiv
  (OpenPartialHomeomorph.toPartialHomeomorph (chart (basePoint R))))
local notation "M" => nativeWeilPeterssonCoefficientMatrix
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "C4" => nativeWeilPeterssonLoweredContraction
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

private theorem native_finite_hermitian_conj (t u v : E) :
    conj (FiniteKahlerCoordinateContract.hermitian M t u v) =
      FiniteKahlerCoordinateContract.hermitian M t v u := by
  unfold FiniteKahlerCoordinateContract.hermitian nativeWeilPeterssonCoefficientMatrix
  simp only [map_sum, map_mul, nativeWeilPeterssonLocalCoefficient_conj,
    Complex.conj_conj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem native_finite_hermitian_I_right (t u v : E) :
    FiniteKahlerCoordinateContract.hermitian M t u (Complex.I • v) =
      -Complex.I * FiniteKahlerCoordinateContract.hermitian M t u v := by
  unfold FiniteKahlerCoordinateContract.hermitian
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem native_finite_hermitian_from_metric (t u v : E) :
    FiniteKahlerCoordinateContract.hermitian M t u v =
      ((FiniteKahlerCoordinateContract.metric M t v u : ℂ) -
        Complex.I * (FiniteKahlerCoordinateContract.metric M t v (Complex.I • u) : ℂ)) / 2 := by
  have hc := (native_finite_hermitian_conj R hp hg hgenus hΓ hfree hsmooth t u v).symm
  simp only [FiniteKahlerCoordinateContract.metric,
    native_finite_hermitian_I_right, hc]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem native_lower4_eq (t u v w s : E) :
    FiniteKahlerCoordinateContract.lower4 M t u v w s = C4 u v w s t := by
  simp only [FiniteKahlerCoordinateContract.lower4, FiniteKahlerCoordinateContract.lowered,
    nativeWeilPeterssonLoweredContraction, nativeWeilPeterssonLoweredCurvatureExpression,
    nativeWeilPeterssonCoefficientMatrix,
    nativeWeilPeterssonClassicalMixed_eq R hp hg hgenus hΓ hfree hsmooth]

private theorem native_lower4_I_last (t p w u v : E) :
    FiniteKahlerCoordinateContract.lower4 M t p w u (Complex.I • v) =
      -Complex.I * FiniteKahlerCoordinateContract.lower4 M t p w u v := by
  unfold FiniteKahlerCoordinateContract.lower4
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

private theorem native_lower4_I_third (t p w u v : E) :
    FiniteKahlerCoordinateContract.lower4 M t p w (Complex.I • u) v =
      Complex.I * FiniteKahlerCoordinateContract.lower4 M t p w u v := by
  unfold FiniteKahlerCoordinateContract.lower4
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

private theorem native_curvature_pairing_difference (t : E)
    (hcurv : ∀ (u v w : E) (j : I),
      FiniteKahlerCoordinateContract.realCurvature M t u v w j =
        ∑ k, ∑ l, ∑ m, FiniteKahlerCoordinateContract.mixed M t j k l m * w k *
          (u l * conj (v m) - v l * conj (u m))) (p u v w : E) :
    FiniteKahlerCoordinateContract.hermitian M t p
        (FiniteKahlerCoordinateContract.realCurvature M t u v w) =
      FiniteKahlerCoordinateContract.lower4 M t p w u v -
        FiniteKahlerCoordinateContract.lower4 M t p w v u := by
  classical
  have hswap (r : I) : FiniteKahlerCoordinateContract.realCurvature M t u v w r =
      ∑ k, ∑ l, ∑ m, FiniteKahlerCoordinateContract.mixed M t r k m l * w k *
        (u m * conj (v l) - v m * conj (u l)) := by
    rw [hcurv]
    apply Finset.sum_congr rfl
    intro k _
    exact Finset.sum_comm
  calc
    _ = ∑ j, ∑ r, ∑ k, ∑ l, ∑ m,
        p j * M t j r * conj (FiniteKahlerCoordinateContract.mixed M t r k m l) *
          conj (w k) * (conj (u m) * v l - conj (v m) * u l) := by
      unfold FiniteKahlerCoordinateContract.hermitian
      simp only [hswap, map_sum, map_mul, map_sub, Complex.conj_conj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = ∑ j, ∑ k, ∑ l, ∑ m, ∑ r,
        p j * M t j r * conj (FiniteKahlerCoordinateContract.mixed M t r k m l) *
          conj (w k) * (conj (u m) * v l - conj (v m) * u l) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ k, ∑ l, ∑ m,
        (FiniteKahlerCoordinateContract.lowered M t j k l m * p j * conj (w k) *
          u l * conj (v m) -
        FiniteKahlerCoordinateContract.lowered M t j k l m * p j * conj (w k) *
          v l * conj (u m)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro m _
      unfold FiniteKahlerCoordinateContract.lowered
      simp only [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      simp only [FiniteKahlerCoordinateContract.lower4, Finset.sum_sub_distrib]

private theorem native_C4_from_real_curvature (t : E)
    (hcurv : ∀ (u v w : E) (j : I),
      FiniteKahlerCoordinateContract.realCurvature M t u v w j =
        ∑ k, ∑ l, ∑ m, FiniteKahlerCoordinateContract.mixed M t j k l m * w k *
          (u l * conj (v m) - v l * conj (u m))) (u v w s : E) :
    C4 u v w s t =
      ((FiniteKahlerCoordinateContract.metric M t
          (FiniteKahlerCoordinateContract.realCurvature M t w s v) u : ℂ) -
        Complex.I * (FiniteKahlerCoordinateContract.metric M t
          (FiniteKahlerCoordinateContract.realCurvature M t w s v) (Complex.I • u) : ℂ) +
        Complex.I * (FiniteKahlerCoordinateContract.metric M t
          (FiniteKahlerCoordinateContract.realCurvature M t w (Complex.I • s) v) u : ℂ) +
        (FiniteKahlerCoordinateContract.metric M t
          (FiniteKahlerCoordinateContract.realCurvature M t w (Complex.I • s) v)
          (Complex.I • u) : ℂ)) / 4 := by
  have hd := native_curvature_pairing_difference R hp hg hgenus hΓ hfree hsmooth
    t hcurv u w s v
  have hi := native_curvature_pairing_difference R hp hg hgenus hΓ hfree hsmooth
    t hcurv u w (Complex.I • s) v
  rw [native_lower4_I_last, native_lower4_I_third] at hi
  rw [← native_lower4_eq R hp hg hgenus hΓ hfree hsmooth t u v w s]
  calc
    _ = (FiniteKahlerCoordinateContract.hermitian M t u
        (FiniteKahlerCoordinateContract.realCurvature M t w s v) +
      Complex.I * FiniteKahlerCoordinateContract.hermitian M t u
        (FiniteKahlerCoordinateContract.realCurvature M t w (Complex.I • s) v)) / 2 := by
      rw [hd, hi]
      ring_nf
      rw [Complex.I_sq]
      ring
    _ = _ := by
      rw [native_finite_hermitian_from_metric R hp hg hgenus hΓ hfree hsmooth t u,
        native_finite_hermitian_from_metric R hp hg hgenus hΓ hfree hsmooth t u]
      ring_nf
      rw [Complex.I_sq]
      ring

variable (ν : Ball Γ)

local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "chartY" => nativeWeilPeterssonCoordinateChart Y hpY hg hY hΔ hfY hsmooth
local notation "UY" => PartialEquiv.target (PartialHomeomorph.toPartialEquiv
  (OpenPartialHomeomorph.toPartialHomeomorph (chartY (basePoint Y))))
local notation "MY" => nativeWeilPeterssonCoefficientMatrix
  Y hpY hg hY hΔ hfY hsmooth (basePoint Y)
local notation "ΩY" => nativeWeilPeterssonFundamentalRealCoordinateForm
  Y hpY hg hY hΔ hfY hsmooth (basePoint Y)
local notation "C4Y" => nativeWeilPeterssonLoweredContraction
  Y hpY hg hY hΔ hfY hsmooth (basePoint Y)
local notation "f" => deformedReferenceWeilPeterssonCoordinateMap R hp hg hgenus hΓ ν
local notation "q" => deformedReferenceWeilPeterssonInverseCoordinateMap R hp hg hgenus hΓ ν
local notation "x" => BC (β ν.val)
local notation "J" => fderiv ℝ f x

private theorem actual_inverse_form (y : E) (hy : y ∈ UY) :
    ΩY y = (Ω (q y)).compContinuousLinearMap (fderiv ℝ q y) := by
  obtain ⟨_, hqU, _, hfq⟩ := deformedReferenceWeilPeterssonCoordinateMap_domains
    R hp hg hgenus hΓ hfree hsmooth ν
  have ha := deformedReferenceWeilPeterssonCoordinateMap_analytic
    R hp hg hgenus hΓ hfree hsmooth ν
  have hevent : (fun z => f (q z)) =ᶠ[𝓝 y] id := by
    filter_upwards [(chartY (basePoint Y)).open_target.mem_nhds hy] with z hz
    exact hfq z hz
  have hD := hevent.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp y ((ha.1 _ (hqU hy)).differentiableAt.restrictScalars ℝ)
    ((ha.2 _ hy).differentiableAt.restrictScalars ℝ), fderiv_id] at hD
  have hpoint : BC ((chart (basePoint R)).symm (q y)) = q y := by
    simpa only [nativeWeilPeterssonCoordinateChart_coe] using
      (chart (basePoint R)).right_inv (hqU hy)
  have hform := nativeWeilPeterssonCoordinateForm_deformedReference_allPoints_pullback
    R hp hg hgenus hΓ hfree hsmooth ν ((chart (basePoint R)).symm (q y))
  rw [hpoint, hfq y hy] at hform
  rw [hform]
  apply ContinuousAlternatingMap.ext
  intro v
  change ΩY y v = ΩY y (fun i => fderiv ℝ f (q y) (fderiv ℝ q y (v i)))
  congr 1
  funext i
  exact (congrArg (fun L : E →L[ℝ] E => L (v i)) hD).symm

variable
    (hWP : WeilPeterssonLocalCoefficientSmoothness R hp hg hgenus hΓ hfree hsmooth)
    (hvariation : ∀ μ : Ball Γ, WeilPeterssonHarmonicIntegralFirstVariation
      (deformedNativeSurface R hgenus hΓ hp μ)
      (deformedNativeSurface_uniformization R hgenus hΓ hp μ) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp μ) (deformedGroup_spec hΓ μ).1
      (deformedNativeSurface_actsFreely R hgenus hΓ hp μ) hsmooth)
    (hjets : CanonicalHarmonicEichlerJets.{0})

include hWP hvariation hjets in
private theorem actual_deformed_coordinate_form_closed :
    ∀ y ∈ UY, extDerivWithin ΩY UY y = 0 := by
  have hbook := nativeWeilPeterssonIsBookKahler_of_harmonicVariation
    R hp hg hgenus hΓ hfree hsmooth hWP hvariation hjets
  have hclosed (t : E) (ht : t ∈ U) : extDeriv Ω t = 0 := by
    simpa only [extDerivWithin, extDeriv,
      fderivWithin_of_isOpen (chart (basePoint R)).open_target ht] using
        hbook.2.2.2.2.2.2.2 t ht
  intro y hy
  have ha := deformedReferenceWeilPeterssonCoordinateMap_analytic
    R hp hg hgenus hΓ hfree hsmooth ν
  have hqU := (deformedReferenceWeilPeterssonCoordinateMap_domains
    R hp hg hgenus hΓ hfree hsmooth ν).2.1
  have hq : ContDiffAt ℝ ∞ q y := (ha.2 y hy).restrictScalars.contDiffAt
  have hΩ : DifferentiableAt ℝ Ω (q y) :=
    ((contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
      R hp hg hgenus hΓ hfree hsmooth hWP (basePoint R)).contDiffAt
        ((chart (basePoint R)).open_target.mem_nhds (hqU hy))).differentiableAt (by simp)
  have hevent : ΩY =ᶠ[𝓝 y]
      (fun z => (Ω (q z)).compContinuousLinearMap (fderiv ℝ q z)) := by
    filter_upwards [(chartY (basePoint Y)).open_target.mem_nhds hy] with z hz
    exact actual_inverse_form R hp hg hgenus hΓ hfree hsmooth ν z hz
  have hz : extDeriv ΩY y = 0 := calc
    _ = extDeriv (fun z => (Ω (q z)).compContinuousLinearMap (fderiv ℝ q z)) y :=
      hevent.extDeriv_eq
    _ = (extDeriv Ω (q y)).compContinuousLinearMap (fderiv ℝ q y) :=
      extDeriv_pullback hΩ hq (by simp)
    _ = 0 := by
      rw [hclosed _ (hqU hy)]
      apply ContinuousAlternatingMap.ext
      intro v
      simp
  simpa only [extDerivWithin, extDeriv,
    fderivWithin_of_isOpen (chartY (basePoint Y)).open_target hy] using hz

include hsmooth in
private theorem actual_reference_derivative_I (v : E) :
    J (Complex.I • v) = Complex.I • J v := by
  have hx : x ∈ U := by
    rw [nativeWeilPeterssonCoordinateChart_target_eq_range]
    exact mem_range_self _
  have hd := ((deformedReferenceWeilPeterssonCoordinateMap_analytic
    R hp hg hgenus hΓ hfree hsmooth ν).1 _ hx).differentiableAt
  rw [hd.fderiv_restrictScalars (𝕜 := ℝ)]
  exact (fderiv ℂ f x).map_smul Complex.I v

/-- The unchanged full complex lowered contraction is covariant under the
actual reference map, conditional only on the original analytic family and
the independent concrete classical real-curvature naturality obligation. -/
theorem nativeWeilPeterssonLoweredContraction_deformedReference
    (hWP : WeilPeterssonLocalCoefficientSmoothness R hp hg hgenus hΓ hfree hsmooth)
    (hvariation : ∀ μ : Ball Γ, WeilPeterssonHarmonicIntegralFirstVariation
      (deformedNativeSurface R hgenus hΓ hp μ)
      (deformedNativeSurface_uniformization R hgenus hΓ hp μ) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp μ) (deformedGroup_spec hΓ μ).1
      (deformedNativeSurface_actsFreely R hgenus hΓ hp μ) hsmooth)
    (hjets : CanonicalHarmonicEichlerJets.{0})
    (hclassical : FiniteKahlerCoordinateContract.ClassicalFiniteKahlerCoordinateCurvature)
    (hnat : WeilPeterssonDeformedReferenceRealCurvatureNaturality
      R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (u v w s : E) :
    nativeWeilPeterssonLoweredContraction R hp hg hgenus hΓ hfree hsmooth
        a u v w s x = C4Y (J u) (J v) (J w) (J s) 0 := by
  change C4 u v w s x = _
  have hx : x ∈ U := by
    rw [nativeWeilPeterssonCoordinateChart_target_eq_range]
    exact mem_range_self _
  have h0 : (0 : E) ∈ UY := by
    rw [nativeWeilPeterssonCoordinateChart_target_eq_range]
    exact ⟨basePoint Y, bersCoordinates_basePoint Y hg hY hP hΔ hfY hpY⟩
  have hR (b c d : E) (j : I) :=
    nativeWeilPeterssonRealCurvature_eq_nativeMixed_of_classical
      R hp hg hgenus hΓ hfree hsmooth hclassical hWP hvariation hjets x hx b c d j
  simp only [← nativeWeilPeterssonClassicalMixed_eq R hp hg hgenus hΓ hfree hsmooth] at hR
  have htransport := nativeWeilPeterssonDeformedReference_loweredRealCurvature
    R hp hg hgenus hΓ hfree hsmooth ν hWP hnat
  have hclosedY := actual_deformed_coordinate_form_closed
    R hp hg hgenus hΓ hfree hsmooth ν hWP hvariation hjets
  have hcyclicY (y : E) (hy : y ∈ UY) (b c d : E) :=
    wp_classical_cyclic_of_closed Y hpY hg hY hΔ hfY hsmooth htransport.1
      y hy (hclosedY y hy) b c d
  have hYclass := hclassical (3 * g - 3) UY MY (chartY (basePoint Y)).open_target
    (contDiffOn_nativeWeilPeterssonClassicalMatrix Y hpY hg hY hΔ hfY hsmooth htransport.1)
    (fun y _ => nativeWeilPeterssonCoefficientMatrix_posDef
      Y hpY hg hY hΔ hfY hsmooth (basePoint Y) y) hcyclicY
  have hYcurv := (hYclass.2 0 h0).2.2.2.2.1
  rw [native_C4_from_real_curvature R hp hg hgenus hΓ hfree hsmooth x hR,
    native_C4_from_real_curvature Y hpY hg hY hΔ hfY hsmooth 0 hYcurv]
  simp_rw [htransport.2, actual_reference_derivative_I R hp hg hgenus hΓ hfree hsmooth ν]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
