module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHorizontalCoefficientIntegral
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHalfPlaneCoverArea
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticPointwisePairing
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.PoincareLineElement
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Ring

/-!
# The original horizontal integral on the same fundamental region

The actual original quadratic coefficient pulls back to the existing
height-weighted quadratic pairing along the same specified covering. The
canonical covering density cancels the two actual quadratic derivative factors.
The prescribed area pushforward then identifies the two literal integrals.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Hyperbolic Fuchsian AtlasMetricConstruction

variable {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The canonical real action on the unchanged original symmetric-tensor submodule. -/
local instance canonicalHorizontalFundamentalTensorSMul :
    SMul ℝ (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact Submodule.smul (symmetricTwoTensorSubmodule R)

private theorem discCover_density_mul_coverCoordinate_norm_sq
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : letI := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.IsUniformization Γ M.halfPlaneCover) (z : ℍ) :
    letI := R.toRiemannAtlas.toChartedSpace
    let e := chosenChart R.toRiemannSurface (M.halfPlaneCover z)
    let h : ℂ → ℂ := fun w => e.val (LiZhongQC.utm_pext M.halfPlaneCover w)
    (discCoverAtlasInducedMetric M).density e (M.halfPlaneCover z) *
      ‖deriv h (z : ℂ)‖ ^ 2 = 1 / z.im ^ 2 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let p := M.halfPlaneCover
  let x := p z
  let e := chosenChart R.toRiemannSurface x
  let h : ℂ → ℂ := fun w => e.val (LiZhongQC.utm_pext p w)
  let a := discFiniteHomeomorph.symm (halfPlaneToDisc z)
  have hpa : M.discCover a = x := rfl
  obtain ⟨l, hla, hl⟩ := M.discCover_covering.isLocalHomeomorph a
  have hxE : x ∈ e.val.source := mem_chart_source ℂ x
  have hxL : x ∈ l.target := by
    have he : l a = x := (congrFun hl a).symm.trans hpa
    exact he ▸ l.map_source hla
  let T := discCoverSheetCoordinate e l
  have hxT : e.val x ∈ T.source := by
    change (e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ l.target) ∧
      l.symm (e.val.symm (e.val x)) ∈ discFiniteChart.source
    rw [e.val.left_inv hxE, discFiniteChart_source]
    exact ⟨⟨e.val.map_source hxE, hxL⟩, mem_univ _⟩
  have hpext : LiZhongQC.utm_pext p (z : ℂ) = x := by
    simpa only [UpperHalfPlane.ofComplex_apply] using LiZhongQC.utm_a_pext_eq p z.im_pos
  have hhz : h (z : ℂ) = e.val x := congrArg e.val hpext
  have hT : DifferentiableAt ℂ T (e.val x) :=
    (discCoverSheetCoordinate_analytic M e l hl (e.val x) hxT).differentiableAt
  have hh : DifferentiableAt ℂ h (z : ℂ) := by
    apply LiZhongQC.utm_a_differentiableAt hp.2.1 x z.im_pos
    rw [hpext]
    exact hxE
  let d : ℂ → extendedUnitDisc := fun w =>
    discFiniteHomeomorph.symm (halfPlaneToDisc (UpperHalfPlane.ofComplex w))
  have hdz : d (z : ℂ) = a := by
    simp only [d, a, UpperHalfPlane.ofComplex_apply]
  have hd : ContinuousAt d (z : ℂ) :=
    discFiniteHomeomorph.symm.continuous.continuousAt.comp
      (cayleyHomeomorph.continuous.continuousAt.comp
        (UpperHalfPlane.mdifferentiableAt_ofComplex z.im_pos).continuousAt)
  have hdmem : ∀ᶠ w in 𝓝 (z : ℂ), d w ∈ l.source := by
    apply hd.eventually_mem
    rw [hdz]
    exact l.open_source.mem_nhds hla
  have hpmem : ∀ᶠ w in 𝓝 (z : ℂ), LiZhongQC.utm_pext p w ∈ e.val.source := by
    apply (LiZhongQC.utm_a_continuousAt hp.1.continuous z.im_pos).eventually_mem
    rw [hpext]
    exact e.val.open_source.mem_nhds hxE
  have hnear : (T : ℂ → ℂ) ∘ h =ᶠ[𝓝 (z : ℂ)] cayleyFormula := by
    filter_upwards [LiZhongQC.isOpen_upperHalf.mem_nhds z.im_pos, hdmem, hpmem]
      with w hw hwd hwp
    change discFiniteChart (l.symm (e.val.symm (e.val (LiZhongQC.utm_pext p w)))) =
      cayleyFormula w
    rw [e.val.left_inv hwp]
    have hpd : LiZhongQC.utm_pext p w = M.discCover (d w) := by
      exact LiZhongQC.utm_a_pext_eq p hw
    rw [hpd, hl, l.left_inv hwd]
    refine (congrArg ((↑) : Complex.UnitDisc → ℂ)
      (discFiniteHomeomorph.apply_symm_apply
        (halfPlaneToDisc (UpperHalfPlane.ofComplex w)))).trans ?_
    change cayleyFormula ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) = cayleyFormula w
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hchain : deriv T (e.val x) * deriv h (z : ℂ) = deriv cayleyFormula (z : ℂ) := by
    calc
      deriv T (e.val x) * deriv h (z : ℂ) = deriv ((T : ℂ → ℂ) ∘ h) (z : ℂ) := by
        rw [deriv_comp (z : ℂ) (hhz.symm ▸ hT) hh, hhz]
      _ = deriv cayleyFormula (z : ℂ) := hnear.deriv_eq
  have hTx : T (e.val x) = cayleyFormula (z : ℂ) := by
    change discFiniteChart (l.symm (e.val.symm (e.val x))) = cayleyFormula (z : ℂ)
    rw [e.val.left_inv hxE]
    have hinv : l.symm x = a := by rw [← hpa, hl, l.left_inv hla]
    exact (congrArg discFiniteChart hinv).trans
      (congrArg ((↑) : Complex.UnitDisc → ℂ)
        (discFiniteHomeomorph.apply_symm_apply (halfPlaneToDisc z)))
  have hden : (discCoverAtlasInducedMetric M).density e x =
      poincareLengthDensity (cayleyFormula (z : ℂ)) ^ 2 * ‖deriv T (e.val x)‖ ^ 2 := by
    change DiscCoverMetricConstruction.density M e x = _
    rw [DiscCoverMetricConstruction.density_eq_sheet M e l hl x ⟨hxE, hxL⟩]
    change poincareLengthDensity (T (e.val x)) ^ 2 * ‖deriv T (e.val x)‖ ^ 2 = _
    rw [hTx]
  change (discCoverAtlasInducedMetric M).density e x * ‖deriv h (z : ℂ)‖ ^ 2 = _
  calc
    (discCoverAtlasInducedMetric M).density e x * ‖deriv h (z : ℂ)‖ ^ 2 =
        discPoincareTensor (cayleyFormula (z : ℂ))
          (deriv cayleyFormula (z : ℂ) * 1) (deriv cayleyFormula (z : ℂ) * 1) := by
      rw [hden, discPoincareTensor_apply, poincareDensityDisc_eq_poincareLengthDensity,
        real_inner_self_eq_norm_sq, ← hchain]
      simp only [mul_one, norm_mul, mul_pow]
      ring
    _ = halfPlanePoincareTensor z 1 1 := cayley_deriv_discPoincareTensor_pullback z 1 1
    _ = 1 / z.im ^ 2 := by rw [halfPlanePoincareTensor_self, norm_one, one_pow]

private theorem horizontal_coefficient_apply_halfPlaneCover
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : letI := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (Q S : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    letI := R.toRiemannAtlas.toChartedSpace
    let e := chosenChart R.toRiemannSurface (M.halfPlaneCover z)
    Q.val (M.halfPlaneCover z) (e.val (M.halfPlaneCover z)) *
        conj (S.val (M.halfPlaneCover z) (e.val (M.halfPlaneCover z))) /
      (((discCoverAtlasInducedMetric M).density e (M.halfPlaneCover z) ^ 2 : ℝ) : ℂ) =
      WeilPetersson.quadraticPointwiseLift R M.halfPlaneCover Q S z := by
  let := R.toRiemannAtlas.toChartedSpace
  let p := M.halfPlaneCover
  let x := p z
  let e := chosenChart R.toRiemannSurface x
  let h : ℂ → ℂ := fun w => e.val (LiZhongQC.utm_pext p w)
  let dens := (discCoverAtlasInducedMetric M).density e x
  let b := deriv h (z : ℂ)
  have hpext : LiZhongQC.utm_pext p (z : ℂ) = x := by
    simpa only [UpperHalfPlane.ofComplex_apply] using LiZhongQC.utm_a_pext_eq p z.im_pos
  have hlift (T : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
      WeilPetersson.liftQuadratic R.toRiemannAtlas p T z = T.val x (e.val x) * b ^ 2 := by
    change LiZhongQC.utm_liftQD T.val p (z : ℂ) = _
    simp only [LiZhongQC.utm_liftQD, hpext, b, h, e, chosenChart]
  have hdens : dens ≠ 0 := ne_of_gt
    ((discCoverAtlasInducedMetric M).density_pos e x (mem_chart_source ℂ x))
  have hdenssq : ((dens ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hdens)
  have hdensity : dens * ‖b‖ ^ 2 = 1 / z.im ^ 2 :=
    discCover_density_mul_coverCoordinate_norm_sq R M hp z
  have hunit : dens * ‖b‖ ^ 2 * z.im ^ 2 = 1 :=
    (eq_div_iff (pow_ne_zero 2 z.im_ne_zero)).mp hdensity
  have hreal : dens ^ 2 * (z.im ^ 4 * ‖b‖ ^ 4) = 1 := by
    calc
      dens ^ 2 * (z.im ^ 4 * ‖b‖ ^ 4) = (dens * ‖b‖ ^ 2 * z.im ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hunit]; norm_num
  have hcomplex : ((dens ^ 2 : ℝ) : ℂ) * ((z.im ^ 4 * ‖b‖ ^ 4 : ℝ) : ℂ) = 1 :=
    (Complex.ofReal_mul _ _).symm.trans (congrArg Complex.ofReal hreal)
  have hnorm : b ^ 2 * conj (b ^ 2) = ((‖b‖ ^ 4 : ℝ) : ℂ) := by
    rw [Complex.mul_conj', norm_pow]
    push_cast
    ring
  change Q.val x (e.val x) * conj (S.val x (e.val x)) / ((dens ^ 2 : ℝ) : ℂ) =
    WeilPetersson.quadraticPointwiseLift R p Q S z
  apply (div_eq_iff hdenssq).mpr
  rw [WeilPetersson.quadraticPointwiseLift, hlift Q, hlift S, map_mul]
  calc
    Q.val x (e.val x) * conj (S.val x (e.val x)) =
        (Q.val x (e.val x) * conj (S.val x (e.val x))) *
          (((dens ^ 2 : ℝ) : ℂ) * ((z.im ^ 4 * ‖b‖ ^ 4 : ℝ) : ℂ)) := by
      rw [hcomplex, mul_one]
    _ = ((z.im ^ 4 : ℝ) : ℂ) * (Q.val x (e.val x) * conj (S.val x (e.val x))) *
        (b ^ 2 * conj (b ^ 2)) * ((dens ^ 2 : ℝ) : ℂ) := by
      rw [hnorm, Complex.ofReal_mul]
      ring
    _ = _ := by ring

/-- The original coefficient integral and the book-normalized actual horizontal
pairing are the same fundamental-region quadratic integral, with factor two. -/
theorem metricTensorBookL2Pairing_horizontal_fundamental_integral
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R
      (discCoverAtlasInducedMetric M).metric)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : letI := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (P : HalfPlaneFuchsianGroup (Γ.map realSLMobius))
    {F : Set ℍ} (hF : IsHalfPlaneFundamentalRegion P F)
    (Q S : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    letI : MeasurableSpace X := borel X
    let μ : Measure X := harea.exists.choose
    let f : X → ℂ := fun x =>
      let e := chosenChart R.toRiemannSurface x
      Q.val x (e.val x) * conj (S.val x (e.val x)) /
        (((discCoverAtlasInducedMetric M).density e x ^ 2 : ℝ) : ℂ)
    (∫ x, f x ∂μ) =
        WeilPetersson.nativeQuadraticPairing R.toRiemannAtlas M.halfPlaneCover F Q S ∧
    metricTensorBookL2Pairing R (discCoverAtlasInducedMetric M).metric harea
        ((2 : ℝ) • quadraticDifferentialTensor R Q)
        ((2 : ℝ) • quadraticDifferentialTensor R S) =
      2 * (WeilPetersson.nativeQuadraticPairing
        R.toRiemannAtlas M.halfPlaneCover F Q S).re := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let μ : Measure X := harea.exists.choose
  let f : X → ℂ := fun x =>
    let e := chosenChart R.toRiemannSurface x
    Q.val x (e.val x) * conj (S.val x (e.val x)) /
      (((discCoverAtlasInducedMetric M).density e x ^ 2 : ℝ) : ℂ)
  have hcoefficient := metricTensorBookL2Pairing_horizontal_coefficient_integral
    R (discCoverAtlasInducedMetric M) harea Q S
  have hc : Continuous f := hcoefficient.1
  have hmap : Measure.map M.halfPlaneCover ((volume : Measure ℍ).restrict F) = μ :=
    (halfPlaneCover_fundamentalRegion_area_eq_selected R M harea hp P hF).2
  have hi : (∫ x, f x ∂μ) =
      WeilPetersson.nativeQuadraticPairing R.toRiemannAtlas M.halfPlaneCover F Q S := by
    calc
      (∫ x, f x ∂μ) =
          ∫ x, f x ∂Measure.map M.halfPlaneCover ((volume : Measure ℍ).restrict F) := by
        rw [hmap]
      _ = ∫ z in F, f (M.halfPlaneCover z) ∂(volume : Measure ℍ) :=
        integral_map_of_stronglyMeasurable M.halfPlaneCover_covering.continuous.measurable
          hc.stronglyMeasurable
      _ = ∫ z in F, WeilPetersson.quadraticPointwiseLift R M.halfPlaneCover Q S z
          ∂(volume : Measure ℍ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (horizontal_coefficient_apply_halfPlaneCover R M hp Q S)
      _ = WeilPetersson.nativeQuadraticPairing R.toRiemannAtlas M.halfPlaneCover F Q S :=
        (WeilPetersson.quadraticPairing_eq_hyperbolicIntegral F hF.1.measurableSet
          (WeilPetersson.liftQuadratic R.toRiemannAtlas M.halfPlaneCover Q)
          (WeilPetersson.liftQuadratic R.toRiemannAtlas M.halfPlaneCover S)).symm
  refine ⟨hi, ?_⟩
  exact hcoefficient.2.2.trans (congrArg (fun a : ℂ => 2 * a.re) hi)

end LowDimensionalTopology.Geometry.Teichmuller
