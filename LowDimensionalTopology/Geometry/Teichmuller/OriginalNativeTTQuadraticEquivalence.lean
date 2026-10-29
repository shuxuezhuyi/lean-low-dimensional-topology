module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalQuadraticDifferentialTensor

/-!
# Native TT tensors and the existing original quadratic differentials

The smooth tensor has already been constructed on the original tangent bundle.
Here its actual metric trace and whole positive divergence vanish. The two
real-part coefficient values and the existing forward construction then give
an equivalence of the actual native carriers. No linear or L2 assertion is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Filter Set Topology
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces AtlasMetricConstruction
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

private theorem quadratic_tensor_gram
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (p : X) (z : ℂ)
    (hz : z ∈ (chosenChart R.toRiemannSurface p).val.target) (a b : ℂ) :
    symmetricTensorGramInChart R (quadraticDifferentialTensor R Q)
        (chosenChart R.toRiemannSurface p)
        ((chosenChart R.toRiemannSurface p).val.symm z) a b =
      (Q.val p z * a * b).re := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let e := chosenChart R.toRiemannSurface p
  let x := e.val.symm z
  have hx : x ∈ e.val.source := e.val.map_target hz
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  rw [symmetricTensorGramInChart_eq R (quadraticDifferentialTensor R Q) e x hx]
  change (quadraticDifferentialTensor R Q).val.toFun x (D.symm a) (D.symm b) = _
  have hs := quadraticDifferentialTensor_apply R Q p x hx (D.symm a) (D.symm b)
  change (quadraticDifferentialTensor R Q).val.toFun x (D.symm a) (D.symm b) =
    (Q.val p (e.val x) * D (D.symm a) * D (D.symm b)).re at hs
  simpa only [D.apply_symm_apply, x, e.val.right_inv hz] using hs

/-- The actual tensor of Q has zero trace for every inducing original metric. -/
theorem metricTensorTrace_quadraticDifferentialTensor
    (G : AtlasInducedMetric R.toRiemannSurface)
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) :
    metricTensorTrace R G.metric (quadraticDifferentialTensor R Q) x = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let e := chosenChart R.toRiemannSurface x
  have hx : x ∈ e.val.source := mem_chart_source ℂ x
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  apply (metricTensorTrace_eq_zero_iff_conformal_frame R G
    (quadraticDifferentialTensor R Q) e x hx).mpr
  have h1 := quadraticDifferentialTensor_apply R Q x x hx (D.symm 1) (D.symm 1)
  have hI := quadraticDifferentialTensor_apply R Q x x hx (D.symm Complex.I) (D.symm Complex.I)
  change (quadraticDifferentialTensor R Q).val.toFun x (D.symm 1) (D.symm 1) =
    (Q.val x (e.val x) * D (D.symm 1) * D (D.symm 1)).re at h1
  change (quadraticDifferentialTensor R Q).val.toFun x (D.symm Complex.I) (D.symm Complex.I) =
    (Q.val x (e.val x) * D (D.symm Complex.I) * D (D.symm Complex.I)).re at hI
  have h11 : (quadraticDifferentialTensor R Q).val.toFun x (D.symm 1) (D.symm 1) =
      (Q.val x (e.val x)).re := by
    simpa only [D.apply_symm_apply, mul_one] using h1
  have h22 : (quadraticDifferentialTensor R Q).val.toFun x
      (D.symm Complex.I) (D.symm Complex.I) = -(Q.val x (e.val x)).re := by
    simpa only [D.apply_symm_apply, mul_assoc, Complex.I_mul_I,
      mul_neg, mul_one, Complex.neg_re] using hI
  change (quadraticDifferentialTensor R Q).val.toFun x
    (D.symm Complex.I) (D.symm Complex.I) =
      -(quadraticDifferentialTensor R Q).val.toFun x (D.symm 1) (D.symm 1)
  rw [h22, h11]

/-- The entire actual native covector divergence of Q's tensor vanishes. -/
theorem metricTensorDivergence_quadraticDifferentialTensor
    (G : AtlasInducedMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    (metricTensorDivergence R G.metric hdiv (quadraticDifferentialTensor R Q)).toFun x = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let e := chosenChart R.toRiemannSurface x
  have hx : x ∈ e.val.source := mem_chart_source ℂ x
  let z := e.val x
  have hz : z ∈ e.val.target := e.val.map_source hx
  let a : ℂ → ℝ := fun w => symmetricTensorGramInChart R
    (quadraticDifferentialTensor R Q) e (e.val.symm w) 1 1
  let b : ℂ → ℝ := fun w => symmetricTensorGramInChart R
    (quadraticDifferentialTensor R Q) e (e.val.symm w) 1 Complex.I
  have htrace : ∀ᶠ w in 𝓝 z,
      metricTensorTrace R G.metric (quadraticDifferentialTensor R Q) (e.val.symm w) = 0 :=
    Filter.Eventually.of_forall (fun w => metricTensorTrace_quadraticDifferentialTensor R G Q _)
  have hq : DifferentiableAt ℂ (Q.val x) z :=
    (Q.property.2 x).differentiableAt (e.val.open_target.mem_nhds hz)
  let A : ℂ →L[ℝ] ℂ := fderiv ℝ (Q.val x) z
  have haeq : a =ᶠ[𝓝 z] (fun w => (Q.val x w).re) := by
    filter_upwards [e.val.open_target.mem_nhds hz] with w hw
    simpa only [mul_one] using quadratic_tensor_gram R Q x w hw 1 1
  have hbeq : b =ᶠ[𝓝 z] (fun w => -(Q.val x w).im) := by
    filter_upwards [e.val.open_target.mem_nhds hz] with w hw
    simpa only [mul_one, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, zero_sub] using quadratic_tensor_gram R Q x w hw 1 Complex.I
  have hqR : HasFDerivAt (Q.val x) A z := (hq.restrictScalars ℝ).hasFDerivAt
  have haD : fderiv ℝ a z = Complex.reCLM.comp A :=
    ((Complex.reCLM.hasFDerivAt.comp z hqR).congr_of_eventuallyEq haeq).fderiv
  have hbD : fderiv ℝ b z = -(Complex.imCLM.comp A) :=
    (((Complex.imCLM.hasFDerivAt.comp z hqR).neg).congr_of_eventuallyEq hbeq).fderiv
  have hqCR : A Complex.I = Complex.I • A 1 :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hq).2
  have hre := congrArg Complex.re hqCR
  have him := congrArg Complex.im hqCR
  simp only [smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub] at hre
  simp only [smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add] at him
  have hCR0 : fderiv ℝ a z 1 + fderiv ℝ b z Complex.I = 0 := by
    rw [haD, hbD]
    change (A 1).re - (A Complex.I).im = 0
    linarith [him]
  have hCR1 : fderiv ℝ b z 1 - fderiv ℝ a z Complex.I = 0 := by
    rw [haD, hbD]
    change -(A 1).im - (A Complex.I).re = 0
    linarith [hre]
  have hlocal := metricTensorDivergence_local_isothermal_cr R G hdiv
    (quadraticDifferentialTensor R Q) e z hz htrace
  have hzero : (metricTensorDivergence R G.metric hdiv
      (quadraticDifferentialTensor R Q)).toFun (e.val.symm z) = 0 :=
    hlocal.2.2.mpr ⟨hCR0, hCR1⟩
  have hback : e.val.symm z = x := e.val.left_inv hx
  exact hback ▸ hzero

private theorem quadratic_tensor_injective :
    Function.Injective (quadraticDifferentialTensor R) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  intro Q P h
  apply Subtype.ext
  funext p z
  let e := chosenChart R.toRiemannSurface p
  by_cases hz : z ∈ e.val.target
  · have hcoeff (a b : ℂ) : (Q.val p z * a * b).re = (P.val p z * a * b).re := by
      have hs := congrArg (fun t : SmoothSymmetricTwoTensor R =>
        symmetricTensorGramInChart R t e (e.val.symm z) a b) h
      rw [quadratic_tensor_gram R Q p z hz a b, quadratic_tensor_gram R P p z hz a b] at hs
      exact hs
    apply Complex.ext
    · simpa only [mul_one] using hcoeff 1 1
    · have hs := hcoeff 1 Complex.I
      simp only [mul_one, Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, zero_sub] at hs
      exact neg_injective hs
  · exact (Q.property.1.1 p z hz).trans (P.property.1.1 p z hz).symm

/-- The original holomorphic quadratic differential is determined by its
actual native real symmetric tensor. -/
theorem quadraticDifferentialTensor_injective :
    Function.Injective (quadraticDifferentialTensor R) :=
  quadratic_tensor_injective R

private theorem quadratic_tensor_eq_of_target_formula
    (h : SmoothSymmetricTwoTensor R)
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    (∀ (p : X) (z : ℂ) (hz : z ∈ (chartAt ℂ p).target),
      let e : OriginalComplexChart R.toRiemannSurface :=
        ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
      let y := e.val.symm z
      let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e y (e.val.map_target hz)
      ∀ (v w : RealSurfaceTangent R.toRiemannSurface y),
        h.val.toFun y v w = (Q.val p z * D v * D w).re) →
      quadraticDifferentialTensor R Q = h := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change _ → quadraticDifferentialTensor R Q = h
  intro hrep
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  ext v w
  let e := chosenChart R.toRiemannSurface x
  have hx : x ∈ e.val.source := mem_chart_source ℂ x
  have hs := hrep x (e.val x) (e.val.map_source hx)
  let P (y : X) : Prop :=
    ∀ (a b : RealSurfaceTangent R.toRiemannSurface y),
      h.val.toFun y a b = (Q.val x (e.val x) *
        originalChartDifferential R.toRiemannSurface e y a *
        originalChartDifferential R.toRiemannSurface e y b).re
  have hsP : P (e.val.symm (e.val x)) := by
    intro a b
    let y : X := e.val.symm (e.val x)
    have hy : y ∈ e.val.source := e.val.map_target (e.val.map_source hx)
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e y hy
    have hsD := hs a b
    change h.val.toFun y a b = (Q.val x (e.val x) * D a * D b).re at hsD
    have ha : D a = originalChartDifferential R.toRiemannSurface e y a :=
      SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply e y hy a
    have hb : D b = originalChartDifferential R.toRiemannSurface e y b :=
      SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply e y hy b
    change h.val.toFun y a b =
      (Q.val x (e.val x) * originalChartDifferential R.toRiemannSurface e y a *
        originalChartDifferential R.toRiemannSurface e y b).re
    exact hsD.trans (congrArg Complex.re
      (congrArg₂ (fun u v : ℂ => Q.val x (e.val x) * u * v) ha hb))
  have hs' : P x := (e.val.left_inv hx) ▸ hsP
  exact (quadraticDifferentialTensor_apply R Q x x hx v w).trans (hs' v w).symm

open scoped Classical in
/-- The same actual native QD and TT carriers are mutually inverse, with the
original coefficient family and every original tangent slot preserved. -/
theorem exists_native_tensor_quadratic_equiv
    (G : AtlasInducedMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u}) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let TT : Type u := {h : SmoothSymmetricTwoTensor R //
      (∀ x : X, metricTensorTrace R G.metric h x = 0) ∧
      (∀ x : X, (metricTensorDivergence R G.metric hdiv h).toFun x = 0)}
    ∃ E : HolomorphicQuadraticDifferential R.toRiemannAtlas ≃ TT,
      (∀ (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
          (p : X) (z : ℂ) (hz : z ∈ (chartAt ℂ p).target),
        let e : OriginalComplexChart R.toRiemannSurface :=
          ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
        let x := e.val.symm z
        let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x (e.val.map_target hz)
        ∀ (v w : RealSurfaceTangent R.toRiemannSurface x),
          (E Q).val.val.toFun x v w = (Q.val p z * D v * D w).re) ∧
      (∀ t : TT, (E.symm t).val = fun p z =>
        let e : OriginalComplexChart R.toRiemannSurface :=
          ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
        if z ∈ e.val.target then
          (symmetricTensorGramInChart R t.val e (e.val.symm z) 1 1 : ℂ) -
            Complex.I *
              (symmetricTensorGramInChart R t.val e (e.val.symm z) 1 Complex.I : ℂ)
        else 0) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let TT : Type u := {h : SmoothSymmetricTwoTensor R //
    (∀ x : X, metricTensorTrace R G.metric h x = 0) ∧
    (∀ x : X, (metricTensorDivergence R G.metric hdiv h).toFun x = 0)}
  let F : HolomorphicQuadraticDifferential R.toRiemannAtlas → TT := fun Q =>
    ⟨quadraticDifferentialTensor R Q,
      (fun x => metricTensorTrace_quadraticDifferentialTensor R G Q x),
      (fun x => metricTensorDivergence_quadraticDifferentialTensor R G hdiv Q x)⟩
  have hinj : Function.Injective F := by
    intro Q P h
    exact quadratic_tensor_injective R (congrArg Subtype.val h)
  have hsurj : Function.Surjective F := by
    intro t
    have hw := native_tt_quadratic_coefficient_family R G hdiv t.val t.property.1 t.property.2
    obtain ⟨Q, _, hrep⟩ := hw.2.2.2
    refine ⟨Q, ?_⟩
    apply Subtype.ext
    exact quadratic_tensor_eq_of_target_formula R t.val Q hrep
  let E : HolomorphicQuadraticDifferential R.toRiemannAtlas ≃ TT :=
    Equiv.ofBijective F ⟨hinj, hsurj⟩
  refine ⟨E, ?_, ?_⟩
  · intro Q p z hz
    let e := chosenChart R.toRiemannSurface p
    let x := e.val.symm z
    have hx : x ∈ e.val.source := e.val.map_target hz
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    change ∀ (v w : RealSurfaceTangent R.toRiemannSurface x),
      (quadraticDifferentialTensor R Q).val.toFun x v w = (Q.val p z * D v * D w).re
    intro v w
    have hs := quadraticDifferentialTensor_apply R Q p x hx v w
    change (quadraticDifferentialTensor R Q).val.toFun x v w =
      (Q.val p (e.val x) * D v * D w).re at hs
    simpa only [x, e.val.right_inv hz] using hs
  · intro t
    have hw := native_tt_quadratic_coefficient_family R G hdiv t.val t.property.1 t.property.2
    obtain ⟨Q, hcoeff, hrep⟩ := hw.2.2.2
    have hQt : E Q = t := by
      apply Subtype.ext
      exact quadratic_tensor_eq_of_target_formula R t.val Q hrep
    have hback : E.symm t = Q := by
      rw [← hQt]
      exact E.symm_apply_apply Q
    rw [hback]
    exact hcoeff

end LowDimensionalTopology.Geometry.Teichmuller
