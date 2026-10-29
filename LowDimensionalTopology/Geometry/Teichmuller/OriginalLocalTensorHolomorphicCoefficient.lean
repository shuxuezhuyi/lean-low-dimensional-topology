module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalLocalTensorDivergenceCR
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The actual holomorphic coefficient of a local native TT tensor

The coefficient is a - I * b in the same original isothermal chart. Its real
differentiability comes from the given tensor's smooth Gram coefficients.
Neighbourhood trace zero and the actual native divergence at the point give
the Cauchy-Riemann equations. The real-part identity retains both original
tangent slots. This local statement does not construct a global differential.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

private theorem coefficient_chart_gram_smooth (h : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) :
    ContDiffOn ℝ ∞ (fun w => symmetricTensorGramInChart R h e (e.val.symm w))
      e.val.target := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have he : e.val ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ X :=
    IsManifold.subset_maximalAtlas e.property
  have hi := contMDiffOn_symm_of_mem_maximalAtlas he
  exact ((symmetricTensorGramInChart_contMDiffOn R h e).comp hi
    (fun w hw => e.val.map_target hw)).contDiffOn

private theorem coefficient_real_bilinear
    (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hsym : B Complex.I 1 = B 1 Complex.I)
    (hdiag : B Complex.I Complex.I = -B 1 1) (v w : ℂ) :
    B v w = (((B 1 1 : ℂ) - Complex.I * (B 1 Complex.I : ℂ)) * v * w).re := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im v).symm
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im w).symm
  calc
    B v w = B (v.re • (1 : ℂ) + v.im • Complex.I)
        (w.re • (1 : ℂ) + w.im • Complex.I) :=
      congrArg₂ (fun a b : ℂ => B a b) hv hw
    _ = (((B 1 1 : ℂ) - Complex.I * (B 1 Complex.I : ℂ)) * v * w).re := by
      simp only [map_add, map_smul, add_apply, smul_apply,
        smul_eq_mul, hsym, hdiag, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring

/-- The actual a - I*b coefficient is holomorphic at the point, and its real
part recovers the same tensor on every pair of original tangent vectors. -/
theorem differentiableAt_native_tracefree_coefficient
    (G : AtlasInducedMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (h : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) (z : ℂ) (hz : z ∈ e.val.target) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let x := e.val.symm z
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x (e.val.map_target hz)
    let a : ℂ → ℝ := fun w =>
      symmetricTensorGramInChart R h e (e.val.symm w) 1 1
    let b : ℂ → ℝ := fun w =>
      symmetricTensorGramInChart R h e (e.val.symm w) 1 Complex.I
    let coefficient : ℂ → ℂ := fun w => (a w : ℂ) - Complex.I * (b w : ℂ)
    (∀ᶠ w in 𝓝 z, metricTensorTrace R G.metric h (e.val.symm w) = 0) →
    (metricTensorDivergence R G.metric hdiv h).toFun x = 0 →
      DifferentiableAt ℂ coefficient z ∧
      ∀ (v w : RealSurfaceTangent R.toRiemannSurface x),
        h.val.toFun x v w = (coefficient z * D v * D w).re := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let x := e.val.symm z
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x (e.val.map_target hz)
  let a : ℂ → ℝ := fun w =>
    symmetricTensorGramInChart R h e (e.val.symm w) 1 1
  let b : ℂ → ℝ := fun w =>
    symmetricTensorGramInChart R h e (e.val.symm w) 1 Complex.I
  let coefficient : ℂ → ℂ := fun w => (a w : ℂ) - Complex.I * (b w : ℂ)
  dsimp only
  intro htrace hzero
  change DifferentiableAt ℂ coefficient z ∧
    ∀ (v w : RealSurfaceTangent R.toRiemannSurface x),
      h.val.toFun x v w = (coefficient z * D v * D w).re
  have ha : DifferentiableAt ℝ a z := by
    have hs := ((coefficient_chart_gram_smooth R h e).clm_apply
      (contDiffOn_const (c := (1 : ℂ)))).clm_apply (contDiffOn_const (c := (1 : ℂ)))
    exact (hs.contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hb : DifferentiableAt ℝ b z := by
    have hs := ((coefficient_chart_gram_smooth R h e).clm_apply
      (contDiffOn_const (c := (1 : ℂ)))).clm_apply (contDiffOn_const (c := Complex.I))
    exact (hs.contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  let A : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp (fderiv ℝ a z)
  let B : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp (fderiv ℝ b z)
  let K : ℂ →L[ℝ] ℂ := A - Complex.I • B
  have hA : HasFDerivAt (fun w => (a w : ℂ)) A z :=
    Complex.ofRealCLM.hasFDerivAt.comp z ha.hasFDerivAt
  have hB : HasFDerivAt (fun w => (b w : ℂ)) B z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hb.hasFDerivAt
  have hcoefficient : HasFDerivAt coefficient K z := hA.sub (hB.const_mul Complex.I)
  have hcr := metricTensorDivergence_local_isothermal_cr R G hdiv h e z hz htrace
  have hscalar : fderiv ℝ a z 1 + fderiv ℝ b z Complex.I = 0 ∧
      fderiv ℝ b z 1 - fderiv ℝ a z Complex.I = 0 := hcr.2.2.mp hzero
  have hK : K Complex.I = Complex.I • K 1 := by
    apply Complex.ext
    · change ((fderiv ℝ a z Complex.I : ℂ) -
          Complex.I * (fderiv ℝ b z Complex.I : ℂ)).re =
        (Complex.I * ((fderiv ℝ a z 1 : ℂ) -
          Complex.I * (fderiv ℝ b z 1 : ℂ))).re
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      linarith [hscalar.2]
    · change ((fderiv ℝ a z Complex.I : ℂ) -
          Complex.I * (fderiv ℝ b z Complex.I : ℂ)).im =
        (Complex.I * ((fderiv ℝ a z 1 : ℂ) -
          Complex.I * (fderiv ℝ b z 1 : ℂ))).im
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      linarith [hscalar.1]
  refine ⟨(hcoefficient.complexOfReal_hasFDerivAt hK).differentiableAt, ?_⟩
  have hpoint := Filter.Eventually.self_of_nhds (x := z) htrace
  let F : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := symmetricTensorGramInChart R h e x
  have hF (v w : ℂ) : F v w = h.val.toFun x (D.symm v) (D.symm w) := by
    dsimp only [F]
    rw [symmetricTensorGramInChart_eq R h e x (e.val.map_target hz)]
    rfl
  have hsymnative := h.property
  change ∀ (y : X) (v w : RealSurfaceTangent R.toRiemannSurface y),
    h.val.toFun y v w = h.val.toFun y w v at hsymnative
  have hsym : F Complex.I 1 = F 1 Complex.I := by
    simpa only [hF] using hsymnative x (D.symm Complex.I) (D.symm 1)
  have hdiag : F Complex.I Complex.I = -F 1 1 := by
    have hd := (metricTensorTrace_eq_zero_iff_conformal_frame R G h e x
      (e.val.map_target hz)).mp hpoint
    simpa only [hF] using hd
  intro v w
  calc
    h.val.toFun x v w = F (D v) (D w) := by
      rw [hF, D.symm_apply_apply, D.symm_apply_apply]
    _ = (coefficient z * D v * D w).re :=
      coefficient_real_bilinear F hsym hdiag (D v) (D w)

end LowDimensionalTopology.Geometry.Teichmuller
