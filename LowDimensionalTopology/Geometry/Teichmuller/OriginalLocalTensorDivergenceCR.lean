module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorDivergence
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalSymmetricTensorGram
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalConformalTensorTrace
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # The local native divergence calculation in an actual isothermal chart -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Filter Set Topology
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

private theorem local_real_inner (a b : ℂ) :
    inner ℝ a b = a.re * b.re + a.im * b.im := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  change (conj a * b).re = _
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem local_basis_inner (i j : Fin 2) :
    inner ℝ (![1, Complex.I] i) (![1, Complex.I] j) =
      if i = j then 1 else 0 := by
  rw [local_real_inner]
  fin_cases i <;> fin_cases j <;> norm_num

private theorem local_repr_inner (v : ℂ) (j : Fin 2) :
    (Complex.basisOneI.repr v) j = inner ℝ v (![1, Complex.I] j) := by
  rw [local_real_inner]
  fin_cases j <;> simp [Complex.coe_basisOneI_repr]

private theorem local_metric_gram (G : AtlasInducedMetric R.toRiemannSurface)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source)
    (a b : ℂ) :
    metricGramInChart G.metric e x a b = G.density e x * inner ℝ a b := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  rw [metricGramInChart_eq G.metric e x hx]
  change G.metric.inner x (D.symm a) (D.symm b) = _
  rw [G.inner_eq e x hx]
  change G.density e x * inner ℝ (D (D.symm a)) (D (D.symm b)) = _
  rw [D.apply_symm_apply, D.apply_symm_apply]

private theorem local_density_raised (G : AtlasInducedMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) (e : OriginalComplexChart R.toRiemannSurface)
    (x : X) (hx : x ∈ e.val.source) (a b : ℂ) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    G.density e x * inner ℝ
        (D (metricRaisedTensor R G.metric h x (D.symm a))) b =
      h.val.toFun x (D.symm a) (D.symm b) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  have hs := metricRaisedTensor_spec R G.metric h x (D.symm a) (D.symm b)
  rw [G.inner_eq e x hx] at hs
  change G.density e x * inner ℝ
      (D (metricRaisedTensor R G.metric h x (D.symm a))) (D (D.symm b)) = _ at hs
  rw [D.apply_symm_apply] at hs
  exact hs

private theorem local_raised_coordinate (G : AtlasInducedMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) (e : OriginalComplexChart R.toRiemannSurface)
    (x : X) (hx : x ∈ e.val.source) (i j : Fin 2) :
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    (Complex.basisOneI.repr
      (D (metricRaisedTensor R G.metric h x (D.symm (![1, Complex.I] i))))) j =
      symmetricTensorGramForm R h e x hx (![1, Complex.I] i) (![1, Complex.I] j) /
        G.density e x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  change (Complex.basisOneI.repr
    (D (metricRaisedTensor R G.metric h x (D.symm (![1, Complex.I] i))))) j =
    h.val.toFun x (D.symm (![1, Complex.I] i)) (D.symm (![1, Complex.I] j)) /
      G.density e x
  apply (eq_div_iff (ne_of_gt (G.density_pos e x hx))).2
  have hs := local_density_raised R G h e x hx (![1, Complex.I] i) (![1, Complex.I] j)
  dsimp only at hs
  rw [← local_repr_inner] at hs
  simpa only [mul_comm] using hs

private theorem local_tensor_gram_symm (h : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (a b : ℂ) :
    symmetricTensorGramInChart R h e x a b = symmetricTensorGramInChart R h e x b a := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  by_cases hx : x ∈ e.val.source
  · simp only [symmetricTensorGramInChart_eq R h e x hx]
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    change h.val.toFun x (D.symm a) (D.symm b) = h.val.toFun x (D.symm b) (D.symm a)
    have hs := h.property
    change ∀ (y : X) (v w : RealSurfaceTangent R.toRiemannSurface y),
      h.val.toFun y v w = h.val.toFun y w v at hs
    exact hs x _ _
  · simp [symmetricTensorGramInChart, hx]

private theorem local_chart_gram_smooth (h : SmoothSymmetricTwoTensor R)
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

private theorem local_chart_density_smooth (G : AtlasInducedMetric R.toRiemannSurface)
    (e : OriginalComplexChart R.toRiemannSurface) :
    ContDiffOn ℝ ∞ (fun w => G.density e (e.val.symm w)) e.val.target := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have he : e.val ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ X :=
    IsManifold.subset_maximalAtlas e.property
  have hi := contMDiffOn_symm_of_mem_maximalAtlas he
  exact ((G.density_smooth e).comp hi (fun w hw => e.val.map_target hw)).contDiffOn

/-- The two signed divergence components and the whole native covector zero
condition in a genuine isothermal chart. Trace zero is assumed on a
neighbourhood, so the opposite-diagonal identity can be differentiated there. -/
theorem metricTensorDivergence_local_isothermal_cr
    (G : AtlasInducedMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (h : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) (z : ℂ) (hz : z ∈ e.val.target) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let x := e.val.symm z
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x (e.val.map_target hz)
    let rho : ℝ := G.density e x
    let a : ℂ → ℝ := fun w =>
      symmetricTensorGramInChart R h e (e.val.symm w) 1 1
    let b : ℂ → ℝ := fun w =>
      symmetricTensorGramInChart R h e (e.val.symm w) 1 Complex.I
    let delta : RealSurfaceTangent R.toRiemannSurface x →L[ℝ] ℝ :=
      (metricTensorDivergence R G.metric hdiv h).toFun x
    (∀ᶠ w in 𝓝 z, metricTensorTrace R G.metric h (e.val.symm w) = 0) →
      delta (D.symm 1) =
        (fderiv ℝ a z 1 + fderiv ℝ b z Complex.I) / rho ∧
      delta (D.symm Complex.I) =
        (fderiv ℝ b z 1 - fderiv ℝ a z Complex.I) / rho ∧
      (delta = 0 ↔
        fderiv ℝ a z 1 + fderiv ℝ b z Complex.I = 0 ∧
        fderiv ℝ b z 1 - fderiv ℝ a z Complex.I = 0) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let x := e.val.symm z
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x (e.val.map_target hz)
  let β : Fin 2 → ℂ := ![1, Complex.I]
  let r : ℂ → ℝ := fun w => G.density e (e.val.symm w)
  let H : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w i j =>
    symmetricTensorGramInChart R h e (e.val.symm w) (β i) (β j)
  let M : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w i j =>
    metricGramInChart G.metric e (e.val.symm w) (β i) (β j)
  let A : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w i j =>
    if hw : w ∈ e.val.target then
      let y := e.val.symm w
      let E := SmoothSurfaceEquiv.originalChartDifferentialEquiv e y (e.val.map_target hw)
      (Complex.basisOneI.repr
        (E (metricRaisedTensor R G.metric h y (E.symm (β i))))) j
    else 0
  let mu : ℂ → ℝ := fun w => Real.sqrt (Matrix.det (M w))
  let a : ℂ → ℝ := fun w => H w 0 0
  let b : ℂ → ℝ := fun w => H w 0 1
  let delta : RealSurfaceTangent R.toRiemannSurface x →L[ℝ] ℝ :=
    (metricTensorDivergence R G.metric hdiv h).toFun x
  dsimp only
  intro htrace
  change delta (D.symm 1) =
      (fderiv ℝ a z 1 + fderiv ℝ b z Complex.I) / r z ∧
    delta (D.symm Complex.I) =
      (fderiv ℝ b z 1 - fderiv ℝ a z Complex.I) / r z ∧
    (delta = 0 ↔ fderiv ℝ a z 1 + fderiv ℝ b z Complex.I = 0 ∧
      fderiv ℝ b z 1 - fderiv ℝ a z Complex.I = 0)
  have htarget : ∀ᶠ w in 𝓝 z, w ∈ e.val.target := e.val.open_target.mem_nhds hz
  have hrpos (w : ℂ) (hw : w ∈ e.val.target) : 0 < r w :=
    G.density_pos e (e.val.symm w) (e.val.map_target hw)
  have hrne (w : ℂ) (hw : w ∈ e.val.target) : r w ≠ 0 := ne_of_gt (hrpos w hw)
  have hHdiff (i j : Fin 2) : DifferentiableAt ℝ (fun w => H w i j) z := by
    have hs := ((local_chart_gram_smooth R h e).clm_apply
      (contDiffOn_const (c := β i))).clm_apply (contDiffOn_const (c := β j))
    exact (hs.contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hrdiff : DifferentiableAt ℝ r z :=
    ((local_chart_density_smooth R G e).contDiffAt
      (e.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hM (w : ℂ) (hw : w ∈ e.val.target) : M w = r w • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    change metricGramInChart G.metric e (e.val.symm w) (β i) (β j) = _
    rw [local_metric_gram R G e (e.val.symm w) (e.val.map_target hw), local_basis_inner]
    simp only [r, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hmu (w : ℂ) (hw : w ∈ e.val.target) : mu w = r w := by
    change Real.sqrt (Matrix.det (M w)) = r w
    rw [hM w hw, Matrix.det_smul, Matrix.det_one]
    simpa only [Fintype.card_fin, mul_one] using Real.sqrt_sq (hrpos w hw).le
  have hA (w : ℂ) (hw : w ∈ e.val.target) (i j : Fin 2) : A w i j = H w i j / r w := by
    dsimp only [A]
    rw [dite_eq_left hw]
    simpa only [H, r, β,
      symmetricTensorGramInChart_eq R h e (e.val.symm w) (e.val.map_target hw)] using
      local_raised_coordinate R G h e (e.val.symm w) (e.val.map_target hw) i j
  have hprod (i j : Fin 2) :
      (fun w => mu w * A w i j) =ᶠ[𝓝 z] fun w => H w i j := by
    filter_upwards [htarget] with w hw
    rw [hmu w hw, hA w hw i j]
    exact mul_div_cancel₀ _ (hrne w hw)
  have hprodD (i j : Fin 2) :
      fderiv ℝ (fun w => mu w * A w i j) z = fderiv ℝ (fun w => H w i j) z :=
    ((hHdiff i j).hasFDerivAt.congr_of_eventuallyEq (hprod i j)).fderiv
  have hmetric (j k : Fin 2) :
      (fun w => M w j k) =ᶠ[𝓝 z] fun w => if j = k then r w else 0 := by
    filter_upwards [htarget] with w hw
    rw [hM w hw]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
  have hmetricD (j k : Fin 2) :
      fderiv ℝ (fun w => M w j k) z = if j = k then fderiv ℝ r z else 0 := by
    by_cases hjk : j = k
    · have hs : (fun w => M w j k) =ᶠ[𝓝 z] r := by
        simpa only [ite_eq_left hjk] using hmetric j k
      simpa only [ite_eq_left hjk] using
        (hrdiff.hasFDerivAt.congr_of_eventuallyEq hs).fderiv
    · have hs : (fun w => M w j k) =ᶠ[𝓝 z] fun _ : ℂ => (0 : ℝ) := by
        simpa only [ite_eq_right hjk] using hmetric j k
      simpa only [ite_eq_right hjk] using
        ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) z).congr_of_eventuallyEq hs).fderiv
  have hInv : (M z)⁻¹ = (r z)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    apply Matrix.inv_eq_left_inv
    rw [hM z hz]
    simp [smul_smul, hrne z hz]
  have hc_eq : (fun w => H w 1 1) =ᶠ[𝓝 z] fun w => -H w 0 0 := by
    filter_upwards [htarget, htrace] with w hw ht
    have hs := (metricTensorTrace_eq_zero_iff_conformal_frame R G h e
      (e.val.symm w) (e.val.map_target hw)).mp ht
    simpa only [H, β, Matrix.cons_val_zero, Matrix.cons_val_one,
      symmetricTensorGramInChart_eq R h e (e.val.symm w) (e.val.map_target hw),
      symmetricTensorGramForm, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearEquiv.coe_coe] using hs
  have hcpoint : H z 1 1 = -H z 0 0 := hc_eq.eq_of_nhds
  have hcD : fderiv ℝ (fun w => H w 1 1) z = -fderiv ℝ (fun w => H w 0 0) z :=
    ((hHdiff 0 0).hasFDerivAt.neg.congr_of_eventuallyEq hc_eq).fderiv
  have hb_eq : (fun w => H w 1 0) =ᶠ[𝓝 z] fun w => H w 0 1 :=
    Filter.Eventually.of_forall fun w =>
      local_tensor_gram_symm R h e (e.val.symm w) (β 1) (β 0)
  have hbD : fderiv ℝ (fun w => H w 1 0) z = fderiv ℝ (fun w => H w 0 1) z :=
    ((hHdiff 0 1).hasFDerivAt.congr_of_eventuallyEq hb_eq).fderiv
  have hdelta (i : Fin 2) : delta (D.symm (β i)) =
      (mu z)⁻¹ * (∑ j : Fin 2,
        fderiv ℝ (fun w => mu w * A w i j) z (β j))
      - (1 / 2 : ℝ) * (∑ k : Fin 2, ∑ l : Fin 2, ∑ j : Fin 2,
        (M z)⁻¹ k l * A z l j * fderiv ℝ (fun w => M w j k) z (β i)) := by
    simpa only [Complex.coe_basisOneI] using
      metricTensorDivergence_coordinates R G.metric hdiv h e z hz i
  have h0 : delta (D.symm 1) =
      (fderiv ℝ a z 1 + fderiv ℝ b z Complex.I) / r z := by
    have hs := hdelta 0
    rw [hmu z hz] at hs
    simp [Fin.sum_univ_two, hprodD, hInv, hA z hz, hmetricD, β, hcpoint] at hs
    calc
      delta (D.symm 1) = _ := hs
      _ = (fderiv ℝ a z 1 + fderiv ℝ b z Complex.I) / r z := by
        dsimp only [a, b]
        rw [div_eq_mul_inv]
        ring
  have h1 : delta (D.symm Complex.I) =
      (fderiv ℝ b z 1 - fderiv ℝ a z Complex.I) / r z := by
    have hs := hdelta 1
    rw [hmu z hz] at hs
    simp [Fin.sum_univ_two, hprodD, hInv, hA z hz, hmetricD, β, hcpoint, hcD, hbD] at hs
    calc
      delta (D.symm Complex.I) = _ := hs
      _ = (fderiv ℝ b z 1 - fderiv ℝ a z Complex.I) / r z := by
        dsimp only [a, b]
        rw [div_eq_mul_inv]
        ring
  have hzero : delta = 0 ↔ delta (D.symm 1) = 0 ∧ delta (D.symm Complex.I) = 0 := by
    constructor
    · intro hd
      rw [hd]
      exact ⟨rfl, rfl⟩
    · rintro ⟨hzero1, hzeroI⟩
      ext v
      change delta v = 0
      have hv : v = (D v).re • D.symm 1 + (D v).im • D.symm Complex.I := by
        apply D.injective
        simp only [map_add, map_smul, D.apply_symm_apply]
        simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im (D v)).symm
      rw [hv]
      simp only [map_add, map_smul, hzero1, hzeroI, smul_zero, add_zero]
  refine ⟨h0, h1, ?_⟩
  rw [hzero, h0, h1]
  have hcancel (t : ℝ) : t / r z = 0 ↔ t = 0 := by
    constructor
    · intro ht
      have hs := congrArg (fun v : ℝ => v * r z) ht
      simpa only [div_mul_cancel₀ _ (hrne z hz), zero_mul] using hs
    · intro ht
      rw [ht, zero_div]
  exact and_congr (hcancel _) (hcancel _)

end LowDimensionalTopology.Geometry.Teichmuller
