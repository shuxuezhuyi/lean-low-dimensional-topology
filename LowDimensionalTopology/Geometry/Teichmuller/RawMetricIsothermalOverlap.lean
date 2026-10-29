module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricIsothermalDensity
public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiConformalEquivalence
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Analytic overlaps for the same arbitrary raw metric

The local plane homeomorphisms and all original tangent vectors are unchanged.
Their two density identities give one common Gram matrix in an original chart.
The original holomorphic transition preserves the strict Wirtinger inequality;
the existing plane cancellation theorem then proves actual overlap analyticity.
No new atlas, coefficient covariance, or complex-linear overlap is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter Topology
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
open LiZhongQC (dz dzbar complexDilatation)
universe u
variable {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}

/-- The actual original chart followed by the same local plane solution,
restricted to the genuine open set on which its density is available. -/
def rawMetricIsothermalChart (e : OriginalComplexChart R) (V : Set ℂ)
    (hV : IsOpen V) (w : ℂ ≃ₜ ℂ) : OpenPartialHomeomorph X ℂ :=
  e.val.trans (w.toOpenPartialHomeomorph.restrOpen V hV)

@[simp]
theorem rawMetricIsothermalChart_source (e : OriginalComplexChart R) (V : Set ℂ)
    (hV : IsOpen V) (w : ℂ ≃ₜ ℂ) :
    (rawMetricIsothermalChart e V hV w).source = e.val.source ∩ e.val ⁻¹' V := by
  simp only [rawMetricIsothermalChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.restrOpen_source, Homeomorph.toOpenPartialHomeomorph_source,
    univ_inter]

theorem rawMetricIsothermalChart_target (e : OriginalComplexChart R) (V : Set ℂ)
    (hV : IsOpen V) (w : ℂ ≃ₜ ℂ) :
    (rawMetricIsothermalChart e V hV w).target = w '' (e.val.target ∩ V) := by
  rw [rawMetricIsothermalChart, OpenPartialHomeomorph.trans_target'']
  change w '' (((univ : Set ℂ) ∩ V) ∩ e.val.target) = w '' (e.val.target ∩ V)
  rw [univ_inter, inter_comm]

theorem rawMetricIsothermalChart_target_of_subset (e : OriginalComplexChart R)
    (V : Set ℂ) (hV : IsOpen V) (w : ℂ ≃ₜ ℂ) (hVE : V ⊆ e.val.target) :
    (rawMetricIsothermalChart e V hV w).target = w '' V := by
  rw [rawMetricIsothermalChart_target, inter_eq_right.mpr hVE]

@[simp]
theorem rawMetricIsothermalChart_apply (e : OriginalComplexChart R) (V : Set ℂ)
    (hV : IsOpen V) (w : ℂ ≃ₜ ℂ) (x : X) :
    rawMetricIsothermalChart e V hV w x = w (e.val x) := rfl

@[simp]
theorem rawMetricIsothermalChart_symm_apply (e : OriginalComplexChart R) (V : Set ℂ)
    (hV : IsOpen V) (w : ℂ ≃ₜ ℂ) (z : ℂ) :
    (rawMetricIsothermalChart e V hV w).symm z = e.val.symm (w.symm z) := rfl

private theorem wirtinger_lt_of_jacobian_pos {F : ℂ → ℂ} {z : ℂ}
    (hJ : 0 < LiZhongQC.jacobian F z) : ‖dzbar F z‖ < ‖dz F z‖ := by
  unfold LiZhongQC.jacobian at hJ
  nlinarith [norm_nonneg (dzbar F z), norm_nonneg (dz F z)]

private theorem coefficient_of_inner_density
    (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (F : ℂ → ℂ) (z : ℂ) (r : ℝ)
    (hr : 0 < r) (hF : DifferentiableAt ℝ F z)
    (hlt : ‖dzbar F z‖ < ‖dz F z‖)
    (hB : ∀ a b : ℂ,
      B a b = r * ⟪fderiv ℝ F z a, fderiv ℝ F z b⟫_ℝ) :
    metricBeltramiFromGram (B 1 1) (B 1 Complex.I) (B Complex.I Complex.I) =
      complexDilatation F z := by
  let a := dz F z
  let b := dzbar F z
  have h1 : fderiv ℝ F z 1 = a + b := by
    simpa only [a, b, map_one, mul_one] using
      LiZhongQC.fderiv_eq_dz_dzbar hF (1 : ℂ)
  have hI : fderiv ℝ F z Complex.I = a * Complex.I - b * Complex.I := by
    simpa only [a, b, Complex.conj_I, mul_neg, sub_eq_add_neg] using
      LiZhongQC.fderiv_eq_dz_dzbar hF Complex.I
  rw [hB 1 1, hB 1 Complex.I, hB Complex.I Complex.I]
  simp only [h1, hI, real_inner_self_eq_norm_sq]
  exact metricBeltramiFromGram_of_wirtinger r a b hr hlt

private theorem isothermal_coord_mvfderiv
    (e : OriginalComplexChart R) (w : ℂ → ℂ) (x : X) (hx : x ∈ e.val.source)
    (hw : DifferentiableAt ℝ w (e.val x)) (v : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    mvfderiv 𝓘(ℝ, ℂ) (w ∘ (e.val : X → ℂ)) x v =
      fderiv ℝ w (e.val x) (originalChartDifferential R e x v) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have he := mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) e.property hx
  calc
    mvfderiv 𝓘(ℝ, ℂ) (w ∘ (e.val : X → ℂ)) x v =
        mvfderiv 𝓘(ℝ, ℂ) w (e.val x)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (e.val : X → ℂ) x v) :=
      congrArg (fun L : RealSurfaceTangent R x →L[ℝ] ℂ => L v)
        (mvfderiv_comp x hw.mdifferentiableAt he)
    _ = fderiv ℝ w (e.val x) (originalChartDifferential R e x v) := by
      rw [mvfderiv_eq_fderiv]
      rfl

private theorem original_transition_intertwines
    (e f : OriginalComplexChart R) (x : X)
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source) (v : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    fderiv ℝ (e.val.symm.trans f.val) (e.val x)
        (originalChartDifferential R e x v) = originalChartDifferential R f x v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have hh := (SmoothSurfaceEquiv.refl R).chartDifferential_intertwines e f x he hf v
  change fderiv ℝ (e.val.symm.trans f.val) (e.val x)
      (originalChartDifferential R e x v) =
    originalChartDifferential R f x
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (id : X → X) x v) at hh
  simpa only [mfderiv_id, ContinuousLinearMap.id_apply] using hh

/-- Two genuine local density identities for the same arbitrary original metric
force the actual new-coordinate overlap to be analytic and positively oriented.
The old charts, plane solutions, metric and all tangent vectors are unchanged. -/
theorem rawMetricIsothermalOverlap_analytic_and_orientation
    (g : SmoothSurfaceMetric R) (e f : OriginalComplexChart R)
    (V W : Set ℂ) (hV : IsOpen V) (hW : IsOpen W)
    (w u : ℂ ≃ₜ ℂ) (rho sigma : X → ℝ)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w : ℂ → ℂ))
    (hwi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w.symm : ℂ → ℂ))
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u : ℂ → ℂ))
    (hJw : ∀ z, 0 < LiZhongQC.jacobian (w : ℂ → ℂ) z)
    (hJu : ∀ z, 0 < LiZhongQC.jacobian (u : ℂ → ℂ) z)
    (hrho : ∀ x ∈ (rawMetricIsothermalChart e V hV w).source, 0 < rho x)
    (hsigma : ∀ x ∈ (rawMetricIsothermalChart f W hW u).source, 0 < sigma x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (∀ x ∈ (rawMetricIsothermalChart e V hV w).source,
      ∀ v t : RealSurfaceTangent R x,
        g.inner x v t = rho x *
          ⟪mvfderiv 𝓘(ℝ, ℂ) ((w : ℂ → ℂ) ∘ (e.val : X → ℂ)) x v,
            mvfderiv 𝓘(ℝ, ℂ) ((w : ℂ → ℂ) ∘ (e.val : X → ℂ)) x t⟫_ℝ) →
    (∀ x ∈ (rawMetricIsothermalChart f W hW u).source,
      ∀ v t : RealSurfaceTangent R x,
        g.inner x v t = sigma x *
          ⟪mvfderiv 𝓘(ℝ, ℂ) ((u : ℂ → ℂ) ∘ (f.val : X → ℂ)) x v,
            mvfderiv 𝓘(ℝ, ℂ) ((u : ℂ → ℂ) ∘ (f.val : X → ℂ)) x t⟫_ℝ) →
    AnalyticOnNhd ℂ
      ((rawMetricIsothermalChart e V hV w).symm.trans
        (rawMetricIsothermalChart f W hW u))
      ((rawMetricIsothermalChart e V hV w).symm.trans
        (rawMetricIsothermalChart f W hW u)).source ∧
    ∀ z ∈ ((rawMetricIsothermalChart e V hV w).symm.trans
        (rawMetricIsothermalChart f W hW u)).source,
      0 < realJacobian
        ((rawMetricIsothermalChart e V hV w).symm.trans
          (rawMetricIsothermalChart f W hW u)) z := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro hinner_e hinner_f
  let c := rawMetricIsothermalChart e V hV w
  let d := rawMetricIsothermalChart f W hW u
  let H : OpenPartialHomeomorph ℂ ℂ := c.symm.trans d
  let T : OpenPartialHomeomorph ℂ ℂ := e.val.symm.trans f.val
  let F : ℂ → ℂ := w
  let G : ℂ → ℂ := (u : ℂ → ℂ) ∘ T
  have hHfun : (H : ℂ → ℂ) = G ∘ (w.symm : ℂ → ℂ) := rfl
  have hcomp : (H : ℂ → ℂ) ∘ F = G := by
    rw [hHfun]
    funext q
    exact congrArg G (w.symm_apply_apply q)
  have hcomplex (z : ℂ) (hz : z ∈ H.source) : DifferentiableAt ℂ (H : ℂ → ℂ) z := by
    let x : X := c.symm z
    have hxc : x ∈ c.source := c.map_target hz.1
    have hxd : x ∈ d.source := hz.2
    have hxe : x ∈ e.val.source ∩ e.val ⁻¹' V := by
      simpa only [c, rawMetricIsothermalChart_source] using hxc
    have hxf : x ∈ f.val.source ∩ f.val ⁻¹' W := by
      simpa only [d, rawMetricIsothermalChart_source] using hxd
    let zeta : ℂ := e.val x
    have hFpoint : F zeta = z := by
      change c x = z
      exact c.right_inv hz.1
    have hTpoint : T zeta = f.val x := by
      change f.val (e.val.symm (e.val x)) = f.val x
      rw [e.val.left_inv hxe.1]
    have hzT : zeta ∈ T.source := by
      refine ⟨e.val.map_source hxe.1, ?_⟩
      change e.val.symm (e.val x) ∈ f.val.source
      rw [e.val.left_inv hxe.1]
      exact hxf.1
    have hTC : DifferentiableAt ℂ (T : ℂ → ℂ) zeta :=
      (R.compatible e.val e.property f.val f.property zeta hzT).differentiableAt
    have hTp : deriv (T : ℂ → ℂ) zeta ≠ 0 :=
      R.toRiemannAtlas.transition_deriv_ne_zero e.val f.val e.property f.property zeta hzT
    have hFD : DifferentiableAt ℝ F zeta := hw.differentiable (by simp) zeta
    have huD : DifferentiableAt ℝ (u : ℂ → ℂ) (T zeta) :=
      hu.differentiable (by simp) (T zeta)
    have hGD : DifferentiableAt ℝ G zeta := huD.comp zeta (hTC.restrictScalars ℝ)
    have hHD : DifferentiableAt ℝ (H : ℂ → ℂ) (F zeta) := by
      rw [hHfun]
      apply DifferentiableAt.comp (F zeta)
      · simpa only [F, w.symm_apply_apply] using hGD
      · exact hwi.differentiable (by simp) (F zeta)
    have hFlt : ‖dzbar F zeta‖ < ‖dz F zeta‖ :=
      wirtinger_lt_of_jacobian_pos (hJw zeta)
    have hult : ‖dzbar (u : ℂ → ℂ) (T zeta)‖ < ‖dz (u : ℂ → ℂ) (T zeta)‖ :=
      wirtinger_lt_of_jacobian_pos (hJu (T zeta))
    obtain ⟨hGa, hGb⟩ := LiZhongQC.eq6_4 hTC huD
    have hGlt : ‖dzbar G zeta‖ < ‖dz G zeta‖ := by
      change ‖dzbar ((u : ℂ → ℂ) ∘ (T : ℂ → ℂ)) zeta‖ <
        ‖dz ((u : ℂ → ℂ) ∘ (T : ℂ → ℂ)) zeta‖
      rw [hGb, hGa, norm_mul, norm_mul, Complex.norm_conj]
      exact mul_lt_mul_of_pos_right hult (norm_pos_iff.mpr hTp)
    have hGdz : dz G zeta ≠ 0 :=
      norm_pos_iff.mp ((norm_nonneg (dzbar G zeta)).trans_lt hGlt)
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hxe.1
    let B := metricGramForm g e x hxe.1
    have hB (a b : ℂ) : B a b = g.inner x (D.symm a) (D.symm b) := rfl
    have hNativeF (v : RealSurfaceTangent R x) :
        mvfderiv 𝓘(ℝ, ℂ) ((w : ℂ → ℂ) ∘ (e.val : X → ℂ)) x v =
          fderiv ℝ F zeta (D v) := by
      simpa only [D, F, zeta, SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply] using
        isothermal_coord_mvfderiv e (w : ℂ → ℂ) x hxe.1 hFD v
    have hDold (v : RealSurfaceTangent R x) :
        fderiv ℝ (T : ℂ → ℂ) zeta (D v) = originalChartDifferential R f x v := by
      simpa only [D, T, zeta, SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply] using
        original_transition_intertwines e f x hxe.1 hxf.1 v
    have hNativeG (v : RealSurfaceTangent R x) :
        mvfderiv 𝓘(ℝ, ℂ) ((u : ℂ → ℂ) ∘ (f.val : X → ℂ)) x v =
          fderiv ℝ G zeta (D v) := by
      calc
        mvfderiv 𝓘(ℝ, ℂ) ((u : ℂ → ℂ) ∘ (f.val : X → ℂ)) x v =
            fderiv ℝ (u : ℂ → ℂ) (f.val x) (originalChartDifferential R f x v) :=
          isothermal_coord_mvfderiv f (u : ℂ → ℂ) x hxf.1
            (hu.differentiable (by simp) (f.val x)) v
        _ = fderiv ℝ (u : ℂ → ℂ) (T zeta) (fderiv ℝ (T : ℂ → ℂ) zeta (D v)) := by
          rw [hTpoint, hDold v]
        _ = fderiv ℝ G zeta (D v) :=
          (congrArg (fun L : ℂ →L[ℝ] ℂ => L (D v))
            (fderiv_comp zeta huD (hTC.restrictScalars ℝ))).symm
    have hBF (a b : ℂ) : B a b = rho x *
        ⟪fderiv ℝ F zeta a, fderiv ℝ F zeta b⟫_ℝ := by
      have hh := hinner_e x hxc (D.symm a) (D.symm b)
      rw [hNativeF (D.symm a), hNativeF (D.symm b)] at hh
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using (hB a b).trans hh
    have hBG (a b : ℂ) : B a b = sigma x *
        ⟪fderiv ℝ G zeta a, fderiv ℝ G zeta b⟫_ℝ := by
      have hh := hinner_f x hxd (D.symm a) (D.symm b)
      rw [hNativeG (D.symm a), hNativeG (D.symm b)] at hh
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using (hB a b).trans hh
    have hcoeffF := coefficient_of_inner_density B F zeta (rho x)
      (hrho x hxc) hFD hFlt hBF
    have hcoeffG := coefficient_of_inner_density B G zeta (sigma x)
      (hsigma x hxd) hGD hGlt hBG
    have hcompdz : dz ((H : ℂ → ℂ) ∘ F) zeta ≠ 0 := by
      rw [hcomp]
      exact hGdz
    have hcompmu : complexDilatation ((H : ℂ → ℂ) ∘ F) zeta =
        complexDilatation F zeta := by
      rw [hcomp]
      exact hcoeffG.symm.trans hcoeffF
    have hh := complexDifferentiableAt_of_comp_dilatation_eq hFD hHD hFlt hcompdz hcompmu
    simpa only [hFpoint] using hh
  have hA : AnalyticOnNhd ℂ (H : ℂ → ℂ) H.source :=
    (show DifferentiableOn ℂ (H : ℂ → ℂ) H.source from
      fun z hz => (hcomplex z hz).differentiableWithinAt).analyticOnNhd H.open_source
  refine ⟨hA, ?_⟩
  intro z hz
  rw [realJacobian_eq_norm_deriv_sq (hA z hz).differentiableAt]
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
    (openPartialHomeomorph_analytic_forward_deriv_ne_zero H hA z hz))

end LowDimensionalTopology.Geometry.Teichmuller
