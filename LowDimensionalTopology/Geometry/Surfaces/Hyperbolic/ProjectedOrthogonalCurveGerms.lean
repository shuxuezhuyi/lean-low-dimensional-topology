module
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ChartwiseRectifiability
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicOrthogonality

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- The same original cover sends two regular orthogonal native germs to
regular germs with a common nonzero complex differential and intrinsic right angle. -/
theorem HyperbolicSurfaceModel.projected_orthogonal_curve_derivatives
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (L N : HalfPlaneLine) (z : ℍ)
    (horth : L.OrthogonalAt N z) (γ σ : ℝ → ℍ) (t a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hγ : ContinuousAt γ t) (hσ : ContinuousAt σ t)
    (hγz : γ t = z) (hσz : σ t = z)
    (hv : HasDerivAt (fun s => (γ s : ℂ)) (a • L.tangentAt z) t)
    (hw : HasDerivAt (fun s => (σ s : ℂ)) (b • N.tangentAt z) t)
    (g : OpenPartialHomeomorph X ℂ) (hg : g ∈ R.charts)
    (hgz : M.halfPlaneCover z ∈ g.source) :
    ∃ d : ℂ, d ≠ 0 ∧
      HasDerivAt (fun s => g (M.halfPlaneCover (γ s))) (d * (a • L.tangentAt z)) t ∧
      HasDerivAt (fun s => g (M.halfPlaneCover (σ s))) (d * (b • N.tangentAt z)) t ∧
      deriv (fun s => g (M.halfPlaneCover (γ s))) t ≠ 0 ∧
      deriv (fun s => g (M.halfPlaneCover (σ s))) t ≠ 0 ∧
      riemannIntrinsicCurveAngle R.toRiemannAtlas (M.halfPlaneCover z)
        (fun s => M.halfPlaneCover (γ s)) (fun s => M.halfPlaneCover (σ s)) t =
          Real.pi / 2 := by
  let e := chartAt ℂ z
  have he : e ∈ (RiemannAtlas.ofManifold ℍ).charts := chart_mem_atlas ℂ z
  have hes (w : ℍ) : w ∈ e.source := by change w ∈ (univ : Set ℍ); trivial
  obtain ⟨l, hzl, hl⟩ := M.halfPlaneCover_covering.isLocalHomeomorph z
  let Q := e.symm.trans (l.trans g)
  have hsub : Q.source ⊆ riemannChartMapDomain e M.halfPlaneCover g := by
    intro w hw'
    change w ∈ e.target ∧ e.symm w ∈ l.source ∧ l (e.symm w) ∈ g.source at hw'
    refine ⟨hw'.1, ?_⟩
    change M.halfPlaneCover (e.symm w) ∈ g.source
    rw [hl]
    exact hw'.2.2
  have hQ : AnalyticOnNhd ℂ Q Q.source := by
    apply AnalyticOnNhd.congr Q.open_source
      ((M.halfPlaneCover_analytic.2 e he g hg).mono hsub)
    intro w _hw
    change g (M.halfPlaneCover (e.symm w)) = g (l (e.symm w))
    rw [hl]
  have hzQ : e z ∈ Q.source := by
    change e z ∈ e.target ∧ e.symm (e z) ∈ l.source ∧ l (e.symm (e z)) ∈ g.source
    rw [e.left_inv (hes z), ← hl]
    exact ⟨e.map_source (hes z), hzl, hgz⟩
  have hval (w : ℍ) : Q (w : ℂ) = g (M.halfPlaneCover w) := by
    change g (l (e.symm (e w))) = g (M.halfPlaneCover w)
    rw [e.left_inv (hes w), ← hl]
  let d := deriv Q (e z)
  have hd : d ≠ 0 := openPartialHomeomorph_analytic_forward_deriv_ne_zero Q hQ (e z) hzQ
  have hD := (hQ (e z) hzQ).differentiableAt
  have htransport {η : ℝ → ℍ} {v : ℂ} (hη : η t = z)
      (hηv : HasDerivAt (fun s => (η s : ℂ)) v t) :
      HasDerivAt (fun s => g (M.halfPlaneCover (η s))) (d * v) t := by
    have hr : HasFDerivAt Q ((fderiv ℂ Q (e z)).restrictScalars ℝ) (η t : ℂ) := by
      rw [hη]
      exact hD.hasFDerivAt.restrictScalars ℝ
    have hc := hr.comp_hasDerivAt t hηv
    simpa only [Function.comp_def, hval, ContinuousLinearMap.coe_restrictScalars',
      fderiv_eq_deriv_mul] using hc
  have hv' := htransport hγz hv
  have hw' := htransport hσz hw
  have hv0 : a • L.tangentAt z ≠ 0 := smul_ne_zero ha (L.tangentAt_ne_zero z)
  have hw0 : b • N.tangentAt z ≠ 0 := smul_ne_zero hb (N.tangentAt_ne_zero z)
  have hvd : d * (a • L.tangentAt z) ≠ 0 := mul_ne_zero hd hv0
  have hwd : d * (b • N.tangentAt z) ≠ 0 := mul_ne_zero hd hw0
  have hangle : InnerProductGeometry.angle (d * (a • L.tangentAt z))
      (d * (b • N.tangentAt z)) = Real.pi / 2 := by
    have hconf := InnerProductGeometry.ConformalAt.preserves_angle
      (hD.hasFDerivAt.restrictScalars ℝ) (hD.conformalAt hd)
      (a • L.tangentAt z) (b • N.tangentAt z)
    have hzero : inner ℝ (a • L.tangentAt z) (b • N.tangentAt z) = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, horth.2.2, mul_zero, mul_zero]
    have hn := (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp hzero
    have hc : InnerProductGeometry.angle (d * (a • L.tangentAt z))
        (d * (b • N.tangentAt z)) =
          InnerProductGeometry.angle (a • L.tangentAt z) (b • N.tangentAt z) := by
      simpa only [ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul] using hconf
    exact hc.trans hn
  refine ⟨d, hd, hv', hw', ?_, ?_, ?_⟩
  · rw [hv'.deriv]
    exact hvd
  · rw [hw'.deriv]
    exact hwd
  · have hi := R.toRiemannAtlas.intrinsicCurveAngle_eq g hg (M.halfPlaneCover z) hgz
      (fun s => M.halfPlaneCover (γ s)) (fun s => M.halfPlaneCover (σ s)) t
      (M.halfPlaneCover_covering.continuous.continuousAt.comp hγ)
      (M.halfPlaneCover_covering.continuous.continuousAt.comp hσ)
      (congrArg M.halfPlaneCover hγz) (congrArg M.halfPlaneCover hσz)
      _ _ hv' hw' hvd hwd
    apply hi.trans
    unfold riemannCurveAngle
    rw [hv'.deriv, hw'.deriv]
    exact hangle

end LowDimensionalTopology.Geometry.Surfaces
