module

public import LowDimensionalTopology.Unproved.Teichmuller.QuadraticSegmentEndpointInput
public import LowDimensionalTopology.Geometry.Teichmuller.NativeLiftedQuadraticIntervalLength
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticProjectionDistance
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The same smooth segment in its actual quadratic metric

The ordinary zero coordinate and the original path are retained in every
length comparison. A segment's parameter is allowed to have zero velocity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC LowDimensionalTopology.Unproved.Teichmuller

private theorem native_chartAt (x : UpperHalfPlane) :
    letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
    chartAt ℂ x = UpperHalfPlane.ofComplex.symm := by
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  have hx := chart_mem_atlas ℂ x
  change chartAt ℂ x ∈ ({UpperHalfPlane.ofComplex.symm} :
    Set (OpenPartialHomeomorph UpperHalfPlane ℂ)) at hx
  exact Set.mem_singleton_iff.mp hx

private theorem native_chartAt_fun (x : UpperHalfPlane) :
    letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
    (chartAt ℂ x : UpperHalfPlane → ℂ) = UpperHalfPlane.coe := by
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  rw [native_chartAt x]
  rfl

private theorem native_lengthOn_eq_model_integral
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ (z₀ : UpperHalfPlane) (m : ℕ) (ξ : ℂ → ℂ) (r : ℝ), 0 < r →
        closedBall (z₀ : ℂ) r ⊆ upperHalf →
        (∀ z ∈ closedBall (z₀ : ℂ) r, AnalyticAt ℂ ξ z ∧ deriv ξ z ≠ 0 ∧
          ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2) →
        InjOn ξ (closedBall (z₀ : ℂ) r) →
        ∀ {a b : UpperHalfPlane} (L : Path a b) (s t : ℝ),
          0 ≤ s → s < t → t ≤ 1 →
          (∃ K : NNReal, LipschitzOnWith K (fun u : ℝ => (L.extend u : ℂ)) (Icc s t)) →
          (∀ u ∈ Icc s t, (L.extend u : ℂ) ∈ ball (z₀ : ℂ) r) →
          phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) L s t =
            ∫⁻ u in Ioo s t,
              phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m)
                (ξ (L.extend u : ℂ)) *
              ‖deriv (fun v : ℝ => ξ (L.extend v : ℂ)) u‖ₑ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  let := upperHalfNativeSurface.toRiemannAtlas.isManifold
  dsimp only
  intro z₀ m ξ r hr hball han hinj a b L s t hs hst ht hLip hsrc
  have hchart := native_chartAt z₀
  have hcenter : chartAt ℂ z₀ z₀ = (z₀ : ℂ) := by rw [hchart]; rfl
  have han' : ∀ z ∈ closedBall (chartAt ℂ z₀ z₀) r,
      AnalyticAt ℂ ξ z ∧ deriv ξ z ≠ 0 ∧
        (qH : UpperHalfPlane → ℂ → ℂ) z₀ z =
          (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2 := by
    intro z hz
    rw [hcenter] at hz
    obtain ⟨hξ, hdξ, hψ⟩ := han z hz
    refine ⟨hξ, hdξ, ?_⟩
    change upperHalf.indicator ψ z = _
    rw [Set.indicator_of_mem (hball hz)]
    exact hψ
  have hinj' : InjOn ξ (closedBall (chartAt ℂ z₀ z₀) r) := by
    simpa only [hcenter] using hinj
  rw [liftedQuadraticLengthOn_eq_integral_of_lipschitz R.toRiemannSurface q hp
    a b L s t hs hst ht hLip]
  refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hx : L.extend u ∈ (chartAt ℂ z₀).source := by
    rw [hchart]
    change L.extend u ∈ (univ : Set UpperHalfPlane)
    trivial
  have hξ := s25e_pw qH.property z₀ m ξ hr han' hinj'
    (γ := L.extend) L.continuous_extend.continuousAt hx (by
      rw [hchart]
      exact hsrc u (Ioo_subset_Icc_self hu))
  rw [native_chartAt_fun z₀] at hξ
  change phiDensity ((qH : UpperHalfPlane → ℂ → ℂ) z₀) (L.extend u : ℂ) *
      ‖deriv (fun v : ℝ => (L.extend v : ℂ)) u‖ₑ = _ at hξ
  have hcoef : (qH : UpperHalfPlane → ℂ → ℂ) z₀ (L.extend u : ℂ) = ψ (L.extend u : ℂ) := by
    change upperHalf.indicator ψ (L.extend u : ℂ) = ψ (L.extend u : ℂ)
    have hz : (L.extend u : ℂ) ∈ upperHalf := (L.extend u).im_pos
    exact Set.indicator_of_mem hz ψ
  simpa only [phiDensity, hcoef] using hξ

private theorem model_ray_integral_of_monotone_clock
    (m : ℕ) (hm : 0 < m) {f : ℝ → ℂ} {s t : ℝ} (hst : s < t)
    {K : NNReal} (hf : LipschitzOnWith K f (Icc s t))
    (ρ : ℝ → ℝ) (hρc : ContinuousOn ρ (Icc s t))
    (hρm : MonotoneOn ρ (Icc s t)) (d : ℝ)
    (hρ0 : ∀ u ∈ Icc s t, 0 ≤ d * ρ u)
    (v : ℂ) (hv : ‖v‖ = 1)
    (hline : ∀ u ∈ Icc s t, f u = ((d * ρ u : ℝ) : ℂ) * v) :
    ∫⁻ u in Ioo s t,
      phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) (f u) *
        ‖deriv f u‖ₑ =
      ENNReal.ofReal (|(d * ρ t) ^ (((m : ℝ) + 2) / 2) -
        (d * ρ s) ^ (((m : ℝ) + 2) / 2)|) := by
  let c : ℝ := ((m : ℝ) + 2) / 2
  have hc : 1 < c := by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp only [c]
    linarith
  let F : ℝ → ℂ := fun u => ((d * u : ℝ) : ℂ) * v
  let σ : ℝ → ℝ := fun u => ρ (projIcc s t hst.le u)
  have hσm : Monotone σ := fun u w huw =>
    hρm (projIcc s t hst.le u).property (projIcc s t hst.le w).property
      (monotone_projIcc hst.le huw)
  have hσc : Continuous σ := hρc.domRestrict.comp continuous_projIcc
  have hσs : σ s = ρ s := by
    dsimp only [σ]
    rw [projIcc_of_mem hst.le (left_mem_Icc.mpr hst.le)]
  have hσt : σ t = ρ t := by
    dsimp only [σ]
    rw [projIcc_of_mem hst.le (right_mem_Icc.mpr hst.le)]
  have hFLip : LipschitzWith ‖(d : ℂ) * v‖₊ F := by
    refine LipschitzWith.of_dist_le_mul fun u w => ?_
    dsimp only [F]
    rw [dist_eq_norm, show ((d * u : ℝ) : ℂ) * v - ((d * w : ℝ) : ℂ) * v =
      ((u - w : ℝ) : ℂ) * ((d : ℂ) * v) by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]
    exact le_of_eq (mul_comm _ _)
  have hF : AbsolutelyContinuousOnInterval F (σ s) (σ t) :=
    hFLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hEq : EqOn f (F ∘ σ) (uIcc s t) := by
    rw [uIcc_of_le hst.le]
    intro u hu
    dsimp only [Function.comp_def, F, σ]
    rw [projIcc_of_mem hst.le hu]
    exact hline u hu
  have hfAC : AbsolutelyContinuousOnInterval f s t :=
    (show LipschitzOnWith K f (uIcc s t) by
      simpa only [uIcc_of_le hst.le] using hf).absolutelyContinuousOnInterval
  have hG : AbsolutelyContinuousOnInterval (F ∘ σ) s t := hfAC.congr hEq
  let g : ℝ → ENNReal := fun u =>
    phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) (F u)
  have hg : Measurable g := by
    have hcont : Continuous g := by
      dsimp only [g, phiDensity]
      exact ENNReal.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (by fun_prop))
    exact hcont.measurable
  have hweighted := s26v_b_reparam_lintegral hst.le hσm hσc hF hG hg
  rw [hσs, hσt] at hweighted
  have hrst : ρ s ≤ ρ t :=
    hρm (left_mem_Icc.mpr hst.le) (right_mem_Icc.mpr hst.le) hst.le
  have hclock : ρ '' Icc s t = Icc (ρ s) (ρ t) := by
    refine subset_antisymm ?_ (intermediate_value_Icc hst.le hρc)
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨hρm (left_mem_Icc.mpr hst.le) hu hu.1,
      hρm hu (right_mem_Icc.mpr hst.le) hu.2⟩
  have hrad := s25e_radial_len (v := v) (α := 0) (β := d) hc hrst
    (fun u hu => by
      obtain ⟨w, hw, rfl⟩ := hclock.symm ▸ hu
      simpa only [zero_add] using hρ0 w hw)
  calc
    _ = ∫⁻ u in Ioo s t, g (σ u) * ‖deriv (F ∘ σ) u‖ₑ := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      have hev : f =ᶠ[𝓝 u] F ∘ σ := by
        filter_upwards [isOpen_Ioo.mem_nhds hu] with w hw
        exact hEq (by simpa only [uIcc_of_le hst.le] using Ioo_subset_Icc_self hw)
      change _ =
        phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) ((F ∘ σ) u) *
          ‖deriv (F ∘ σ) u‖ₑ
      rw [← hEq (by simpa only [uIcc_of_le hst.le] using Ioo_subset_Icc_self hu),
        ← hev.deriv_eq]
    _ = ∫⁻ u in Ioo (ρ s) (ρ t), g u * ‖deriv F u‖ₑ := hweighted
    _ = _ := by
      dsimp only [g]
      simp only [phiDensity, s25e_rho_eq]
      simpa only [F, c, zero_add, hv, Real.one_rpow, one_mul] using hrad

private theorem model_radial_increment_le_dist (m : ℕ) (a b : ℂ) :
    ENNReal.ofReal (|‖b‖ ^ (((m : ℝ) + 2) / 2) - ‖a‖ ^ (((m : ℝ) + 2) / 2)|) ≤
      metricDist univ (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m)) a b := by
  let G : ℂ → ℝ := fun w =>
    |‖w‖ ^ (((m : ℝ) + 2) / 2) - ‖a‖ ^ (((m : ℝ) + 2) / 2)|
  have hG : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |G y - G x| ≤ ((((m : ℝ) + 2) / 2) *
        ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖ := by
    intro x ε hε
    obtain ⟨δ, hδ, hδbound⟩ := s25e_radial_hG m x ε hε
    refine ⟨δ, hδ, fun y hy => ?_⟩
    calc |G y - G x| ≤
          |(‖y‖ ^ (((m : ℝ) + 2) / 2) - ‖a‖ ^ (((m : ℝ) + 2) / 2)) -
            (‖x‖ ^ (((m : ℝ) + 2) / 2) - ‖a‖ ^ (((m : ℝ) + 2) / 2))| :=
          abs_abs_sub_abs_le_abs_sub _ _
      _ = |‖y‖ ^ (((m : ℝ) + 2) / 2) - ‖x‖ ^ (((m : ℝ) + 2) / 2)| := by
          congr 1
          ring
      _ ≤ _ := hδbound y hy
  unfold metricDist
  refine le_iInf₂ fun γ hγ => ?_
  change ENNReal.ofReal (G b) ≤
    phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) γ
  exact s25e_cone_lower m hG (by simp only [G, sub_self, abs_zero]) hγ

private theorem model_flat_chord_le_dist (a b : ℂ) :
    ENNReal.ofReal ‖b - a‖ ≤
      metricDist univ (phiDensity (fun w : ℂ => (((0 : ℕ) + 2 : ℂ) / 2) ^ 2 * w ^ 0)) a b := by
  let G : ℂ → ℝ := fun w => ‖w - a‖
  have hG : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |G y - G x| ≤ ((((0 : ℕ) + 2 : ℝ) / 2) *
        ‖x‖ ^ ((((0 : ℕ) + 2 : ℝ) / 2) - 1) + ε) * ‖y - x‖ := by
    intro x ε hε
    refine ⟨1, one_pos, fun y _ => ?_⟩
    have hnorm : |‖y - a‖ - ‖x - a‖| ≤ ‖y - x‖ := by
      simpa only [sub_sub_sub_cancel_right] using abs_norm_sub_norm_le (y - a) (x - a)
    have hc : (((0 : ℕ) + 2 : ℝ) / 2) = 1 := by norm_num
    rw [hc]
    simp only [sub_self, Real.rpow_zero, one_mul]
    dsimp only [G]
    nlinarith [norm_nonneg (y - x)]
  unfold metricDist
  refine le_iInf₂ fun γ hγ => ?_
  change ENNReal.ofReal (G b) ≤
    phiLength (fun w : ℂ => (((0 : ℕ) + 2 : ℂ) / 2) ^ 2 * w ^ 0) γ
  exact s25e_cone_lower 0 hG (by simp only [G, sub_self, norm_zero]) hγ

private theorem flat_line_integral_of_monotone_clock
    {f : ℝ → ℂ} {s t : ℝ} (hst : s < t) {K : NNReal}
    (hf : LipschitzOnWith K f (Icc s t)) (ρ : ℝ → ℝ)
    (hρc : ContinuousOn ρ (Icc s t)) (hρm : MonotoneOn ρ (Icc s t))
    (A v : ℂ) (hline : ∀ u ∈ Icc s t, f u = A + (ρ u : ℂ) * v) :
    ∫⁻ u in Ioo s t, ‖deriv f u‖ₑ = ENNReal.ofReal ‖f t - f s‖ := by
  let F : ℝ → ℂ := fun u => A + (u : ℂ) * v
  let σ : ℝ → ℝ := fun u => ρ (projIcc s t hst.le u)
  have hσm : Monotone σ := fun u w huw =>
    hρm (projIcc s t hst.le u).property (projIcc s t hst.le w).property
      (monotone_projIcc hst.le huw)
  have hσc : Continuous σ := hρc.domRestrict.comp continuous_projIcc
  have hσs : σ s = ρ s := by
    dsimp only [σ]
    rw [projIcc_of_mem hst.le (left_mem_Icc.mpr hst.le)]
  have hσt : σ t = ρ t := by
    dsimp only [σ]
    rw [projIcc_of_mem hst.le (right_mem_Icc.mpr hst.le)]
  have hFLip : LipschitzWith ‖v‖₊ F := by
    refine LipschitzWith.of_dist_le_mul fun u w => ?_
    dsimp only [F]
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_mul,
      ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]
    exact le_of_eq (mul_comm _ _)
  have hF : AbsolutelyContinuousOnInterval F (σ s) (σ t) :=
    hFLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hEq : EqOn f (F ∘ σ) (uIcc s t) := by
    rw [uIcc_of_le hst.le]
    intro u hu
    dsimp only [Function.comp_def, F, σ]
    rw [projIcc_of_mem hst.le hu]
    exact hline u hu
  have hfAC : AbsolutelyContinuousOnInterval f s t :=
    (show LipschitzOnWith K f (uIcc s t) by
      simpa only [uIcc_of_le hst.le] using hf).absolutelyContinuousOnInterval
  have hG : AbsolutelyContinuousOnInterval (F ∘ σ) s t := hfAC.congr hEq
  have hweighted := s26v_b_reparam_lintegral (g := fun _ => 1)
    hst.le hσm hσc hF hG measurable_const
  simp only [one_mul] at hweighted
  rw [hσs, hσt] at hweighted
  have hrst : ρ s ≤ ρ t :=
    hρm (left_mem_Icc.mpr hst.le) (right_mem_Icc.mpr hst.le) hst.le
  have hnorm : ‖f t - f s‖ = (ρ t - ρ s) * ‖v‖ := by
    rw [hline t (right_mem_Icc.mpr hst.le), hline s (left_mem_Icc.mpr hst.le),
      add_sub_add_left_eq_sub, ← sub_mul, ← Complex.ofReal_sub, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hrst)]
  calc
    _ = ∫⁻ u in Ioo s t, ‖deriv (F ∘ σ) u‖ₑ := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      have hev : f =ᶠ[𝓝 u] F ∘ σ := by
        filter_upwards [isOpen_Ioo.mem_nhds hu] with w hw
        exact hEq (by simpa only [uIcc_of_le hst.le] using Ioo_subset_Icc_self hw)
      rw [hev.deriv_eq]
    _ = ∫⁻ u in Ioo (ρ s) (ρ t), ‖deriv F u‖ₑ := hweighted
    _ = ENNReal.ofReal ((ρ t - ρ s) * ‖v‖) := by
      have hderiv (u : ℝ) : deriv F u = v :=
        ((hasDerivAt_ofReal_mul v u).const_add A).deriv
      simp only [hderiv, setLIntegral_const, Real.volume_Ioo]
      rw [← ofReal_norm, mul_comm, ← ENNReal.ofReal_mul (sub_nonneg.mpr hrst)]
    _ = _ := by rw [hnorm]

private theorem model_ray_cost_le_distance_of_clock
    (m : ℕ) (hm : 0 < m) {f : ℝ → ℂ} {s t : ℝ} (hst : s < t)
    {K : NNReal} (hf : LipschitzOnWith K f (Icc s t))
    (ρ : ℝ → ℝ) (hρc : ContinuousOn ρ (Icc s t))
    (hρm : MonotoneOn ρ (Icc s t)) (d : ℝ)
    (hρ0 : ∀ u ∈ Icc s t, 0 ≤ d * ρ u)
    (v : ℂ) (hv : ‖v‖ = 1)
    (hline : ∀ u ∈ Icc s t, f u = ((d * ρ u : ℝ) : ℂ) * v) :
    ∫⁻ u in Ioo s t,
      phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) (f u) *
        ‖deriv f u‖ₑ ≤
      metricDist univ (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m))
        (f s) (f t) := by
  rw [model_ray_integral_of_monotone_clock m hm hst hf ρ hρc hρm d hρ0 v hv hline]
  have hnorm (u : ℝ) (hu : u ∈ Icc s t) : ‖f u‖ = d * ρ u := by
    rw [hline u hu, norm_mul, hv, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (hρ0 u hu)]
  rw [← hnorm s (left_mem_Icc.mpr hst.le), ← hnorm t (right_mem_Icc.mpr hst.le)]
  exact model_radial_increment_le_dist m (f s) (f t)

private theorem model_flat_cost_le_distance_of_clock
    {f : ℝ → ℂ} {s t : ℝ} (hst : s < t) {K : NNReal}
    (hf : LipschitzOnWith K f (Icc s t)) (ρ : ℝ → ℝ)
    (hρc : ContinuousOn ρ (Icc s t)) (hρm : MonotoneOn ρ (Icc s t))
    (A v : ℂ) (hline : ∀ u ∈ Icc s t, f u = A + (ρ u : ℂ) * v) :
    ∫⁻ u in Ioo s t,
      phiDensity (fun w : ℂ => (((0 : ℕ) + 2 : ℂ) / 2) ^ 2 * w ^ 0) (f u) *
        ‖deriv f u‖ₑ ≤
      metricDist univ (phiDensity (fun w : ℂ => (((0 : ℕ) + 2 : ℂ) / 2) ^ 2 * w ^ 0))
        (f s) (f t) := by
  have hφ (z : ℂ) :
      phiDensity (fun w : ℂ => (((0 : ℕ) + 2 : ℂ) / 2) ^ 2 * w ^ 0) z = 1 := by
    norm_num [phiDensity]
  calc
    _ = ∫⁻ u in Ioo s t, ‖deriv f u‖ₑ := by simp only [hφ, one_mul]
    _ = ENNReal.ofReal ‖f t - f s‖ :=
      flat_line_integral_of_monotone_clock hst hf ρ hρc hρm A v hline
    _ ≤ _ := model_flat_chord_le_dist (f s) (f t)

private theorem clock_of_injective_ray_image
    {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) {K : NNReal}
    (hf : LipschitzOnWith K f (Icc a b)) (hi : InjOn f (Icc a b))
    (v : ℂ) (hv : ‖v‖ = 1)
    (himage : ∀ u ∈ Icc a b, ∃ r : ℝ, 0 ≤ r ∧ f u = (r : ℂ) * v) :
    ∃ (ρ : ℝ → ℝ) (d : ℝ), ContinuousOn ρ (Icc a b) ∧ MonotoneOn ρ (Icc a b) ∧
      (∀ u ∈ Icc a b, 0 ≤ d * ρ u) ∧
      ∀ u ∈ Icc a b, f u = ((d * ρ u : ℝ) : ℂ) * v := by
  have hvne : v ≠ 0 := by
    intro hzero
    have hbad : (0 : ℝ) = 1 := by simpa only [hzero, norm_zero] using hv
    exact zero_ne_one hbad
  let r : ℝ → ℝ := fun u => (f u / v).re
  have hr : ∀ u ∈ Icc a b, 0 ≤ r u ∧ f u = (r u : ℂ) * v := by
    intro u hu
    obtain ⟨r₀, hr₀, hfu⟩ := himage u hu
    have hdiv : f u / v = (r₀ : ℂ) := by rw [hfu, mul_div_cancel_right₀ _ hvne]
    have hval : r u = r₀ := by dsimp only [r]; rw [hdiv, Complex.ofReal_re]
    exact ⟨hval.symm ▸ hr₀, hval.symm ▸ hfu⟩
  have hrc : ContinuousOn r (Icc a b) :=
    Complex.continuous_re.comp_continuousOn (hf.continuousOn.div_const v)
  have hri : InjOn r (Icc a b) := by
    intro u hu w hw heq
    apply hi hu hw
    rw [(hr u hu).2, (hr w hw).2, heq]
  rcases hrc.strictMonoOn_of_injOn_Icc' hab hri with hmono | hanti
  · refine ⟨r, 1, hrc, hmono.monotoneOn, ?_, ?_⟩
    · intro u hu
      simpa only [one_mul] using (hr u hu).1
    · intro u hu
      simpa only [one_mul] using (hr u hu).2
  · refine ⟨-r, -1, hrc.neg, ?_, ?_, ?_⟩
    · intro u hu w hw huw
      exact neg_le_neg (hanti.antitoneOn hu hw huw)
    · intro u hu
      simpa only [Pi.neg_apply, neg_one_mul, neg_neg] using (hr u hu).1
    · intro u hu
      simpa only [Pi.neg_apply, neg_one_mul, neg_neg] using (hr u hu).2

private theorem clock_of_injective_segment_image
    {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) {K : NNReal}
    (hf : LipschitzOnWith K f (Icc a b)) (hi : InjOn f (Icc a b))
    (A B : ℂ) (hAB : A ≠ B)
    (himage : ∀ u ∈ Icc a b, f u ∈ segment ℝ A B) :
    ∃ (ρ : ℝ → ℝ) (v : ℂ), ContinuousOn ρ (Icc a b) ∧ MonotoneOn ρ (Icc a b) ∧
      ∀ u ∈ Icc a b, f u = A + (ρ u : ℂ) * v := by
  let v : ℂ := B - A
  have hv : v ≠ 0 := sub_ne_zero.mpr hAB.symm
  let ρ : ℝ → ℝ := fun u => ((f u - A) / v).re
  have hfact : ∀ u ∈ Icc a b, f u = A + (ρ u : ℂ) * v := by
    intro u hu
    obtain ⟨r₀, s₀, _, _, hrs, hfu⟩ := himage u hu
    have hreal : r₀ = 1 - s₀ := by linarith
    have hfu' : f u = A + (s₀ : ℂ) * v := by
      rw [← hfu, hreal]
      dsimp only [v]
      simp only [Complex.real_smul]
      push_cast
      ring
    have hval : ρ u = s₀ := by
      dsimp only [ρ]
      rw [hfu', add_sub_cancel_left, mul_div_cancel_right₀ _ hv, Complex.ofReal_re]
    exact hval.symm ▸ hfu'
  have hρc : ContinuousOn ρ (Icc a b) :=
    Complex.continuous_re.comp_continuousOn
      ((hf.continuousOn.sub continuousOn_const).div_const v)
  have hρi : InjOn ρ (Icc a b) := by
    intro u hu w hw heq
    apply hi hu hw
    rw [hfact u hu, hfact w hw, heq]
  rcases hρc.strictMonoOn_of_injOn_Icc' hab hρi with hmono | hanti
  · exact ⟨ρ, v, hρc, hmono.monotoneOn, hfact⟩
  · refine ⟨-ρ, -v, hρc.neg, ?_, ?_⟩
    · intro u hu w hw huw
      exact neg_le_neg (hanti.antitoneOn hu hw huw)
    · intro u hu
      simpa only [Pi.neg_apply, Complex.ofReal_neg, neg_mul, mul_neg, neg_neg]
        using hfact u hu

private theorem native_lifted_coefficient_ne_zero
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      (upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp) : UpperHalfPlane → ℂ → ℂ) ≠ 0 := by
  let := R.t2Space
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  have hqne : (q : X → ℂ → ℂ) ≠ 0 := fun hzero => hq (Subtype.ext hzero)
  obtain ⟨z, hz, hψz⟩ := utm_liftQD_ne q.property hqne hp
  intro hzero
  have heq := congrFun (congrFun hzero ⟨z, hz⟩) z
  change upperHalf.indicator (utm_liftQD (q : X → ℂ → ℂ) p) z = 0 at heq
  rw [Set.indicator_of_mem hz] at heq
  exact hψz heq

private theorem native_model_neighborhood
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ (z₀ : UpperHalfPlane) (m : ℕ) (ξ : ℂ → ℂ),
        AnalyticAt ℂ ξ (z₀ : ℂ) → ξ (z₀ : ℂ) = 0 → deriv ξ (z₀ : ℂ) ≠ 0 →
        (∀ᶠ z in 𝓝 (z₀ : ℂ),
          ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2) →
        ∃ (r : ℝ) (W : Set UpperHalfPlane), 0 < r ∧ W ∈ 𝓝 z₀ ∧
          closedBall (z₀ : ℂ) r ⊆ upperHalf ∧
          (∀ z ∈ closedBall (z₀ : ℂ) r, AnalyticAt ℂ ξ z ∧ deriv ξ z ≠ 0 ∧
            ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2) ∧
          InjOn ξ (closedBall (z₀ : ℂ) r) ∧
          ∀ a ∈ W, ∀ b ∈ W, ∀ δ : Path a b,
            metricDist univ (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m))
              (ξ (a : ℂ)) (ξ (b : ℂ)) ≤ phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  let := upperHalfNativeSurface.t2Space
  let := upperHalfNativeSurface.connectedSpace
  let := upperHalfNativeSurface.toRiemannAtlas.isManifold
  dsimp only
  intro z₀ m ξ hξ hξ0 hξd hξq
  have hchart := native_chartAt z₀
  have hcenter : chartAt ℂ z₀ z₀ = (z₀ : ℂ) := by rw [hchart]; rfl
  have htarget : (chartAt ℂ z₀).target = upperHalf := by
    rw [hchart]
    change (UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph
      UpperHalfPlane.coe).target = _
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, UpperHalfPlane.range_coe]
    rfl
  have hξ' : AnalyticAt ℂ ξ (chartAt ℂ z₀ z₀) := by simpa only [hcenter] using hξ
  have hξ0' : ξ (chartAt ℂ z₀ z₀) = 0 := by simpa only [hcenter] using hξ0
  have hξd' : deriv ξ (chartAt ℂ z₀ z₀) ≠ 0 := by simpa only [hcenter] using hξd
  have hξq' : ∀ᶠ z in 𝓝 (chartAt ℂ z₀ z₀),
      (qH : UpperHalfPlane → ℂ → ℂ) z₀ z =
        (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2 := by
    rw [hcenter]
    filter_upwards [hξq, isOpen_upperHalf.mem_nhds z₀.im_pos] with z hz hzH
    change upperHalf.indicator ψ z = _
    rw [Set.indicator_of_mem hzH]
    exact hz
  obtain ⟨r, hr, hsub, han, hinj⟩ :=
    s25e_local_chart qH.property z₀ m ξ hξ' hξ0' hξd' hξq'
  have hne := native_lifted_coefficient_ne_zero R q hq hp
  obtain ⟨W, hW, hlower⟩ :=
    s25e_surface_lower qH.property hne z₀ m ξ hξ' hξ0' hξd' hξq'
  have hsub' : closedBall (z₀ : ℂ) r ⊆ upperHalf := by
    simpa only [hcenter, htarget] using hsub
  refine ⟨r, W, hr, hW, hsub', ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨ha, hd, heq⟩ := han z (by simpa only [hcenter] using hz)
    refine ⟨ha, hd, ?_⟩
    change upperHalf.indicator ψ z = _ at heq
    rwa [Set.indicator_of_mem (hsub' hz)] at heq
  · simpa only [hcenter] using hinj
  · intro a ha b hb δ
    have h := hlower a ha b hb δ
    simpa only [native_chartAt_fun z₀] using h

private theorem model_cost_le_distance_of_ray_image
    (m : ℕ) {f : ℝ → ℂ} {s t : ℝ} (hst : s < t) {K : NNReal}
    (hf : LipschitzOnWith K f (Icc s t)) (hi : InjOn f (Icc s t))
    (v : ℂ) (hv : ‖v‖ = 1)
    (himage : ∀ u ∈ Icc s t, ∃ r : ℝ, 0 ≤ r ∧ f u = (r : ℂ) * v) :
    ∫⁻ u in Ioo s t,
      phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) (f u) *
        ‖deriv f u‖ₑ ≤
      metricDist univ (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m))
        (f s) (f t) := by
  obtain ⟨ρ, d, hρc, hρm, hρ0, hline⟩ :=
    clock_of_injective_ray_image hst.le hf hi v hv himage
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst m
    apply model_flat_cost_le_distance_of_clock hst hf ρ hρc hρm 0 ((d : ℂ) * v)
    intro u hu
    rw [hline u hu]
    push_cast
    ring
  · exact model_ray_cost_le_distance_of_clock m hm hst hf ρ hρc hρm d hρ0 v hv hline

private theorem model_flat_cost_le_distance_of_segment_image
    {f : ℝ → ℂ} {s t : ℝ} (hst : s < t) {K : NNReal}
    (hf : LipschitzOnWith K f (Icc s t)) (hi : InjOn f (Icc s t))
    (A B : ℂ) (hAB : A ≠ B)
    (himage : ∀ u ∈ Icc s t, f u ∈ segment ℝ A B) :
    ∫⁻ u in Ioo s t,
      phiDensity (fun w : ℂ => (((0 : ℕ) + 2 : ℂ) / 2) ^ 2 * w ^ 0) (f u) *
        ‖deriv f u‖ₑ ≤
      metricDist univ (phiDensity (fun w : ℂ => (((0 : ℕ) + 2 : ℂ) / 2) ^ 2 * w ^ 0))
        (f s) (f t) := by
  obtain ⟨ρ, v, hρc, hρm, hline⟩ :=
    clock_of_injective_segment_image hst.le hf hi A B hAB himage
  exact model_flat_cost_le_distance_of_clock hst hf ρ hρc hρm A v hline

private theorem native_segment_endpoint_local_minimum
    (hordinary : NativeQuadraticOrdinaryEndpointRay) (hzero : NativeQuadraticZeroEndpointRay)
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (L : Path a b),
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface L →
        IsQuadraticSegment upperHalfNativeSurface qH L.toContinuousMap →
        ∀ first : Bool, ∃ δ : ℝ, 0 < δ ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            (if first then 0 else 1) - δ < s → s < t → t < (if first then 0 else 1) + δ →
            phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) L s t =
              phiDistRS (qH : UpperHalfPlane → ℂ → ℂ) (L.extend s) (L.extend t) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  let := upperHalfNativeSurface.t2Space
  let := upperHalfNativeSurface.connectedSpace
  let := upperHalfNativeSurface.toRiemannAtlas.isManifold
  dsimp only
  intro a b L hSmooth hSeg first
  let t₀ : ℝ := if first then 0 else 1
  let z₀ : UpperHalfPlane := if first then a else b
  have hstart : L.extend t₀ = z₀ := by
    cases first
    · exact L.extend_one
    · exact L.extend_zero
  have hne := native_lifted_coefficient_ne_zero R q hq hp
  obtain ⟨m, ξ, hξ, hξ0, hξd, hξq⟩ := s25e_natural_chart qH.property hne z₀
  have hchart := native_chartAt z₀
  have hcenter : chartAt ℂ z₀ z₀ = (z₀ : ℂ) := by rw [hchart]; rfl
  rw [hcenter] at hξ hξ0 hξd hξq
  have hξψ : ∀ᶠ z in 𝓝 (z₀ : ℂ),
      ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2 := by
    filter_upwards [hξq, isOpen_upperHalf.mem_nhds z₀.im_pos] with z hz hzH
    change upperHalf.indicator ψ z = _ at hz
    rwa [Set.indicator_of_mem hzH] at hz
  have htail : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ v : ℂ, ‖v‖ = 1 ∧
      ∀ u ∈ Icc (0 : ℝ) ε, ∃ r : ℝ, 0 ≤ r ∧
        ξ (L.extend (if first then u else 1 - u) : ℂ) = (r : ℂ) * v := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst m
      have hconst : ψ (z₀ : ℂ) = deriv ξ (z₀ : ℂ) ^ 2 := by
        have h := hξψ.self_of_nhds
        norm_num at h
        exact h
      have hψne : ψ (z₀ : ℂ) ≠ 0 := by
        rw [hconst]
        exact pow_ne_zero 2 hξd
      have hderiv : ∀ᶠ z in 𝓝 (z₀ : ℂ), deriv ξ z ^ 2 = ψ z :=
        hξψ.mono fun z hz => by norm_num at hz; exact hz.symm
      exact hordinary R q hq (Γ := Γ) (p := p) hp L hSmooth hSeg first hψne
        ξ hξ hξ0 hξd hderiv
    · have hψ0 : ψ (z₀ : ℂ) = 0 := by
        have h := hξψ.self_of_nhds
        rw [hξ0, zero_pow hm.ne', mul_zero, zero_mul] at h
        exact h
      exact hzero R q hq (Γ := Γ) (p := p) hp L hSmooth hSeg first hψ0
        m hm ξ hξ hξ0 hξd hξψ
  obtain ⟨ε, hε, _hε1, v, hv, htail⟩ := htail
  obtain ⟨r, W, hr, hW, hsub, han, hinj, hlower⟩ :=
    native_model_neighborhood R q hq hp z₀ m ξ hξ hξ0 hξd hξψ
  have hN : {u : ℝ | L.extend u ∈ W ∧ (L.extend u : ℂ) ∈ ball (z₀ : ℂ) r} ∈ 𝓝 t₀ := by
    have hNW : {u : ℝ | L.extend u ∈ W} ∈ 𝓝 t₀ :=
      L.continuous_extend.continuousAt.preimage_mem_nhds (by rw [hstart]; exact hW)
    have hNB : {u : ℝ | (L.extend u : ℂ) ∈ ball (z₀ : ℂ) r} ∈ 𝓝 t₀ :=
      (UpperHalfPlane.continuous_coe.comp L.continuous_extend).continuousAt.preimage_mem_nhds
        (by
          change ball (z₀ : ℂ) r ∈ 𝓝 (L.extend t₀ : ℂ)
          rw [hstart]
          exact isOpen_ball.mem_nhds (mem_ball_self hr))
    exact inter_mem hNW hNB
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.mem_nhds_iff.1 hN
  let η : ℝ := min ε δ₀ / 2
  have hη : 0 < η := div_pos (lt_min hε hδ₀) (by norm_num)
  have hηε : η ≤ ε := by dsimp only [η]; linarith [min_le_left ε δ₀]
  have hηδ : η < δ₀ := by dsimp only [η]; linarith [min_le_right ε δ₀]
  obtain ⟨K, hK⟩ := nativeH_lipschitz_of_length_lt_top (qH : UpperHalfPlane → ℂ → ℂ) L
    (quadraticLengthPath_lt_top_of_piecewiseSmooth upperHalfNativeSurface qH L hSmooth)
  refine ⟨η / 2, div_pos hη (by norm_num), ?_⟩
  intro s hs t ht hleft hst hright
  have hnear : ∀ u ∈ Icc s t, |u - t₀| < η := by
    intro u hu
    apply abs_lt.mpr
    change t₀ - η / 2 < s at hleft
    change t < t₀ + η / 2 at hright
    constructor <;> linarith [hu.1, hu.2]
  have hu01 : ∀ u ∈ Icc s t, u ∈ Icc (0 : ℝ) 1 :=
    fun u hu => ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
  have hdata : ∀ u ∈ Icc s t, L.extend u ∈ W ∧ (L.extend u : ℂ) ∈ ball (z₀ : ℂ) r := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    exact (hnear u hu).trans hηδ
  have hRay : ∀ u ∈ Icc s t, ∃ r : ℝ, 0 ≤ r ∧ ξ (L.extend u : ℂ) = (r : ℂ) * v := by
    intro u hu
    have hc := hnear u hu
    have hI := hu01 u hu
    cases first
    · have hpar : 1 - u ∈ Icc (0 : ℝ) ε := by
        change |u - 1| < η at hc
        obtain ⟨hc1, hc2⟩ := abs_lt.mp hc
        constructor <;> linarith [hI.1, hI.2]
      obtain ⟨r', hr', heq⟩ := htail (1 - u) hpar
      change ξ (L.extend (1 - (1 - u)) : ℂ) = (r' : ℂ) * v at heq
      rw [show (1 : ℝ) - (1 - u) = u by ring] at heq
      exact ⟨r', hr', heq⟩
    · have hpar : u ∈ Icc (0 : ℝ) ε := by
        change |u - 0| < η at hc
        obtain ⟨hc1, hc2⟩ := abs_lt.mp hc
        constructor <;> linarith [hI.1, hI.2]
      exact htail u hpar
  have hKst := hK.mono (Icc_subset_Icc hs.1 ht.2)
  obtain ⟨Kξ, hKξ⟩ := s25e_comp_lipschitz isOpen_ball
    (fun z hz => (han z (ball_subset_closedBall hz)).1.differentiableAt.differentiableWithinAt)
    hKst (fun u hu => (hdata u hu).2)
  have hi : InjOn (fun u : ℝ => ξ (L.extend u : ℂ)) (Icc s t) := by
    intro u hu w hw heq
    have hco := hinj (ball_subset_closedBall (hdata u hu).2)
      (ball_subset_closedBall (hdata w hw).2) heq
    have hpath : L ⟨u, hu01 u hu⟩ = L ⟨w, hu01 w hw⟩ := by
      have h := UpperHalfPlane.coe_injective hco
      simpa only [L.extend_apply (hu01 u hu), L.extend_apply (hu01 w hw)] using h
    exact congrArg (fun z : unitInterval => (z : ℝ)) (hSeg.1 hpath)
  apply le_antisymm
  · rw [native_lengthOn_eq_model_integral R q hp z₀ m ξ r hr hsub han hinj
      L s t hs.1 hst ht.2 ⟨K, hKst⟩ (fun u hu => (hdata u hu).2)]
    have hcost := model_cost_le_distance_of_ray_image m hst hKξ hi v hv hRay
    exact hcost.trans (le_iInf fun δ =>
      hlower (L.extend s) (hdata s (left_mem_Icc.mpr hst.le)).1
        (L.extend t) (hdata t (right_mem_Icc.mpr hst.le)).1 δ)
  · obtain ⟨δ, _, hδ⟩ := s25i_subpath_length (q := (qH : UpperHalfPlane → ℂ → ℂ)) L hs.1 hst ht.2
    exact (iInf_le _ δ).trans hδ

private theorem native_segment_interior_local_minimum
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (L : Path a b),
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface L →
        IsQuadraticSegment upperHalfNativeSurface qH L.toContinuousMap →
        ∀ t₀ : ℝ, 0 < t₀ → t₀ < 1 → ∃ δ : ℝ, 0 < δ ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            t₀ - δ < s → s < t → t < t₀ + δ →
            phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) L s t =
              phiDistRS (qH : UpperHalfPlane → ℂ → ℂ) (L.extend s) (L.extend t) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  let := upperHalfNativeSurface.toRiemannAtlas.isManifold
  dsimp only
  intro a b L hSmooth hSeg t₀ ht₀0 ht₀1
  let u₀ : unitInterval := ⟨t₀, ht₀0.le, ht₀1.le⟩
  let z₀ : UpperHalfPlane := L u₀
  have hstart : L.extend t₀ = z₀ := L.extend_apply u₀.property
  obtain ⟨hreg, e, hEtar, hEan, hE0, hEcoeff, ta, tb, hat, hbt, hmap, himage⟩ :=
    hSeg.2 u₀ ht₀0 ht₀1
  rw [native_chartAt_fun (L.toContinuousMap u₀)] at hreg hE0 hmap himage
  change e.source ⊆ (chartAt ℂ z₀).target at hEtar
  have habT : ta < tb := hat.trans hbt
  have hchart := native_chartAt z₀
  have hEs0 : (z₀ : ℂ) ∈ e.source := by
    have h := (hmap u₀ ⟨hat.le, hbt.le⟩).2
    exact h
  have hEa : AnalyticAt ℂ (e : ℂ → ℂ) (z₀ : ℂ) := hEan _ hEs0
  have hE0' : e (z₀ : ℂ) = 0 := hE0
  have hreg' : (qH : UpperHalfPlane → ℂ → ℂ) z₀ (z₀ : ℂ) ≠ 0 := hreg
  have hEd : deriv (e : ℂ → ℂ) (z₀ : ℂ) ≠ 0 := by
    intro hzero
    apply hreg'
    have heq := hEcoeff _ hEs0
    change deriv (e : ℂ → ℂ) (z₀ : ℂ) ^ 2 =
      (qH : UpperHalfPlane → ℂ → ℂ) z₀ (z₀ : ℂ) at heq
    rw [← heq, hzero]
    norm_num
  have htarget : (chartAt ℂ z₀).target = upperHalf := by
    rw [hchart]
    change (UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph
      UpperHalfPlane.coe).target = _
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, UpperHalfPlane.range_coe]
    rfl
  have hψnormal : ∀ᶠ z in 𝓝 (z₀ : ℂ),
      ψ z = (((0 : ℕ) + 2 : ℂ) / 2) ^ 2 * e z ^ 0 * deriv (e : ℂ → ℂ) z ^ 2 := by
    filter_upwards [e.open_source.mem_nhds hEs0] with z hz
    have h := hEcoeff z hz
    have hzH : z ∈ upperHalf := by
      rw [← htarget]
      exact hEtar hz
    change deriv (e : ℂ → ℂ) z ^ 2 = upperHalf.indicator ψ z at h
    rw [Set.indicator_of_mem hzH] at h
    norm_num
    exact h.symm
  obtain ⟨r, W, hr, hW, hsub, han, hinj, hlower⟩ :=
    native_model_neighborhood R q hq hp z₀ 0 (e : ℂ → ℂ) hEa hE0' hEd hψnormal
  have hN : Ioo (ta : ℝ) (tb : ℝ) ∩
      {u : ℝ | L.extend u ∈ W ∧ (L.extend u : ℂ) ∈ ball (z₀ : ℂ) r} ∈ 𝓝 t₀ := by
    have hNW : {u : ℝ | L.extend u ∈ W} ∈ 𝓝 t₀ :=
      L.continuous_extend.continuousAt.preimage_mem_nhds (by rw [hstart]; exact hW)
    have hNB : {u : ℝ | (L.extend u : ℂ) ∈ ball (z₀ : ℂ) r} ∈ 𝓝 t₀ :=
      (UpperHalfPlane.continuous_coe.comp L.continuous_extend).continuousAt.preimage_mem_nhds
        (by
          change ball (z₀ : ℂ) r ∈ 𝓝 (L.extend t₀ : ℂ)
          rw [hstart]
          exact isOpen_ball.mem_nhds (mem_ball_self hr))
    exact inter_mem (isOpen_Ioo.mem_nhds ⟨hat, hbt⟩) (inter_mem hNW hNB)
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.mem_nhds_iff.1 hN
  have hsrca : (L ta : ℂ) ∈ e.source := by
    exact (hmap ta (left_mem_Icc.mpr habT.le)).2
  have hsrcb : (L tb : ℂ) ∈ e.source := by
    exact (hmap tb (right_mem_Icc.mpr habT.le)).2
  have hAB : e (L ta : ℂ) ≠ e (L tb : ℂ) := by
    intro heq
    have hc := e.injOn hsrca hsrcb heq
    exact habT.ne (hSeg.1 (UpperHalfPlane.coe_injective hc))
  obtain ⟨K, hK⟩ := nativeH_lipschitz_of_length_lt_top (qH : UpperHalfPlane → ℂ → ℂ) L
    (quadraticLengthPath_lt_top_of_piecewiseSmooth upperHalfNativeSurface qH L hSmooth)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro s hs t ht hleft hst hright
  have hu01 : ∀ u ∈ Icc s t, u ∈ Icc (0 : ℝ) 1 :=
    fun u hu => ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
  have hdata : ∀ u ∈ Icc s t, u ∈ Ioo (ta : ℝ) (tb : ℝ) ∧
      L.extend u ∈ W ∧ (L.extend u : ℂ) ∈ ball (z₀ : ℂ) r := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hu.1, hu.2]
  have hKst := hK.mono (Icc_subset_Icc hs.1 ht.2)
  obtain ⟨Kξ, hKξ⟩ := s25e_comp_lipschitz isOpen_ball
    (fun z hz => (han z (ball_subset_closedBall hz)).1.differentiableAt.differentiableWithinAt)
    hKst (fun u hu => (hdata u hu).2.2)
  have hi : InjOn (fun u : ℝ => e (L.extend u : ℂ)) (Icc s t) := by
    intro u hu w hw heq
    have hc := hinj (ball_subset_closedBall (hdata u hu).2.2)
      (ball_subset_closedBall (hdata w hw).2.2) heq
    have hpath : L ⟨u, hu01 u hu⟩ = L ⟨w, hu01 w hw⟩ := by
      have h := UpperHalfPlane.coe_injective hc
      simpa only [L.extend_apply (hu01 u hu), L.extend_apply (hu01 w hw)] using h
    exact congrArg (fun z : unitInterval => (z : ℝ)) (hSeg.1 hpath)
  have hImage : ∀ u ∈ Icc s t,
      e (L.extend u : ℂ) ∈ segment ℝ (e (L ta : ℂ)) (e (L tb : ℂ)) := by
    intro u hu
    have huT : (⟨u, hu01 u hu⟩ : unitInterval) ∈ Icc ta tb :=
      ⟨(hdata u hu).1.1.le, (hdata u hu).1.2.le⟩
    have hm : e (L ⟨u, hu01 u hu⟩ : ℂ) ∈
        (fun w : unitInterval => e (L w : ℂ)) '' Icc ta tb :=
      ⟨⟨u, hu01 u hu⟩, huT, rfl⟩
    change (fun w : unitInterval => e (L w : ℂ)) '' Icc ta tb =
      segment ℝ (e (L ta : ℂ)) (e (L tb : ℂ)) at himage
    rw [himage] at hm
    simpa only [L.extend_apply (hu01 u hu)] using hm
  apply le_antisymm
  · rw [native_lengthOn_eq_model_integral R q hp z₀ 0 (e : ℂ → ℂ) r hr hsub han hinj
      L s t hs.1 hst ht.2 ⟨K, hKst⟩ (fun u hu => (hdata u hu).2.2)]
    have hcost := model_flat_cost_le_distance_of_segment_image hst hKξ hi
      (e (L ta : ℂ)) (e (L tb : ℂ)) hAB hImage
    exact hcost.trans (le_iInf fun δ =>
      hlower (L.extend s) (hdata s (left_mem_Icc.mpr hst.le)).2.1
        (L.extend t) (hdata t (right_mem_Icc.mpr hst.le)).2.1 δ)
  · obtain ⟨δ, _, hδ⟩ := s25i_subpath_length (q := (qH : UpperHalfPlane → ℂ → ℂ)) L hs.1 hst ht.2
    exact (iInf_le _ δ).trans hδ

/-- The SAME source-smooth segment is locally shortest in its actual native
metric. Only the two explicit classical endpoint image inputs are deferred. -/
theorem native_sourceSmooth_segment_isPhiGeodesic
    (hordinary : NativeQuadraticOrdinaryEndpointRay) (hzero : NativeQuadraticZeroEndpointRay)
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (L : Path a b),
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface L →
        IsQuadraticSegment upperHalfNativeSurface qH L.toContinuousMap →
        IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) L := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
    (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b L hSmooth hSeg t₀ ht₀
  by_cases h0 : t₀ = 0
  · subst t₀
    exact native_segment_endpoint_local_minimum hordinary hzero R q hq hp L hSmooth hSeg true
  by_cases h1 : t₀ = 1
  · subst t₀
    exact native_segment_endpoint_local_minimum hordinary hzero R q hq hp L hSmooth hSeg false
  have ht₀0 : 0 < t₀ := lt_of_le_of_ne ht₀.1 (Ne.symm h0)
  have ht₀1 : t₀ < 1 := lt_of_le_of_ne ht₀.2 h1
  exact native_segment_interior_local_minimum R q hq hp L hSmooth hSeg t₀ ht₀0 ht₀1

/-- The same injective Lipschitz ray parameter has its exact radial
increment as weighted length. Its own Lipschitz bound supplies the AC data. -/
theorem model_ray_integral_eq_radial_increment_of_rayImage
    (m : ℕ) (hm : 0 < m) {f : ℝ → ℂ} {s t : ℝ} (hst : s < t)
    {K : NNReal} (hf : LipschitzOnWith K f (Icc s t))
    (hi : InjOn f (Icc s t)) (v : ℂ) (hv : ‖v‖ = 1)
    (himage : ∀ u ∈ Icc s t, ∃ r : ℝ, 0 ≤ r ∧ f u = (r : ℂ) * v) :
    (∫⁻ u in Ioo s t,
      phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) (f u) *
        ‖deriv f u‖ₑ) =
      ENNReal.ofReal (|‖f t‖ ^ (((m : ℝ) + 2) / 2) -
        ‖f s‖ ^ (((m : ℝ) + 2) / 2)|) := by
  obtain ⟨ρ, d, hρc, hρm, hρ0, hline⟩ :=
    clock_of_injective_ray_image hst.le hf hi v hv himage
  have hnorm (u : ℝ) (hu : u ∈ Icc s t) : ‖f u‖ = d * ρ u := by
    rw [hline u hu, norm_mul, hv, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (hρ0 u hu)]
  have hlength := model_ray_integral_of_monotone_clock m hm hst hf ρ hρc hρm d hρ0 v hv hline
  have hsNorm := hnorm s (left_mem_Icc.mpr hst.le)
  have htNorm := hnorm t (right_mem_Icc.mpr hst.le)
  rw [← hsNorm, ← htNorm] at hlength
  exact hlength

/-- The same original native subinterval length is its actual normalized-coordinate integral. -/
theorem native_quadratic_lengthOn_eq_model_integral
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ (z₀ : UpperHalfPlane) (m : ℕ) (ξ : ℂ → ℂ) (r : ℝ), 0 < r →
        closedBall (z₀ : ℂ) r ⊆ upperHalf →
        (∀ z ∈ closedBall (z₀ : ℂ) r, AnalyticAt ℂ ξ z ∧ deriv ξ z ≠ 0 ∧
          ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2) →
        InjOn ξ (closedBall (z₀ : ℂ) r) →
        ∀ {a b : UpperHalfPlane} (L : Path a b) (s t : ℝ),
          0 ≤ s → s < t → t ≤ 1 →
          (∃ K : NNReal, LipschitzOnWith K (fun u : ℝ => (L.extend u : ℂ)) (Icc s t)) →
          (∀ u ∈ Icc s t, (L.extend u : ℂ) ∈ ball (z₀ : ℂ) r) →
          phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) L s t =
            ∫⁻ u in Ioo s t,
              phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m)
                (ξ (L.extend u : ℂ)) *
              ‖deriv (fun v : ℝ => ξ (L.extend v : ℂ)) u‖ₑ := by
  exact native_lengthOn_eq_model_integral R q (Γ := Γ) (p := p)

/-- A genuine normalized coordinate gives a native neighborhood and a lower bound for every actual path. -/
theorem native_quadratic_model_neighborhood
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ (z₀ : UpperHalfPlane) (m : ℕ) (ξ : ℂ → ℂ),
        AnalyticAt ℂ ξ (z₀ : ℂ) → ξ (z₀ : ℂ) = 0 → deriv ξ (z₀ : ℂ) ≠ 0 →
        (∀ᶠ z in 𝓝 (z₀ : ℂ),
          ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2) →
        ∃ (r : ℝ) (W : Set UpperHalfPlane), 0 < r ∧ W ∈ 𝓝 z₀ ∧
          closedBall (z₀ : ℂ) r ⊆ upperHalf ∧
          (∀ z ∈ closedBall (z₀ : ℂ) r, AnalyticAt ℂ ξ z ∧ deriv ξ z ≠ 0 ∧
            ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2) ∧
          InjOn ξ (closedBall (z₀ : ℂ) r) ∧
          ∀ a ∈ W, ∀ b ∈ W, ∀ δ : Path a b,
            metricDist univ (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m))
              (ξ (a : ℂ)) (ξ (b : ℂ)) ≤ phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ := by
  exact native_model_neighborhood R q hq (Γ := Γ) (p := p)

end LowDimensionalTopology.Geometry.Teichmuller
