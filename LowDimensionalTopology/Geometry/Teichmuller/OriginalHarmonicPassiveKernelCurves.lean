module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPassiveCauchyData
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPassiveL2Curve
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPassiveRegularL2Curve
public import LowDimensionalTopology.Geometry.Quasiconformal.HilbertLpOperator
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.Algebra.Module.Star
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Actual L2 input curves and ordinary regular pairings

The existing Hilbert continuous linear map differentiates genuine L2 classes.
A countable almost-everywhere subsequence and a genuine ordinary bilinear
pairing are retained separately from scalar pointwise kernel derivatives.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

private theorem actual_point_parameter_variation
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℂ) :
    HasDerivAt (fun s : ℂ => canonicalBiparameterFamily R p q s 0 z)
      (ahVar (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w) z) 0 := by
  let μ : ℂ → ℂ := fun w => if w.im < 0 then 0 else harmonicPlane R p q w
  have hcoeff (s : ℂ) : harmonicBiparameterCoefficient R p q s 0 =
      fun w : ℂ => s * μ w := by
    funext w
    by_cases hw : w.im < 0 <;>
      simp only [harmonicBiparameterCoefficient, μ, hw, ite_true, ite_false, zero_mul, mul_zero]
  have hzero : canonicalBiparameterFamily R p q 0 0 = id := by
    unfold canonicalBiparameterFamily
    rw [hcoeff]
    have he : (fun w : ℂ => (0 : ℂ) * μ w) = 0 := by funext w; simp only [zero_mul, Pi.zero_apply]
    rw [he, bB_l_normalizedSolution_zero]
  obtain ⟨ε, hε, hspec, _, _⟩ := canonicalBiparameterFamily_separately_holomorphic R p hp q
  have hzε : ‖(0 : ℂ)‖ < ε := by simpa only [norm_zero] using hε
  have hμ : ∀ s ∈ ball (0 : ℂ) ε,
      IsBeltramiCoeff (fun w : ℂ => s * μ w) univ (1 / 2) := by
    intro s hs
    rw [← hcoeff]
    exact (hspec s 0 (mem_ball_zero_iff.mp hs) hzε).1
  have hf : ∀ s ∈ ball (0 : ℂ) ε,
      IsNormalizedSolution (canonicalBiparameterFamily R p q s 0)
        (fun w : ℂ => s * μ w) := by
    intro s hs
    rw [← hcoeff]
    exact (hspec s 0 (mem_ball_zero_iff.mp hs) hzε).2
  have hd := ahT_hasDerivAt isOpen_ball (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hμ
    (fun w => by
      let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
      exact (differentiable_id.mul_const (μ w)).differentiableOn)
    hf (mem_ball_self hε) z
  have hdot : ahT_dot (fun w => deriv (fun s : ℂ => s * μ w) 0)
      (fun w : ℂ => (0 : ℂ) * μ w) (canonicalBiparameterFamily R p q 0 0) = μ := by
    rw [hzero]
    funext w
    have hinv : Function.invFunOn (id : ℂ → ℂ) univ w = w :=
      (injOn_id univ).leftInvOn_invFunOn (mem_univ w)
    have hdz : dz id w = 1 := by
      simp only [dz, fderiv_id, ContinuousLinearMap.id_apply]
      rw [I_mul_I]
      ring
    have hder : deriv (fun s : ℂ => s * μ w) 0 = μ w := by simp
    simp only [ahT_dot, hinv, zero_mul, map_zero, mul_zero, sub_zero,
      hdz, map_one, div_one, mul_one, hder]
  rw [hdot, hzero] at hd
  exact hd

private theorem actual_active_variation_eq_normalized
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ahVar (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w) =
      normalizedCauchyTOn upperHalf (harmonicPlane R p q) := by
  let μ : ℂ → ℂ := fun w => if w.im < 0 then 0 else harmonicPlane R p q w
  have hzero (w : ℂ) (hw : w.im ≤ 0) : μ w = 0 := by
    by_cases hw' : w.im < 0
    · simp only [μ, hw', ite_true]
    · have him : w.im = 0 := le_antisymm hw (not_lt.mp hw')
      simp only [μ, harmonicPlane, him, Complex.ofReal_zero,
        zero_pow two_ne_zero, zero_mul, ite_self]
  rw [← b36_p_normalizedCauchyT_eq_ahVar hzero]
  funext z
  unfold normalizedCauchyTOn
  congr 1
  apply setIntegral_congr_fun isOpen_upperHalf.measurableSet
  intro w hw
  change 0 < w.im at hw
  simp only [μ, not_lt.mpr hw.le, ite_false]

theorem actual_passive_point_first_variation
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : ℂ) :
    HasDerivAt (fun t : ℂ => canonicalBiparameterFamily R p q 0 t x)
      (conj (normalizedCauchyTOn upperHalf (harmonicPlane R p q) (conj x))) 0 := by
  obtain ⟨ε, hε, _, hreflect, _, _⟩ :=
    canonicalBiparameterFamily_spatial_c1_compact_control R p hp q
  have hfirst := (actual_point_parameter_variation R p hp q (conj x)).conj_conj
  have he : (fun t : ℂ => canonicalBiparameterFamily R p q 0 t x) =ᶠ[𝓝 0]
      fun t : ℂ => conj (canonicalBiparameterFamily R p q (conj t) 0 (conj x)) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hε] with t ht
    have h := congrFun (hreflect 0 t
      (by simpa only [norm_zero] using hε) (mem_ball_zero_iff.mp ht)) x
    simpa only [map_zero] using h
  have hfirst' : HasDerivAt
      (fun t : ℂ => conj (canonicalBiparameterFamily R p q (conj t) 0 (conj x)))
      (conj (ahVar (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
        (conj x))) 0 := by
    simpa only [Function.comp_def, map_zero] using hfirst
  rw [actual_active_variation_eq_normalized R p q] at hfirst'
  exact hfirst'.congr_of_eventuallyEq he

theorem actual_passive_base_variation_holomorphic
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    DifferentiableOn ℂ
      (fun x : ℂ => conj (normalizedCauchyTOn upperHalf (harmonicPlane R p q) (conj x)))
      upperHalf := by
  let M : ℝ := ‖(NativeHarmonicBeltrami.ofQuadratic R p hp q).val‖
  have hM : 0 ≤ M := norm_nonneg _
  have hμ : IsBeltramiCoeff (harmonicPlane R p q) upperHalf M := by
    have hb := planeRepresentative_isBeltramiCoeff
      (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
    have hae : planeRepresentative (NativeHarmonicBeltrami.ofQuadratic R p hp q).val =ᵐ[
        volume.restrict upperHalf] harmonicPlane R p q :=
      NativeHarmonicBeltrami.planeRepresentative_ofQuadratic_ae R p hp q
    refine ⟨hb.1.congr hae, ?_⟩
    filter_upwards [hae, hb.2] with w hw hbound
    rwa [← hw]
  intro x hx
  have hxL : conj x ∈ lowerHalf := by
    change (conj x).im < 0
    simpa only [conj_im] using neg_lt_zero.mpr hx
  have hN := ((b36_p_hasDerivAt_N hM hμ.1 hμ.2 hxL).2).const_mul
    (-(1 / Real.pi : ℂ))
  have hV : HasDerivAt (normalizedCauchyTOn upperHalf (harmonicPlane R p q))
      (-(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf,
        harmonicPlane R p q w *
          (1 / (w - conj x) ^ 2 - 1 / (w * (w - 1)))) (conj x) := by
    simpa only [b36_p_normalizedCauchyT_eq] using hN
  have hc := hV.conj_conj
  have hd : DifferentiableAt ℂ
      (fun y : ℂ => conj (normalizedCauchyTOn upperHalf (harmonicPlane R p q) (conj y))) x := by
    simpa only [Function.comp_def, Complex.conj_conj] using hc.differentiableAt
  exact hd.differentiableWithinAt

theorem actual_passive_deriv_first_variation
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : ℍ) :
    HasDerivAt (fun t : ℂ => deriv (canonicalBiparameterFamily R p q 0 t) x)
      (deriv (fun y : ℂ =>
        conj (normalizedCauchyTOn upperHalf (harmonicPlane R p q) (conj y))) x) 0 := by
  let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
  obtain ⟨εQ, hεQ, hdata⟩ := actual_passive_conformal_data R p hp q
  obtain ⟨εP, hεP, _, _, hparam, _⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control R p hp q
  obtain ⟨E, hE, _, _, hlocal, _⟩ :=
    canonicalBiparameterFamily_spatial_c1_compact_control R p hp q
  obtain ⟨r, C, hr, _, _, hrH, hbound⟩ := hlocal 0 (mem_ball_self hE) x x.im_pos
  let σ := min εQ (min εP E)
  have hσ : 0 < σ := lt_min hεQ (lt_min hεP hE)
  have hσQ : σ ≤ εQ := min_le_left _ _
  have hσP : σ ≤ εP := (min_le_right _ _).trans (min_le_left _ _)
  have hσE : σ ≤ E := (min_le_right _ _).trans (min_le_right _ _)
  let F := fun t : ℂ => canonicalBiparameterFamily R p q 0 t
  let V : ℂ → ℂ := fun y =>
    conj (normalizedCauchyTOn upperHalf (harmonicPlane R p q) (conj y))
  have hFt (t : ℂ) (ht : t ∈ ball (0 : ℂ) σ) (u : ℂ) (hu : u ∈ ball (x : ℂ) r) :
      DifferentiableAt ℂ (F t) u := by
    have hh := (hdata t (mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ht).trans_le hσQ))).2
    exact hh.differentiableAt (isOpen_upperHalf.mem_nhds (hrH hu))
  have hDp (u : ℂ) (hu : u ∈ ball (x : ℂ) r) :
      DifferentiableOn ℂ (fun t => deriv (F t) u) (ball 0 σ) := by
    apply ((((hparam 0 (by simpa only [norm_zero] using hεP) u (Or.inl (hrH hu))).1).mono
      (ball_subset_ball hσP))).congr
    intro t ht
    exact (dz_eq_deriv (hFt t ht u hu)).symm
  have hDn (u : ℂ) (hu : u ∈ ball (x : ℂ) r) (t : ℂ) (ht : t ∈ ball (0 : ℂ) σ) :
      ‖deriv (F t) u‖ ≤ C := by
    rw [← dz_eq_deriv (hFt t ht u hu)]
    exact (norm_dz_le_real_derivative (F t) u).trans
      (hbound 0 (mem_ball_self hr) t (ball_subset_ball hσE ht) u hu)
  let Q : ℂ → ℂ → ℂ := fun t u => (F t u - F 0 u) / t
  let Q' : ℂ → ℂ → ℂ := fun t u => (deriv (F t) u - deriv (F 0) u) / t
  let D : ℂ → ℂ := fun u => deriv (fun t : ℂ => deriv (F t) u) 0
  have hQu : TendstoUniformlyOn Q' D (𝓝[≠] (0 : ℂ)) (ball (x : ℂ) r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have hl : Tendsto (fun t : ℂ => 8 * C / σ ^ 2 * ‖t‖)
        (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using
        ((continuous_norm.tendsto (0 : ℂ)).const_mul (8 * C / σ ^ 2)).mono_left
          nhdsWithin_le_nhds
    filter_upwards [hl.eventually (gt_mem_nhds hδ), self_mem_nhdsWithin,
      nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (half_pos hσ))] with t hδt htne ht u hu
    have hne : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using htne
    rw [dist_eq_norm, norm_sub_rev]
    have he : ‖Q' t u - D u‖ ≤ 8 * C / σ ^ 2 * ‖t‖ := by
      simpa only [Q', D, zero_add] using
        bB_h0_diffQuot_le hσ (hDp u hu) (hDn u hu) hne (mem_ball_zero_iff.mp ht)
    exact he.trans_lt hδt
  have hQs : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ), ∀ u ∈ ball (x : ℂ) r,
      HasDerivAt (Q t) (Q' t u) u := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hσ)] with t ht u hu
    exact ((hFt t ht u hu).hasDerivAt.sub
      (hFt 0 (mem_ball_self hσ) u hu).hasDerivAt).div_const t
  have hQp (u : ℂ) (_hu : u ∈ ball (x : ℂ) r) :
      Tendsto (fun t : ℂ => Q t u) (𝓝[≠] 0) (𝓝 (V u)) := by
    simpa only [Q, V, F, zero_add, div_eq_mul_inv, smul_eq_mul, mul_comm] using
      (actual_passive_point_first_variation R p hp q u).tendsto_slope_zero
  have hDV : HasDerivAt V (D x) (x : ℂ) :=
    hasDerivAt_of_tendstoUniformlyOn isOpen_ball hQu hQs hQp (mem_ball_self hr)
  have hV : DifferentiableAt ℂ V (x : ℂ) :=
    (actual_passive_base_variation_holomorphic R p hp q).differentiableAt
      (isOpen_upperHalf.mem_nhds x.im_pos)
  have hD : D x = deriv V x := hDV.unique hV.hasDerivAt
  have h := (hDp x (mem_ball_self hr)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_self hσ))
  have hh : HasDerivAt (fun t : ℂ => deriv (F t) x) (D x) 0 := h.hasDerivAt
  rw [hD] at hh
  simpa only [F, V] using hh

private theorem normalized_square_variation_identity {a b w : ℂ}
    (hab : a ≠ b) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwa : w ≠ a) (hwb : w ≠ b) :
    ((1 / (w - a) ^ 2 - 1 / (w * (w - 1))) +
      (1 / (w - b) ^ 2 - 1 / (w * (w - 1)))) / (a - b) ^ 2 -
        2 * (ahKer a w - ahKer b w) / (a - b) ^ 3 =
      1 / ((w - a) ^ 2 * (w - b) ^ 2) := by
  unfold ahKer
  field_simp [sub_ne_zero.mpr hab, hw0, sub_ne_zero.mpr hw1,
    sub_ne_zero.mpr hwa, sub_ne_zero.mpr hwb]
  ring

private theorem actual_normalized_square_variation_integral
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {a b : ℂ} (ha : a ∈ lowerHalf) (hb : b ∈ lowerHalf) (hab : a ≠ b) :
    let V := normalizedCauchyTOn upperHalf (harmonicPlane R p q)
    IntegrableOn (fun w : ℂ => harmonicPlane R p q w /
      ((w - a) ^ 2 * (w - b) ^ 2)) upperHalf ∧
      (deriv V a + deriv V b) / (a - b) ^ 2 - 2 * (V a - V b) / (a - b) ^ 3 =
        -(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf,
          harmonicPlane R p q w / ((w - a) ^ 2 * (w - b) ^ 2) := by
  dsimp only
  let μ := harmonicPlane R p q
  let V := normalizedCauchyTOn upperHalf μ
  let M : ℝ := ‖(NativeHarmonicBeltrami.ofQuadratic R p hp q).val‖
  have hM : 0 ≤ M := norm_nonneg _
  have hμ : IsBeltramiCoeff μ upperHalf M := by
    have hraw := planeRepresentative_isBeltramiCoeff
      (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
    have hae : planeRepresentative (NativeHarmonicBeltrami.ofQuadratic R p hp q).val =ᵐ[
        volume.restrict upperHalf] μ :=
      NativeHarmonicBeltrami.planeRepresentative_ofQuadratic_ae R p hp q
    refine ⟨hraw.1.congr hae, ?_⟩
    filter_upwards [hae, hraw.2] with w hw hbound
    rwa [← hw]
  let A : ℂ → ℂ → ℂ := fun v w => μ w * ahKer v w
  let C : ℂ → ℂ → ℂ := fun v w =>
    μ w * (1 / (w - v) ^ 2 - 1 / (w * (w - 1)))
  have hAi (v : ℂ) : IntegrableOn (A v) upperHalf :=
    (ah_ker_integrable v).integrableOn.bdd_mul hμ.1 hμ.2
  have hCi (v : ℂ) (hv : v ∈ lowerHalf) : IntegrableOn (C v) upperHalf :=
    (b36_p_hasDerivAt_N hM hμ.1 hμ.2 hv).1
  have hDv (v : ℂ) (hv : v ∈ lowerHalf) :
      deriv V v = -(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf, C v w := by
    have hh : HasDerivAt V (-(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf, C v w) v := by
      simpa only [V, C, b36_p_normalizedCauchyT_eq] using
        ((b36_p_hasDerivAt_N hM hμ.1 hμ.2 hv).2).const_mul (-(1 / Real.pi : ℂ))
    exact hh.deriv
  have hVv (v : ℂ) : V v = -(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf, A v w :=
    congrFun (b36_p_normalizedCauchyT_eq μ) v
  let T₁ : ℂ → ℂ := fun w => (C a w + C b w) / (a - b) ^ 2
  let T₂ : ℂ → ℂ := fun w => 2 * (A a w - A b w) / (a - b) ^ 3
  have hT₁ : IntegrableOn T₁ upperHalf := by
    change Integrable T₁ (volume.restrict upperHalf)
    have haI : Integrable (C a) (volume.restrict upperHalf) := hCi a ha
    have hbI : Integrable (C b) (volume.restrict upperHalf) := hCi b hb
    simpa only [T₁, Pi.add_apply] using (haI.add hbI).div_const ((a - b) ^ 2)
  have hT₂ : IntegrableOn T₂ upperHalf := ((hAi a).sub' (hAi b)).const_mul 2 |>.div_const _
  have he : (fun w : ℂ => T₁ w - T₂ w) =ᵐ[volume.restrict upperHalf]
      fun w : ℂ => μ w / ((w - a) ^ 2 * (w - b) ^ 2) := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ)),
      ae_restrict_of_ae (volume.ae_ne (1 : ℂ)), ae_restrict_of_ae (volume.ae_ne a),
      ae_restrict_of_ae (volume.ae_ne b)] with w hw0 hw1 hwa hwb
    calc
      T₁ w - T₂ w = μ w *
          (((1 / (w - a) ^ 2 - 1 / (w * (w - 1))) +
            (1 / (w - b) ^ 2 - 1 / (w * (w - 1)))) / (a - b) ^ 2 -
              2 * (ahKer a w - ahKer b w) / (a - b) ^ 3) := by
        dsimp only [T₁, T₂, A, C]
        ring
      _ = _ := by rw [normalized_square_variation_identity hab hw0 hw1 hwa hwb]; ring
  have hInt : (∫ w : ℂ in upperHalf, T₁ w - T₂ w) =
      ((∫ w : ℂ in upperHalf, C a w) + (∫ w : ℂ in upperHalf, C b w)) / (a - b) ^ 2 -
        2 * ((∫ w : ℂ in upperHalf, A a w) - (∫ w : ℂ in upperHalf, A b w)) /
          (a - b) ^ 3 := by
    rw [integral_sub hT₁ hT₂]
    dsimp only [T₁, T₂]
    rw [integral_div, integral_add (hCi a ha) (hCi b hb), integral_div,
      integral_const_mul, integral_sub (hAi a) (hAi b)]
  refine ⟨(hT₁.sub' hT₂).congr he, ?_⟩
  calc
    (deriv V a + deriv V b) / (a - b) ^ 2 - 2 * (V a - V b) / (a - b) ^ 3 =
        -(1 / Real.pi : ℂ) *
          (((∫ w : ℂ in upperHalf, C a w) + (∫ w : ℂ in upperHalf, C b w)) / (a - b) ^ 2 -
            2 * ((∫ w : ℂ in upperHalf, A a w) - (∫ w : ℂ in upperHalf, A b w)) /
              (a - b) ^ 3) := by
      rw [hDv a ha, hDv b hb, hVv a, hVv b]
      ring
    _ = -(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf, T₁ w - T₂ w := by rw [hInt]
    _ = _ := by rw [integral_congr_ae he]

theorem actual_passive_regular_input_first_variation
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x y : ℍ)
    (hxy : (x : ℂ) ≠ (y : ℂ)) :
    IntegrableOn (fun w : ℂ => conj (harmonicPlane R p q w) /
      ((conj w - x) ^ 2 * (conj w - y) ^ 2)) upperHalf ∧
      HasDerivAt (fun t : ℂ => canonicalPassiveRegularKernelInput R p q x t y)
        (-(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf,
          conj (harmonicPlane R p q w) / ((conj w - x) ^ 2 * (conj w - y) ^ 2)) 0 := by
  let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
  let μ := harmonicPlane R p q
  let N := normalizedCauchyTOn upperHalf μ
  let V : ℂ → ℂ := fun v => conj (N (conj v))
  let F := fun t : ℂ => canonicalBiparameterFamily R p q 0 t
  let E : ℂ := (deriv V x + deriv V y) / ((x : ℂ) - y) ^ 2 -
    2 * (V x - V y) / ((x : ℂ) - y) ^ 3
  have ha : conj (x : ℂ) ∈ lowerHalf := by
    change (conj (x : ℂ)).im < 0
    simpa only [conj_im, UpperHalfPlane.coe_im] using neg_lt_zero.mpr x.im_pos
  have hb : conj (y : ℂ) ∈ lowerHalf := by
    change (conj (y : ℂ)).im < 0
    simpa only [conj_im, UpperHalfPlane.coe_im] using neg_lt_zero.mpr y.im_pos
  have hab : conj (x : ℂ) ≠ conj (y : ℂ) := by
    intro h
    apply hxy
    simpa only [Complex.conj_conj] using congrArg (fun v : ℂ => conj v) h
  obtain ⟨hcross, hcrossEq⟩ := actual_normalized_square_variation_integral R p hp q ha hb hab
  have hfun (w : ℂ) : conj (μ w / ((w - conj (x : ℂ)) ^ 2 *
      (w - conj (y : ℂ)) ^ 2)) =
      conj (μ w) / ((conj w - x) ^ 2 * (conj w - y) ^ 2) := by
    simp only [map_div₀, map_mul, map_pow, map_sub, Complex.conj_conj]
  have htarget : IntegrableOn (fun w : ℂ =>
      conj (μ w) / ((conj w - x) ^ 2 * (conj w - y) ^ 2)) upperHalf := by
    apply (Complex.conjCLE.toContinuousLinearMap.integrable_comp hcross).congr
    exact Eventually.of_forall fun w => by
      simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using hfun w
  have hDV (v : ℂ) : deriv V v = conj (deriv N (conj v)) := by
    simpa only [V, Function.comp_def] using congrFun (deriv_conj_conj (f := N)) v
  have hE : E = -(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf,
      conj (μ w) / ((conj w - x) ^ 2 * (conj w - y) ^ 2) := by
    calc
      E = conj ((deriv N (conj (x : ℂ)) + deriv N (conj (y : ℂ))) /
          (conj (x : ℂ) - conj (y : ℂ)) ^ 2 -
            2 * (N (conj (x : ℂ)) - N (conj (y : ℂ))) /
              (conj (x : ℂ) - conj (y : ℂ)) ^ 3) := by
        simp only [E, hDV, V, map_sub, map_add, map_div₀, map_pow,
          map_mul, map_ofNat, Complex.conj_conj]
      _ = conj (-(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf,
          μ w / ((w - conj (x : ℂ)) ^ 2 * (w - conj (y : ℂ)) ^ 2)) :=
        congrArg (fun v : ℂ => conj v) hcrossEq
      _ = _ := by
        rw [map_mul, ← integral_conj]
        have hc : conj (-(1 / Real.pi : ℂ)) = -(1 / Real.pi : ℂ) := by
          simp only [map_neg, map_div₀, map_one, conj_ofReal]
        rw [hc]
        congr 1
        exact setIntegral_congr_fun isOpen_upperHalf.measurableSet (fun w _ => hfun w)
  have hF0 : canonicalBiparameterFamily R p q 0 0 = id := by
    simpa only [map_zero] using
      (canonicalBiparameterFamily_diagonal R p q 0).trans (canonicalFamily_zero R p q)
  have hnum := (actual_passive_deriv_first_variation R p hp q x).fun_mul
    (actual_passive_deriv_first_variation R p hp q y)
  have hden := ((actual_passive_point_first_variation R p hp q (x : ℂ)).fun_sub
    (actual_passive_point_first_variation R p hp q (y : ℂ))).pow 2
  have hne : (F 0 x - F 0 y) ^ 2 ≠ 0 := by
    simpa only [F, hF0, id_eq] using pow_ne_zero 2 (sub_ne_zero.mpr hxy)
  have hq := (hnum.fun_div hden hne).sub_const
    ((1 : ℂ) / ((x : ℂ) - y) ^ 2)
  have hparam : HasDerivAt (fun t : ℂ => deriv (F t) x * deriv (F t) y /
      (F t x - F t y) ^ 2 - 1 / ((x : ℂ) - y) ^ 2) E 0 := by
    apply hq.congr_deriv
    dsimp only [F, E, V, N, μ]
    norm_num only [Pi.pow_apply, hF0, id_eq, deriv_id, one_mul, mul_one,
      Nat.reduceSub, pow_one]
    field_simp [sub_ne_zero.mpr hxy]
  obtain ⟨ε, hε, hdata⟩ := actual_passive_conformal_data R p hp q
  have he : (fun t : ℂ => canonicalPassiveRegularKernelInput R p q x t y) =ᶠ[𝓝 0]
      fun t : ℂ => deriv (F t) x * deriv (F t) y /
        (F t x - F t y) ^ 2 - 1 / ((x : ℂ) - y) ^ 2 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hε] with t ht
    have hhol := (hdata t ht).2
    rw [canonicalPassiveRegularKernelInput,
      indicator_of_mem (show (y : ℂ) ∈ upperHalf from y.im_pos)]
    rw [dz_eq_deriv (hhol.differentiableAt (isOpen_upperHalf.mem_nhds x.im_pos)),
      dz_eq_deriv (hhol.differentiableAt (isOpen_upperHalf.mem_nhds y.im_pos))]
  exact ⟨htarget, (hparam.congr_of_eventuallyEq he).congr_deriv hE⟩

private theorem actual_passive_hilbert_input_curve_derivative
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    let K := fun (t : ℂ) (η : ℍ) =>
      dz (canonicalBiparameterFamily R p q 0 t) η *
        dz (canonicalBiparameterFamily R p q 0 t) (conj (z : ℂ)) /
        (canonicalBiparameterFamily R p q 0 t η -
          canonicalBiparameterFamily R p q 0 t (conj (z : ℂ))) ^ 2
    let W := fun t => WeilPetersson.SourceKernel.upperExtension
      (fun η => harmonicPlane R p q η * K t η)
    ∃ (ε : ℝ) (J : ℂ → ℂ) (_hJ : MemLp J 2 (volume : Measure ℂ))
      (d : Lp ℂ 2 (volume : Measure ℂ)) (N : ℂ → Lp ℂ 2 (volume : Measure ℂ)),
      0 < ε ∧ Measurable J ∧
      (∀ᵐ η : ℂ,
        HasDerivAt (fun t => W t η) (J η) 0 ∧
        J η = WeilPetersson.SourceKernel.upperExtension
          (fun ξ => harmonicPlane R p q ξ * deriv (fun t => K t ξ) 0) η) ∧
      (d : ℂ → ℂ) =ᵐ[volume] hilbertH J ∧ HasDerivAt N d 0 ∧
      ∀ t : ℂ, ‖t‖ < ε → (N t : ℂ → ℂ) =ᵐ[volume] hilbertH (W t) := by
  dsimp only
  obtain ⟨ε, J, hJ, M, hε, hJm, hcanonical, hMderiv, hM⟩ :=
    canonicalPassiveFullKernelInput_hasDerivAt_toLp R p hp q z
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  obtain ⟨T, hTcoe⟩ :
      ∃ T : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ),
        ∀ f : Lp ℂ 2 (volume : Measure ℂ),
          (T f : ℂ → ℂ) =ᵐ[volume] hilbertH (f : ℂ → ℂ) := by
    have h : ∀ [_hLp : Fact (1 ≤ ENNReal.ofReal (2 : ℝ))],
        ∃ T : Lp ℂ (ENNReal.ofReal (2 : ℝ)) volume →L[ℂ]
          Lp ℂ (ENNReal.ofReal (2 : ℝ)) volume,
          ∀ f : Lp ℂ (ENNReal.ofReal (2 : ℝ)) volume,
            (T f : ℂ → ℂ) =ᵐ[volume] hilbertH (f : ℂ → ℂ) := by
      intro _hLp
      exact ⟨Quasiconformal.hilbertLp (p := 2) (by norm_num),
        Quasiconformal.hilbertLp_coeFn (p := 2) (by norm_num)⟩
    rw [htwo] at h
    exact h
  have hd : (T (hJ.toLp J) : ℂ → ℂ) =ᵐ[volume] hilbertH J := by
    have he := hilbertH_congr_ae hJ.coeFn_toLp
    exact (hTcoe (hJ.toLp J)).trans (Eventually.of_forall (congrFun he))
  have hN : HasDerivAt (fun t : ℂ => T (M t)) (T (hJ.toLp J)) 0 := by
    simpa only [Function.comp_def] using
      (T.hasFDerivAt (x := M 0)).comp_hasDerivAt 0 hMderiv
  refine ⟨ε, J, hJ, T (hJ.toLp J), (fun t => T (M t)),
    hε, hJm, hcanonical, hd, hN, ?_⟩
  intro t ht
  have he := hilbertH_congr_ae (hM t ht)
  exact (hTcoe (M t)).trans (Eventually.of_forall (congrFun he))

theorem actual_passive_hilbert_difference_quotient_ae_subsequence
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    let K := fun (t : ℂ) (η : ℍ) =>
      dz (canonicalBiparameterFamily R p q 0 t) η *
        dz (canonicalBiparameterFamily R p q 0 t) (conj (z : ℂ)) /
        (canonicalBiparameterFamily R p q 0 t η -
          canonicalBiparameterFamily R p q 0 t (conj (z : ℂ))) ^ 2
    let W := fun t => WeilPetersson.SourceKernel.upperExtension
      (fun η => harmonicPlane R p q η * K t η)
    ∃ (J : ℂ → ℂ) (_hJ : MemLp J 2 (volume : Measure ℂ)) (τ : ℕ → ℂ),
      Measurable J ∧
      (∀ᵐ η : ℂ,
        HasDerivAt (fun t => W t η) (J η) 0 ∧
        J η = WeilPetersson.SourceKernel.upperExtension
          (fun ξ => harmonicPlane R p q ξ * deriv (fun t => K t ξ) 0) η) ∧
      (∀ n, τ n ≠ 0) ∧ Tendsto τ atTop (𝓝 0) ∧
      ∀ᵐ η : ℂ, Tendsto
        (fun n => (hilbertH (W (τ n)) η - hilbertH (W 0) η) / τ n)
        atTop (𝓝 (hilbertH J η)) := by
  dsimp only
  obtain ⟨ε, J, hJ, d, N, hε, hJm, hcanonical, hd, hNderiv, hN⟩ :=
    actual_passive_hilbert_input_curve_derivative R p hp q z
  let W : ℂ → ℂ → ℂ := fun t => WeilPetersson.SourceKernel.upperExtension
    (fun ξ => harmonicPlane R p q ξ *
      (dz (canonicalBiparameterFamily R p q 0 t) ξ *
        dz (canonicalBiparameterFamily R p q 0 t) (conj (z : ℂ)) /
        (canonicalBiparameterFamily R p q 0 t ξ -
          canonicalBiparameterFamily R p q 0 t (conj (z : ℂ))) ^ 2))
  let t : ℕ → ℂ := fun n => ((ε / 2 * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)
  have htpos (n : ℕ) : 0 < ε / 2 * (1 / ((n : ℝ) + 1)) := by positivity
  have htne (n : ℕ) : t n ≠ 0 := Complex.ofReal_ne_zero.mpr (htpos n).ne'
  have htsmall (n : ℕ) : ‖t n‖ < ε := by
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      simpa only [div_one] using one_div_le_one_div_of_le
        (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)
    have hhalf : ε / 2 * (1 / ((n : ℝ) + 1)) ≤ ε / 2 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ ε / 2)
    simpa only [t, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos n)] using
      hhalf.trans_lt (half_lt_self hε)
  have htlim : Tendsto t atTop (𝓝 (0 : ℂ)) := by
    have hr : Tendsto (fun n : ℕ => ε / 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ε / 2)
    simpa only [t, Function.comp_def, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp hr
  have htlim' : Tendsto t atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htlim, Eventually.of_forall (fun n => htne n)⟩
  let Q : ℕ → Lp ℂ 2 (volume : Measure ℂ) := fun n =>
    (t n)⁻¹ • (N (t n) - N 0)
  have hQlim : Tendsto Q atTop (𝓝 d) := by
    simpa only [Q, Function.comp_def, zero_add] using hNderiv.tendsto_slope_zero.comp htlim'
  obtain ⟨ns, hns, hseq⟩ := (tendstoInMeasure_of_tendsto_Lp hQlim).exists_seq_tendsto_ae
  have hQn (n : ℕ) : (Q n : ℂ → ℂ) =ᵐ[volume]
      fun η => (hilbertH (W (t n)) η - hilbertH (W 0) η) / t n := by
    filter_upwards [Lp.coeFn_smul (t n)⁻¹ (N (t n) - N 0),
      Lp.coeFn_sub (N (t n)) (N 0), hN (t n) (htsmall n),
      hN 0 (by simpa only [norm_zero] using hε)] with η h₁ h₂ h₃ h₄
    simp only [Pi.smul_apply, Pi.sub_apply] at h₁ h₂
    change ((t n)⁻¹ • (N (t n) - N 0) : Lp ℂ 2 (volume : Measure ℂ)) η = _
    rw [h₁, h₂, h₃, h₄]
    change (t n)⁻¹ • (hilbertH (W (t n)) η - hilbertH (W 0) η) =
      (hilbertH (W (t n)) η - hilbertH (W 0) η) / t n
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hAll := ae_all_iff.mpr hQn
  refine ⟨J, hJ, (fun n => t (ns n)), hJm, hcanonical,
    (fun n => htne (ns n)), htlim.comp hns.tendsto_atTop, ?_⟩
  filter_upwards [hseq, hAll, hd] with η hη hcoh hηd
  have hη' := hη.congr' (Eventually.of_forall (fun n => hcoh (ns n)))
  simpa only [hηd] using hη'

private theorem actual_passive_regular_pairing_hasDerivAt
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z x : ℍ) :
    let K := fun (t : ℂ) (η : ℍ) =>
      dz (canonicalBiparameterFamily R p q 0 t) η *
        dz (canonicalBiparameterFamily R p q 0 t) (conj (z : ℂ)) /
        (canonicalBiparameterFamily R p q 0 t η -
          canonicalBiparameterFamily R p q 0 t (conj (z : ℂ))) ^ 2
    let W := fun t => WeilPetersson.SourceKernel.upperExtension
      (fun η => harmonicPlane R p q η * K t η)
    ∃ (ε : ℝ) (D : ℂ → ℂ) (_hD : MemLp D 2 (volume : Measure ℂ)),
      0 < ε ∧ Measurable D ∧
      (∀ᵐ η : ℂ, HasDerivAt
        (fun t => canonicalPassiveRegularKernelInput R p q x t η) (D η) 0) ∧
      (∀ t : ℂ, ‖t‖ < ε → Integrable
        (fun η : ℂ => W t η * canonicalPassiveRegularKernelInput R p q x t η) volume) ∧
      Integrable (fun η : ℂ => W 0 η * D η) volume ∧
      HasDerivAt (fun t : ℂ => ∫ η : ℂ,
        W t η * canonicalPassiveRegularKernelInput R p q x t η)
        (∫ η : ℂ, W 0 η * D η) 0 := by
  dsimp only
  obtain ⟨εW, J, hJ, M, hεW, _, _, hMd, hM⟩ :=
    canonicalPassiveFullKernelInput_hasDerivAt_toLp R p hp q z
  obtain ⟨εR, D, hD, L, hεR, hDm, hpoint, hLd, hL⟩ :=
    canonicalPassiveRegularKernelInput_hasDerivAt_toLp R p hp q x
  let W : ℂ → ℂ → ℂ := fun t => WeilPetersson.SourceKernel.upperExtension
    (fun η => harmonicPlane R p q η *
      (dz (canonicalBiparameterFamily R p q 0 t) η *
        dz (canonicalBiparameterFamily R p q 0 t) (conj (z : ℂ)) /
        (canonicalBiparameterFamily R p q 0 t η -
          canonicalBiparameterFamily R p q 0 t (conj (z : ℂ))) ^ 2))
  let A := Lp ℂ 2 (volume : Measure ℂ)
  let S : A →L⋆[ℂ] A :=
    ((starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap).compLpL 2 volume
  let B : A →L[ℂ] A →L[ℂ] ℂ := (innerSL ℂ).comp S
  have hS (f : A) : (S f : ℂ → ℂ) =ᵐ[volume] fun η => conj (f η) := by
    simpa only [S, ContinuousLinearEquiv.coe_coe, starL_apply, RCLike.star_def] using
      ((starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap.coeFn_compLpL f)
  have hpair (U V : A) (r w : ℂ → ℂ)
      (hr : (U : ℂ → ℂ) =ᵐ[volume] r) (hw : (V : ℂ → ℂ) =ᵐ[volume] w) :
      Integrable (fun η : ℂ => w η * r η) volume ∧ B U V = ∫ η : ℂ, w η * r η := by
    have he : (fun η : ℂ => inner ℂ ((S U : ℂ → ℂ) η) (V η)) =ᵐ[volume]
        fun η : ℂ => w η * r η := by
      filter_upwards [hS U, hr, hw] with η hs hu hv
      rw [RCLike.inner_apply, hs, Complex.conj_conj, hu, hv]
    refine ⟨(MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (S U) V).congr he, ?_⟩
    change inner ℂ (S U) V = _
    rw [MeasureTheory.L2.inner_def]
    exact integral_congr_ae he
  have hF0 : canonicalBiparameterFamily R p q 0 0 = id := by
    simpa only [map_zero] using
      (canonicalBiparameterFamily_diagonal R p q 0).trans (canonicalFamily_zero R p q)
  have hdz0 : dz (id : ℂ → ℂ) = fun _ => 1 := by
    funext y
    simp only [dz, fderiv_id, ContinuousLinearMap.id_apply]
    rw [I_mul_I]
    ring
  have hR0 : canonicalPassiveRegularKernelInput R p q x 0 = 0 := by
    funext y
    by_cases hy : y ∈ upperHalf
    · simp only [canonicalPassiveRegularKernelInput, indicator_of_mem hy, hF0,
        hdz0, id_eq, one_mul, sub_self, Pi.zero_apply]
    · simp only [canonicalPassiveRegularKernelInput, indicator_of_notMem hy, Pi.zero_apply]
  have hL0 : L 0 = 0 := by
    apply Lp.ext
    filter_upwards [hL 0 (by simpa only [norm_zero] using hεR),
      Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with η hη hzero
    simp only [hR0, Pi.zero_apply] at hη
    exact hη.trans hzero.symm
  let ε := min εW εR
  have hε : 0 < ε := lt_min hεW hεR
  have hactual (t : ℂ) (ht : ‖t‖ < ε) :
      Integrable (fun η : ℂ => W t η * canonicalPassiveRegularKernelInput R p q x t η) volume ∧
        B (L t) (M t) = ∫ η : ℂ, W t η * canonicalPassiveRegularKernelInput R p q x t η :=
    hpair (L t) (M t) _ _ (hL t (ht.trans_le (min_le_right _ _)))
      (hM t (ht.trans_le (min_le_left _ _)))
  have hbase : Integrable (fun η : ℂ => W 0 η * D η) volume ∧
      B (hD.toLp D) (M 0) = ∫ η : ℂ, W 0 η * D η :=
    hpair (hD.toLp D) (M 0) D (W 0) hD.coeFn_toLp
      (hM 0 (by simpa only [norm_zero] using hεW))
  have hderiv : HasDerivAt (fun t : ℂ => B (L t) (M t))
      (∫ η : ℂ, W 0 η * D η) 0 := by
    have hBd := (B.hasFDerivAt (x := L 0)).comp_hasDerivAt 0 hLd
    simpa only [Function.comp_def, hL0, map_zero, zero_apply, add_zero, hbase.2] using hBd.clm_apply hMd
  refine ⟨ε, D, hD, hε, hDm, hpoint, (fun t ht => (hactual t ht).1), hbase.1, ?_⟩
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds (0 : ℂ) hε] with t ht
  exact (hactual t (mem_ball_zero_iff.mp ht)).2.symm

theorem actual_passive_regular_pairing_cross_kernel_derivative
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z x : ℍ) :
    let K := fun (t : ℂ) (η : ℍ) =>
      dz (canonicalBiparameterFamily R p q 0 t) η *
        dz (canonicalBiparameterFamily R p q 0 t) (conj (z : ℂ)) /
        (canonicalBiparameterFamily R p q 0 t η -
          canonicalBiparameterFamily R p q 0 t (conj (z : ℂ))) ^ 2
    let W := fun t => WeilPetersson.SourceKernel.upperExtension
      (fun η => harmonicPlane R p q η * K t η)
    let B₁ : ℂ → ℂ := upperHalf.indicator (fun η : ℂ =>
      -(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf,
        conj (harmonicPlane R p q w) / ((conj w - x) ^ 2 * (conj w - η) ^ 2))
    ∃ ε : ℝ, 0 < ε ∧ MemLp B₁ 2 (volume : Measure ℂ) ∧
      (∀ t : ℂ, ‖t‖ < ε → Integrable
        (fun η : ℂ => W t η * canonicalPassiveRegularKernelInput R p q x t η) volume) ∧
      Integrable (fun η : ℂ => W 0 η * B₁ η) volume ∧
      HasDerivAt (fun t : ℂ => ∫ η : ℂ,
        W t η * canonicalPassiveRegularKernelInput R p q x t η)
        (∫ η : ℂ, W 0 η * B₁ η) 0 := by
  dsimp only
  obtain ⟨ε, D, hD, hε, _, hpoint, hnear, hi, hd⟩ :=
    actual_passive_regular_pairing_hasDerivAt R p hp q z x
  let W : ℂ → ℂ → ℂ := fun t => WeilPetersson.SourceKernel.upperExtension
    (fun η => harmonicPlane R p q η *
      (dz (canonicalBiparameterFamily R p q 0 t) η *
        dz (canonicalBiparameterFamily R p q 0 t) (conj (z : ℂ)) /
        (canonicalBiparameterFamily R p q 0 t η -
          canonicalBiparameterFamily R p q 0 t (conj (z : ℂ))) ^ 2))
  let B₁ : ℂ → ℂ := upperHalf.indicator (fun η : ℂ =>
    -(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf,
      conj (harmonicPlane R p q w) / ((conj w - x) ^ 2 * (conj w - η) ^ 2))
  have hDB : D =ᵐ[volume] B₁ := by
    filter_upwards [hpoint, volume.ae_ne (x : ℂ)] with η hη hne
    by_cases hU : η ∈ upperHalf
    · let y : ℍ := ⟨η, hU⟩
      have hxy : (x : ℂ) ≠ (y : ℂ) := fun h => hne h.symm
      have hs := (actual_passive_regular_input_first_variation R p hp q x y hxy).2
      change D η = upperHalf.indicator _ η
      rw [indicator_of_mem hU]
      exact hη.unique hs
    · have hs : HasDerivAt (fun t : ℂ => canonicalPassiveRegularKernelInput R p q x t η) 0 0 := by
        simpa only [canonicalPassiveRegularKernelInput, indicator_of_notMem hU] using
          hasDerivAt_const (0 : ℂ) (0 : ℂ)
      change D η = upperHalf.indicator _ η
      rw [indicator_of_notMem hU]
      exact hη.unique hs
  have hprod : (fun η : ℂ => W 0 η * D η) =ᵐ[volume] fun η => W 0 η * B₁ η :=
    hDB.mono (fun η he => congrArg (fun w : ℂ => W 0 η * w) he)
  refine ⟨ε, hε, (memLp_congr_ae hDB).mp hD, hnear, hi.congr hprod, ?_⟩
  exact hd.congr_deriv (integral_congr_ae hprod)


end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
