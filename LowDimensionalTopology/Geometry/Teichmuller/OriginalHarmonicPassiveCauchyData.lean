module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicComplexifiedKernel
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicFirstSpatialParameters
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Ordinary Cauchy data for the actual passive deformation

The actual pushed coefficient is supported on the genuine image half-plane.
Ordinary target Cauchy integrability, area substitution, and the normalized
resolvent are established before any singular differentiation.
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

theorem norm_dz_le_real_derivative (F : ℂ → ℂ) (x : ℂ) :
    ‖dz F x‖ ≤ ‖fderiv ℝ F x‖ := by
  have h₁ := (fderiv ℝ F x).le_opNorm (1 : ℂ)
  have hI := (fderiv ℝ F x).le_opNorm Complex.I
  rw [norm_one, mul_one] at h₁
  rw [Complex.norm_I, mul_one] at hI
  rw [dz, norm_div, Complex.norm_two]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  calc
    ‖fderiv ℝ F x 1 - Complex.I * fderiv ℝ F x Complex.I‖ ≤
        ‖fderiv ℝ F x 1‖ + ‖Complex.I * fderiv ℝ F x Complex.I‖ := norm_sub_le _ _
    _ = ‖fderiv ℝ F x 1‖ + ‖fderiv ℝ F x Complex.I‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ‖fderiv ℝ F x‖ + ‖fderiv ℝ F x‖ := add_le_add h₁ hI
    _ = ‖fderiv ℝ F x‖ * 2 := by ring

private theorem cauchy_tail_hasDerivAt
    {d : ℂ → ℂ} (hm : AEStronglyMeasurable d (volume : Measure ℂ))
    {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ w : ℂ, ‖w - z‖ ≤ 2 * r → d w = 0)
    (hvalue : Integrable (fun w : ℂ => d w / (w - z)) volume)
    (hsquare : Integrable (fun w : ℂ => d w / (w - z) ^ 2) volume) :
    HasDerivAt (cauchyT d)
      (-(1 / Real.pi : ℂ) * ∫ w : ℂ, d w / (w - z) ^ 2) z := by
  have hsep (w b : ℂ) (hw : d w ≠ 0) (hb : b ∈ ball z r) :
      0 < ‖w - b‖ ∧ ‖w - z‖ ≤ 2 * ‖w - b‖ := by
    have hwfar : 2 * r < ‖w - z‖ := by
      by_contra h
      exact hw (hzero w (le_of_not_gt h))
    have hbnear : ‖b - z‖ < r := by simpa only [mem_ball, dist_eq_norm] using hb
    have htri : ‖w - z‖ ≤ ‖w - b‖ + ‖b - z‖ := norm_sub_le_norm_sub_add_norm_sub w b z
    constructor <;> linarith
  have hd (w b : ℂ) (hb : b ∈ ball z r) :
      HasDerivAt (fun a : ℂ => d w / (w - a)) (d w / (w - b) ^ 2) b := by
    by_cases hw : d w = 0
    · simpa only [hw, zero_div] using (hasDerivAt_const b (0 : ℂ))
    · have hne : w - b ≠ 0 := norm_pos_iff.mp (hsep w b hw hb).1
      convert (((hasDerivAt_id b).const_sub w).inv hne).const_mul (d w) using 1 <;>
        simp only [neg_neg, div_eq_mul_inv, one_mul, Pi.inv_apply, id_eq]
  have hbound (w b : ℂ) (hb : b ∈ ball z r) :
      ‖d w / (w - b) ^ 2‖ ≤ 4 * ‖d w / (w - z) ^ 2‖ := by
    by_cases hw : d w = 0
    · simp only [hw, zero_div, norm_zero, mul_zero, le_refl]
    · obtain ⟨hpos, hdist⟩ := hsep w b hw hb
      have hzpos : 0 < ‖w - z‖ := by
        by_contra h
        apply hw
        exact hzero w (le_trans (le_of_not_gt h) (by positivity))
      have hsq : ‖w - z‖ ^ 2 ≤ 4 * ‖w - b‖ ^ 2 := by nlinarith [norm_nonneg (w - z)]
      simp only [norm_div, norm_pow]
      calc
        ‖d w‖ / ‖w - b‖ ^ 2 ≤ ‖d w‖ / (‖w - z‖ ^ 2 / 4) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith [hsq])
        _ = 4 * (‖d w‖ / ‖w - z‖ ^ 2) := by
          rw [div_div_eq_mul_div]
          ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℂ))
    (F := fun b w : ℂ => d w / (w - b))
    (F' := fun b w : ℂ => d w / (w - b) ^ 2)
    (bound := fun w : ℂ => 4 * ‖d w / (w - z) ^ 2‖)
    (ball_mem_nhds z hr)
    (Eventually.of_forall fun b => hm.div₀
      (by fun_prop : Measurable fun w : ℂ => w - b).aestronglyMeasurable)
    hvalue
    (hm.div₀ (by fun_prop : Measurable fun w : ℂ => (w - z) ^ 2).aestronglyMeasurable)
    (Eventually.of_forall fun w b hb => hbound w b hb)
    (hsquare.norm.const_mul 4)
    (Eventually.of_forall fun w b hb => hd w b hb)
  unfold cauchyT
  exact h.2.const_mul (-(1 / Real.pi : ℂ))

theorem localized_cauchy_dz_and_radial
    (f : ℂ → ℂ) (hLp : MemLp f 2 (volume : Measure ℂ))
    (hC1 : ContDiffOn ℝ 1 f upperHalf)
    (hvalue : ∀ z ∈ upperHalf, Integrable (fun w : ℂ => f w / (w - z)) volume)
    (ξ : ℍ) :
    DifferentiableAt ℝ (cauchyT f) (ξ : ℂ) ∧
      dz (cauchyT f) ξ = hilbertHSmooth f ξ ∧
      Tendsto (fun r : ℝ => -(1 / Real.pi : ℂ) *
        ∫ w in {w : ℂ | r < ‖w - ξ‖}, f w / (w - ξ) ^ 2)
        (𝓝[>] 0) (𝓝 (hilbertHSmooth f ξ)) := by
  let b : ContDiffBump (ξ : ℂ) :=
    ⟨ξ.im / 4, ξ.im / 2, by positivity, by linarith [ξ.im_pos]⟩
  let ψ : ℂ → ℂ := fun w => (b w : ℂ) * f w
  have hsub : closedBall (ξ : ℂ) (ξ.im / 2) ⊆ upperHalf := by
    intro w hw
    have hn : ‖w - ξ‖ ≤ ξ.im / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hi : ξ.im - w.im ≤ ‖w - ξ‖ := by
      calc
        ξ.im - w.im = -(w - ξ).im := by simp only [sub_im, UpperHalfPlane.coe_im]; ring
        _ ≤ |(w - ξ).im| := neg_le_abs _
        _ ≤ ‖w - ξ‖ := Complex.abs_im_le_norm _
    change 0 < w.im
    linarith [ξ.im_pos]
  have hb : ContDiff ℝ 1 (fun w : ℂ => (b w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hψ : ContDiff ℝ 1 ψ := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w ∈ tsupport b
    · have hwU : w ∈ upperHalf := hsub (by simpa only [b.tsupport_eq] using hw)
      exact hb.contDiffAt.mul (hC1.contDiffAt (isOpen_upperHalf.mem_nhds hwU))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (b : ℂ → ℝ)).isOpen_compl.mem_nhds hw] with w' hw'
      change (b w' : ℂ) * f w' = 0
      rw [image_eq_zero_of_notMem_tsupport hw', Complex.ofReal_zero, zero_mul]
  have hcψ : HasCompactSupport ψ :=
    (b.hasCompactSupport.comp_left (g := fun a : ℝ => (a : ℂ)) rfl).mul_right
  have hψLp : MemLp ψ 2 (volume : Measure ℂ) :=
    hψ.continuous.memLp_of_hasCompactSupport hcψ
  have hψvalue (z : ℂ) : Integrable (fun w : ℂ => ψ w / (w - z)) volume := by
    obtain ⟨S, hS⟩ := hcψ.isCompact.isBounded.subset_closedBall (0 : ℂ)
    apply integrable_cauchyT_kernel (p := 3) (by norm_num)
      (show 0 < max S 1 by positivity)
      (hψ.continuous.memLp_of_hasCompactSupport hcψ)
    intro w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hws
    have hn := hS hws
    have hn' : ‖w‖ ≤ S := by simpa only [mem_closedBall, dist_zero_right] using hn
    exact not_lt_of_ge (hn'.trans (le_max_left _ _)) hw
  let d : ℂ → ℂ := f - ψ
  have hdLp : MemLp d 2 (volume : Measure ℂ) := hLp.sub hψLp
  have hzero (w : ℂ) (hw : ‖w - ξ‖ ≤ ξ.im / 4) : d w = 0 := by
    have hone := b.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_eq_norm] using hw)
    simp only [d, Pi.sub_apply, ψ, hone, Complex.ofReal_one, one_mul, sub_self]
  have hdvalue (z : ℂ) (hz : z ∈ upperHalf) :
      Integrable (fun w : ℂ => d w / (w - z)) volume := by
    apply ((hvalue z hz).sub (hψvalue z)).congr
    exact Eventually.of_forall fun w => by dsimp only [d, Pi.sub_apply]; rw [sub_div]
  have hdsquare : Integrable (fun w : ℂ => d w / (w - ξ) ^ 2) volume := by
    have hi := integrableOn_truncated_kernel (p := 2) (by norm_num)
      (by simpa using hdLp) (ξ : ℂ) (by positivity : 0 < ξ.im / 4)
    apply hi.integrable_of_forall_notMem_eq_zero
    intro w hw
    rw [hzero w (le_of_not_gt hw), zero_div]
  have hd : HasDerivAt (cauchyT d)
      (-(1 / Real.pi : ℂ) * ∫ w : ℂ, d w / (w - ξ) ^ 2) (ξ : ℂ) := by
    apply cauchy_tail_hasDerivAt hdLp.aestronglyMeasurable (by positivity : 0 < ξ.im / 8)
      (fun w hw => hzero w (by linarith)) (hdvalue ξ ξ.im_pos) hdsquare
  have heq : cauchyT f =ᶠ[𝓝 (ξ : ℂ)] fun z => cauchyT ψ z + cauchyT d z := by
    filter_upwards [isOpen_upperHalf.mem_nhds ξ.im_pos] with z hz
    unfold cauchyT
    rw [← mul_add, ← integral_add (hψvalue z) (hdvalue z hz)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by dsimp only [d, Pi.sub_apply]; ring
  have hψdiff : DifferentiableAt ℝ (cauchyT ψ) (ξ : ℂ) :=
    (contDiff_cauchyT hψ hcψ).differentiable one_ne_zero _
  have hddiff : DifferentiableAt ℝ (cauchyT d) (ξ : ℂ) := hd.differentiableAt.restrictScalars ℝ
  have hdiff := (hψdiff.add hddiff).congr_of_eventuallyEq heq
  have hdzsum : dz (cauchyT f) ξ = dz (cauchyT ψ) ξ + dz (cauchyT d) ξ := by
    have hfd := heq.fderiv_eq (𝕜 := ℝ)
    have hadd := (hψdiff.hasFDerivAt.add hddiff.hasFDerivAt).fderiv
    have hsumfun : cauchyT ψ + cauchyT d =
        (fun z : ℂ => cauchyT ψ z + cauchyT d z) := by
      funext z
      simp only [Pi.add_apply]
    rw [hsumfun] at hadd
    simp only [dz, hfd, hadd, add_apply]
    ring
  have hψlim := tendsto_truncated_cauchyT_dz hψ hcψ (ξ : ℂ)
  have hdlim : Tendsto
      (fun r : ℝ => -(1 / Real.pi : ℂ) *
        ∫ w in {w : ℂ | r < ‖w - ξ‖}, d w / (w - ξ) ^ 2)
      (𝓝[>] 0) (𝓝 (-(1 / Real.pi : ℂ) * ∫ w : ℂ, d w / (w - ξ) ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by positivity : 0 < ξ.im / 4)] with r hr
    congr 1
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    rw [hzero w ((le_of_not_gt hw).trans hr.2.le), zero_div]
  have hlim : Tendsto
      (fun r : ℝ => -(1 / Real.pi : ℂ) *
        ∫ w in {w : ℂ | r < ‖w - ξ‖}, f w / (w - ξ) ^ 2)
      (𝓝[>] 0) (𝓝 (cauchyT (dz ψ) ξ +
        -(1 / Real.pi : ℂ) * ∫ w : ℂ, d w / (w - ξ) ^ 2)) := by
    apply (hψlim.add hdlim).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hψint := integrableOn_truncated_kernel (p := 2) (by norm_num)
      (by simpa using hψLp) (ξ : ℂ) hr
    have hdint := integrableOn_truncated_kernel (p := 2) (by norm_num)
      (by simpa using hdLp) (ξ : ℂ) hr
    rw [← mul_add, ← integral_add hψint hdint]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by dsimp only [d, Pi.sub_apply]; ring
  have hH : hilbertHSmooth f ξ = cauchyT (dz ψ) ξ +
      -(1 / Real.pi : ℂ) * ∫ w : ℂ, d w / (w - ξ) ^ 2 := hlim.limUnder_eq
  refine ⟨hdiff, ?_, ?_⟩
  · rw [hH, hdzsum, dz_cauchyT hψ hcψ,
      dz_eq_deriv hd.differentiableAt, hd.deriv]
  · simpa only [hH] using hlim

theorem actual_passive_conformal_data
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ ball (0 : ℂ) ε,
      IsKQCNormalizedPlane (canonicalBiparameterFamily R p q 0 t) 3 ∧
      DifferentiableOn ℂ (canonicalBiparameterFamily R p q 0 t) upperHalf := by
  obtain ⟨ε, hε, hspec, _, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  have hz : ‖(0 : ℂ)‖ < ε := by simpa only [norm_zero] using hε
  refine ⟨ε, hε, ?_⟩
  intro t ht
  have htε : ‖t‖ < ε := mem_ball_zero_iff.mp ht
  have hsol := (hspec 0 t hz htε).2
  have hsharp : IsKQCNormalizedPlane (canonicalBiparameterFamily R p q 0 t) 3 := by
    obtain ⟨f, _, hK, huniq⟩ := thm13_7_normalized_existence
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      (hspec 0 t hz htε).1
    have heq := huniq _ hsol
    refine ⟨?_, hsol.2.1, hsol.2.2.1, hsol.2.2.2.1⟩
    rw [heq]
    simpa only [show (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) = 3 by norm_num] using hK
  have hqc : IsKQC (canonicalBiparameterFamily R p q 0 t) upperHalf 3 :=
    ac_t_isKQC_restrict hsharp.1 isOpen_upperHalf (subset_univ _)
  have hdil : ∀ᵐ w ∂volume.restrict upperHalf,
      complexDilatation (canonicalBiparameterFamily R p q 0 t) w = 0 := by
    filter_upwards [ae_restrict_of_ae hsol.2.2.2.2,
      ae_restrict_mem isOpen_upperHalf.measurableSet] with w hw hwH
    rw [hw, harmonicBiparameterCoefficient,
      ite_eq_right (not_lt.mpr (le_of_lt hwH)), zero_mul]
  exact ⟨hsharp, nx_differentiableOn_of_dilatation_zero hqc hdil⟩

theorem actual_point_parameter_variation_at_passive
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → ∀ x : ℂ,
      HasDerivAt (fun s : ℂ => canonicalBiparameterFamily R p q s t x)
        (ahVar (ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
          (harmonicBiparameterCoefficient R p q 0 t)
          (canonicalBiparameterFamily R p q 0 t))
            (canonicalBiparameterFamily R p q 0 t x)) 0 := by
  obtain ⟨ε, hε, hspec, _, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  refine ⟨ε, hε, ?_⟩
  intro t ht x
  let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
  have hμ (s : ℂ) (hs : s ∈ ball (0 : ℂ) ε) :
      IsBeltramiCoeff (harmonicBiparameterCoefficient R p q s t) univ (1 / 2) :=
    (hspec s t (mem_ball_zero_iff.mp hs) ht).1
  have hsol (s : ℂ) (hs : s ∈ ball (0 : ℂ) ε) :
      IsNormalizedSolution (canonicalBiparameterFamily R p q s t)
        (harmonicBiparameterCoefficient R p q s t) :=
    (hspec s t (mem_ball_zero_iff.mp hs) ht).2
  have hhol (w : ℂ) : DifferentiableOn ℂ
      (fun s => harmonicBiparameterCoefficient R p q s t w) (ball 0 ε) := by
    by_cases hw : w.im < 0
    · simp only [harmonicBiparameterCoefficient, hw, ite_true]
      exact differentiableOn_const _
    · simp only [harmonicBiparameterCoefficient, hw, ite_false]
      exact (differentiable_id.mul_const (harmonicPlane R p q w)).differentiableOn
  have hdot : (fun w : ℂ => deriv
      (fun s : ℂ => harmonicBiparameterCoefficient R p q s t w) 0) =
        fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w := by
    funext w
    by_cases hw : w.im < 0
    · simp only [harmonicBiparameterCoefficient, hw, ite_true, deriv_const]
    · simp only [harmonicBiparameterCoefficient, hw, ite_false]
      exact (hasDerivAt_mul_const (harmonicPlane R p q w)).deriv
  have h := ahT_hasDerivAt isOpen_ball (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hμ hhol hsol (mem_ball_self hε) x
  rw [hdot] at h
  exact h

private theorem actual_passive_pushed_coefficient_identity
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
      let F := canonicalBiparameterFamily R p q 0 t
      let β := ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
        (harmonicBiparameterCoefficient R p q 0 t) F
      (∀ y ∈ upperHalf,
        β (F y) = harmonicPlane R p q y * deriv F y / conj (deriv F y)) ∧
      ∀ w ∉ F '' upperHalf, β w = 0 := by
  obtain ⟨ε, hε, hdata⟩ := actual_passive_conformal_data R p hp q
  refine ⟨ε, hε, ?_⟩
  intro t ht
  dsimp only
  let F := canonicalBiparameterFamily R p q 0 t
  let β := ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
    (harmonicBiparameterCoefficient R p q 0 t) F
  obtain ⟨hqc, hhol⟩ := hdata t (mem_ball_zero_iff.mpr ht)
  have hinj : InjOn F univ := hqc.1.2.2.1.2.1
  have hinv (y : ℂ) : Function.invFunOn F univ (F y) = y :=
    hinj.leftInvOn_invFunOn (mem_univ y)
  have hinv' (w : ℂ) : F (Function.invFunOn F univ w) = w :=
    Function.invFunOn_eq (show w ∈ F '' univ from by
      have himage : F '' univ = univ := hqc.2.1
      exact himage.symm ▸ mem_univ w)
  constructor
  · intro y hy
    change β (F y) = _
    dsimp only [β, ahT_dot]
    rw [hinv]
    have hyn : ¬y.im < 0 := not_lt.mpr (le_of_lt hy)
    simp only [hyn, ite_false, harmonicBiparameterCoefficient, zero_mul,
      map_zero, mul_zero, sub_zero, div_one]
    rw [dz_eq_deriv (hhol.differentiableAt (isOpen_upperHalf.mem_nhds hy)), mul_div_assoc]
  · intro w hw
    let y := Function.invFunOn F univ w
    have hy : y ∉ upperHalf := by
      intro hyH
      exact hw ⟨y, hyH, hinv' w⟩
    have hμ : (if y.im < 0 then 0 else harmonicPlane R p q y) = 0 := by
      by_cases hyn : y.im < 0
      · rw [ite_eq_left hyn]
      · rw [ite_eq_right hyn]
        have hzero : y.im = 0 := le_antisymm (not_lt.mp hy) (not_lt.mp hyn)
        simp only [harmonicPlane, hzero, Complex.ofReal_zero, zero_pow two_ne_zero, zero_mul]
    change β w = 0
    dsimp only [β, ahT_dot]
    change (if y.im < 0 then 0 else harmonicPlane R p q y) / _ * _ = 0
    rw [hμ, zero_div, zero_mul]

private theorem actual_passive_pushed_coefficient_measurable_bound
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 ≤ M ∧ ∀ t : ℂ, ‖t‖ < ε →
      let F := canonicalBiparameterFamily R p q 0 t
      let β := ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
        (harmonicBiparameterCoefficient R p q 0 t) F
      AEStronglyMeasurable β volume ∧ ∀ w : ℂ, ‖β w‖ ≤ M := by
  obtain ⟨εQ, hεQ, hdata⟩ := actual_passive_conformal_data R p hp q
  obtain ⟨εI, hεI, hidentity⟩ := actual_passive_pushed_coefficient_identity R p hp q
  obtain ⟨εS, hεS, hspec, _, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  obtain ⟨M, hM, hbound⟩ := QuadraticBergman.uniformizedQuadratic_weightedBound R p hp q
  let ε := min εQ (min εI εS)
  have hε : 0 < ε := lt_min hεQ (lt_min hεI hεS)
  refine ⟨ε, M, hε, hM, ?_⟩
  intro t ht
  dsimp only
  let F := canonicalBiparameterFamily R p q 0 t
  let δμ : ℂ → ℂ := fun w => if w.im < 0 then 0 else harmonicPlane R p q w
  let μ₀ := harmonicBiparameterCoefficient R p q 0 t
  let β := ahT_dot δμ μ₀ F
  have htQ : ‖t‖ < εQ := ht.trans_le (min_le_left _ _)
  have htI : ‖t‖ < εI := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htS : ‖t‖ < εS := ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hqc, _⟩ := hdata t (mem_ball_zero_iff.mpr htQ)
  have hμ (s : ℂ) (hs : s ∈ ball (0 : ℂ) εS) :
      IsBeltramiCoeff (harmonicBiparameterCoefficient R p q s t) univ (1 / 2) :=
    (hspec s t (mem_ball_zero_iff.mp hs) htS).1
  have hhol (w : ℂ) : DifferentiableOn ℂ
      (fun s => harmonicBiparameterCoefficient R p q s t w) (ball 0 εS) := by
    by_cases hw : w.im < 0
    · simp only [harmonicBiparameterCoefficient, hw, ite_true]
      exact differentiableOn_const _
    · simp only [harmonicBiparameterCoefficient, hw, ite_false]
      exact (differentiable_id.mul_const (harmonicPlane R p q w)).differentiableOn
  have hdot : (fun w : ℂ => deriv
      (fun s : ℂ => harmonicBiparameterCoefficient R p q s t w) 0) = δμ := by
    funext w
    by_cases hw : w.im < 0
    · simp only [harmonicBiparameterCoefficient, δμ, hw, ite_true, deriv_const]
    · simp only [harmonicBiparameterCoefficient, δμ, hw, ite_false]
      exact (hasDerivAt_mul_const (harmonicPlane R p q w)).deriv
  have hδm : AEStronglyMeasurable δμ volume := by
    have hm := ahE_aestronglyMeasurable_deriv isOpen_ball hμ hhol (mem_ball_self hεS)
    rw [hdot] at hm
    exact hm
  have hμ₀m : AEStronglyMeasurable μ₀ volume := by
    simpa only [Measure.restrict_univ] using (hμ 0 (mem_ball_self hεS)).1
  have hdzm : AEStronglyMeasurable (dz F) volume :=
    (measurable_dz F).aestronglyMeasurable
  have hρm : AEStronglyMeasurable (fun y : ℂ => dz F y / conj (dz F y)) volume :=
    hdzm.div₀ (Complex.continuous_conj.comp_aestronglyMeasurable hdzm)
  have hin : AEStronglyMeasurable (fun y : ℂ =>
      δμ y / (1 - conj (μ₀ y) * μ₀ y) * (dz F y / conj (dz F y))) volume :=
    (hδm.div₀ (aestronglyMeasurable_const.sub
      ((Complex.continuous_conj.comp_aestronglyMeasurable hμ₀m).mul hμ₀m))).mul hρm
  have hqmp := ahT_qmp_inv (show IsQuasiconformal F univ from ⟨3, hqc.1⟩) hqc.2.1
  refine ⟨?_, ?_⟩
  · exact hin.comp_quasiMeasurePreserving hqmp
  · intro w
    have hid := hidentity t htI
    by_cases hw : w ∈ F '' upperHalf
    · obtain ⟨y, hy, rfl⟩ := hw
      rw [hid.1 y hy, mul_div_assoc, norm_mul]
      have hμy : ‖harmonicPlane R p q y‖ ≤ M := by
        have he := NativeHarmonicBeltrami.norm_coefficient R p q (⟨y, hy⟩ : ℍ)
        rw [← harmonicPlane_eq_coefficient] at he
        simpa only [he, UpperHalfPlane.im] using hbound y hy
      exact (mul_le_mul hμy (ahT_norm_div_conj_le _) (norm_nonneg _) hM).trans_eq
        (mul_one M)
    · rw [hid.2 w hw, norm_zero]
      exact hM

theorem actual_passive_pole_image_gap
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ ε d : ℝ, 0 < ε ∧ 0 < d ∧ ∀ t : ℂ, ‖t‖ < ε →
      let F := canonicalBiparameterFamily R p q 0 t
      ∀ y ∈ upperHalf, d ≤ ‖F y - F (conj (z : ℂ))‖ := by
  obtain ⟨εC, d, _, hεC, hd, _, hcompact⟩ :=
    canonicalBiparameterFamily_compact_image_control R p hp q {z} isCompact_singleton
  obtain ⟨εR, hεR, _, hreflect, _, _⟩ :=
    canonicalBiparameterFamily_spatial_c1_compact_control R p hp q
  refine ⟨min εC εR, d, lt_min hεC hεR, hd, ?_⟩
  intro t ht
  dsimp only
  let F := canonicalBiparameterFamily R p q 0 t
  let T := canonicalBiparameterFamily R p q (conj t) 0
  have htC : ‖conj t‖ < εC := by
    simpa only [norm_conj] using ht.trans_le (min_le_left _ _)
  have htR : ‖conj t‖ < εR := by
    simpa only [norm_conj] using ht.trans_le (min_le_right _ _)
  have hzC : ‖(0 : ℂ)‖ < εC := by simpa only [norm_zero] using hεC
  have hzR : ‖(0 : ℂ)‖ < εR := by simpa only [norm_zero] using hεR
  have hT : T = fun w : ℂ => conj (F (conj w)) := by
    simpa only [T, F, map_zero, Complex.conj_conj] using hreflect (conj t) 0 htR hzR
  intro y hy
  have hlow : (conj y).im ≤ 0 := by
    rw [conj_im]
    exact neg_nonpos.mpr (le_of_lt hy)
  have hs := ((hcompact (conj t) 0 htC hzC).2 z (mem_singleton z)).2.1 (conj y) hlow
  calc
    d ≤ ‖T (z : ℂ) - T (conj y)‖ := hs
    _ = ‖F (conj (z : ℂ)) - F y‖ := by
      simp only [hT, Complex.conj_conj, ← map_sub, norm_conj]
    _ = ‖F y - F (conj (z : ℂ))‖ := norm_sub_rev _ _

private theorem actual_passive_weighted_target_cauchy_integrable
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
      let F := canonicalBiparameterFamily R p q 0 t
      let b := F (conj (z : ℂ))
      let β := ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
        (harmonicBiparameterCoefficient R p q 0 t) F
      ∀ ξ : ℂ, Integrable (fun w : ℂ => β w / ((w - b) ^ 2 * (w - ξ))) volume := by
  obtain ⟨εB, M, hεB, hM, hβ⟩ := actual_passive_pushed_coefficient_measurable_bound R p hp q
  obtain ⟨εG, d, hεG, hd, hgap⟩ := actual_passive_pole_image_gap R p hp q z
  obtain ⟨εI, hεI, hidentity⟩ := actual_passive_pushed_coefficient_identity R p hp q
  refine ⟨min εB (min εG εI), lt_min hεB (lt_min hεG hεI), ?_⟩
  intro t ht
  dsimp only
  let F := canonicalBiparameterFamily R p q 0 t
  let b := F (conj (z : ℂ))
  let β := ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
    (harmonicBiparameterCoefficient R p q 0 t) F
  have htB : ‖t‖ < εB := ht.trans_le (min_le_left _ _)
  have htG : ‖t‖ < εG := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htI : ‖t‖ < εI := ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hβm, hβbound⟩ := hβ t htB
  let φ : ℂ → ℂ := fun w => β w / (w - b) ^ 2
  let L := M / d ^ 2
  have hL : 0 ≤ L := div_nonneg hM (sq_nonneg _)
  have hφm : AEStronglyMeasurable φ volume :=
    hβm.div₀ ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable
  have hφbound (w : ℂ) : ‖φ w‖ ≤ L := by
    by_cases hw : w ∈ F '' upperHalf
    · obtain ⟨y, hy, rfl⟩ := hw
      have hsep := hgap t htG y hy
      change ‖β (F y) / (F y - b) ^ 2‖ ≤ M / d ^ 2
      rw [norm_div, norm_pow]
      exact div_le_div₀ hM (hβbound _) (sq_pos_of_pos hd)
        (pow_le_pow_left₀ hd.le hsep 2)
    · have hz : β w = 0 := (hidentity t htI).2 w hw
      change ‖β w / (w - b) ^ 2‖ ≤ L
      rw [hz, zero_div, norm_zero]
      exact hL
  intro ξ
  let G : ℂ → ℂ := fun w => φ w / (w - ξ)
  have hGm : AEStronglyMeasurable G volume :=
    hφm.div₀ (measurable_id.sub measurable_const).aestronglyMeasurable
  let R := 4 * (1 + ‖b‖ + ‖ξ‖)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hnear : IntegrableOn G (ball (0 : ℂ) R) := by
    apply ((integrableOn_cauchy_kernel_ball hR ξ).norm.const_mul L).mono' hGm.restrict
    apply Eventually.of_forall
    intro w
    change ‖φ w / (w - ξ)‖ ≤ L * ‖1 / (w - ξ)‖
    calc
      _ = ‖φ w‖ / ‖w - ξ‖ := norm_div _ _
      _ ≤ L / ‖w - ξ‖ := div_le_div_of_nonneg_right (hφbound w) (norm_nonneg _)
      _ = L * ‖1 / (w - ξ)‖ := by rw [norm_div, norm_one]; ring
  have hfarbound (w : ℂ) (hw : w ∉ ball (0 : ℂ) R) :
      ‖G w‖ ≤ (64 * M) * ((1 + ‖w‖) ^ 3)⁻¹ := by
    have hwR : R ≤ ‖w‖ := by
      simpa only [mem_ball, dist_zero_right, not_lt] using hw
    let A := (1 + ‖w‖) / 4
    have hA : 0 < A := by dsimp only [A]; positivity
    have hwb : A ≤ ‖w - b‖ := by
      have htri := norm_sub_norm_le w b
      dsimp only [A]
      dsimp only [R] at hwR
      nlinarith [norm_nonneg w, norm_nonneg b, norm_nonneg ξ]
    have hwξ : A ≤ ‖w - ξ‖ := by
      have htri := norm_sub_norm_le w ξ
      dsimp only [A]
      dsimp only [R] at hwR
      nlinarith [norm_nonneg w, norm_nonneg b, norm_nonneg ξ]
    change ‖β w / (w - b) ^ 2 / (w - ξ)‖ ≤ _
    rw [norm_div, norm_div, norm_pow]
    calc
      ‖β w‖ / ‖w - b‖ ^ 2 / ‖w - ξ‖ ≤ (M / A ^ 2) / A :=
        div_le_div₀ (by positivity)
          (div_le_div₀ hM (hβbound w) (sq_pos_of_pos hA)
            (pow_le_pow_left₀ hA.le hwb 2)) hA hwξ
      _ = (64 * M) * ((1 + ‖w‖) ^ 3)⁻¹ := by
        dsimp only [A]
        field_simp
        ring
  have hfar : IntegrableOn G (ball (0 : ℂ) R)ᶜ := by
    apply (b36_p_profile_integrable.const_mul (64 * M)).integrableOn.mono' hGm.restrict
    apply ae_restrict_of_forall_mem isOpen_ball.measurableSet.compl
    intro w hw
    exact hfarbound w hw
  have hwhole : Integrable G volume := by
    simpa only [union_compl_self, integrableOn_univ] using hnear.union hfar
  simpa only [G, φ, div_div] using hwhole

theorem actual_passive_weighted_cauchy_pullback
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
      let F := canonicalBiparameterFamily R p q 0 t
      let b := F (conj (z : ℂ))
      let β := ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
        (harmonicBiparameterCoefficient R p q 0 t) F
      ∀ ξ : ℂ,
        IntegrableOn (fun y : ℂ => harmonicPlane R p q y * deriv F y ^ 2 /
          ((F y - b) ^ 2 * (F y - ξ))) upperHalf ∧
        cauchyT (fun w => β w / (w - b) ^ 2) ξ =
          -(1 / Real.pi : ℂ) * ∫ y : ℂ in upperHalf,
            harmonicPlane R p q y * deriv F y ^ 2 / ((F y - b) ^ 2 * (F y - ξ)) := by
  obtain ⟨εD, hεD, hdata⟩ := actual_passive_conformal_data R p hp q
  obtain ⟨εI, hεI, hidentity⟩ := actual_passive_pushed_coefficient_identity R p hp q
  obtain ⟨εV, hεV, hvalue⟩ := actual_passive_weighted_target_cauchy_integrable R p hp q z
  refine ⟨min εD (min εI εV), lt_min hεD (lt_min hεI hεV), ?_⟩
  intro t ht
  dsimp only
  let F := canonicalBiparameterFamily R p q 0 t
  let b := F (conj (z : ℂ))
  let β := ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
    (harmonicBiparameterCoefficient R p q 0 t) F
  have htD : ‖t‖ < εD := ht.trans_le (min_le_left _ _)
  have htI : ‖t‖ < εI := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htV : ‖t‖ < εV := ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hqc, hhol⟩ := hdata t (mem_ball_zero_iff.mpr htD)
  have hinj : InjOn F upperHalf := hqc.1.2.2.1.2.1.mono (subset_univ _)
  have hid : (∀ y ∈ upperHalf,
      β (F y) = harmonicPlane R p q y * deriv F y / conj (deriv F y)) ∧
      ∀ w ∉ F '' upperHalf, β w = 0 := hidentity t htI
  intro ξ
  let J : ℂ → ℂ := fun w => β w / ((w - b) ^ 2 * (w - ξ))
  have hJi : Integrable J volume := hvalue t htV ξ
  have hweight (y : ℂ) (hy : y ∈ upperHalf) : ‖deriv F y‖ ^ 2 • J (F y) =
      harmonicPlane R p q y * deriv F y ^ 2 / ((F y - b) ^ 2 * (F y - ξ)) := by
    have hn : ((‖deriv F y‖ ^ 2 : ℝ) : ℂ) = deriv F y * conj (deriv F y) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hcancel : deriv F y * conj (deriv F y) *
        (harmonicPlane R p q y * deriv F y / conj (deriv F y)) =
          harmonicPlane R p q y * deriv F y ^ 2 := by
      by_cases hd : deriv F y = 0
      · simp only [hd, map_zero, mul_zero, zero_div, zero_pow two_ne_zero]
      · have hc : conj (deriv F y) ≠ 0 := (map_ne_zero _).2 hd
        rw [div_eq_mul_inv]
        calc
          _ = harmonicPlane R p q y * deriv F y ^ 2 *
              (conj (deriv F y) * (conj (deriv F y))⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ hc, mul_one]
    dsimp only [J]
    rw [Complex.real_smul, hid.1 y hy, hn, ← mul_div_assoc, hcancel]
  have hPull := (ahP_integrableOn_image isOpen_upperHalf hhol hinj J).1 hJi.integrableOn
  refine ⟨hPull.congr_fun hweight isOpen_upperHalf.measurableSet, ?_⟩
  have hrestrict : (∫ w : ℂ in F '' upperHalf, J w) = ∫ w : ℂ, J w := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    change β w / ((w - b) ^ 2 * (w - ξ)) = 0
    rw [hid.2 w hw, zero_div]
  unfold cauchyT
  have hfun : (fun w : ℂ => (β w / (w - b) ^ 2) / (w - ξ)) = J := by
    funext w
    exact div_div _ _ _
  rw [hfun, ← hrestrict, ahP_integral_image isOpen_upperHalf hhol hinj J]
  congr 1
  exact setIntegral_congr_fun isOpen_upperHalf.measurableSet hweight

private theorem actual_passive_weighted_target_cauchy_at_pole
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
      let F := canonicalBiparameterFamily R p q 0 t
      let b := F (conj (z : ℂ))
      let β := ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
        (harmonicBiparameterCoefficient R p q 0 t) F
      DifferentiableAt ℂ (cauchyT (fun w => β w / (w - b) ^ 2)) b := by
  obtain ⟨εB, M, hεB, _, hβ⟩ := actual_passive_pushed_coefficient_measurable_bound R p hp q
  obtain ⟨εG, d, hεG, hd, hgap⟩ := actual_passive_pole_image_gap R p hp q z
  obtain ⟨εI, hεI, hidentity⟩ := actual_passive_pushed_coefficient_identity R p hp q
  obtain ⟨εV, hεV, hvalue⟩ := actual_passive_weighted_target_cauchy_integrable R p hp q z
  let ε := min εB (min εG (min εI εV))
  have hε : 0 < ε := lt_min hεB (lt_min hεG (lt_min hεI hεV))
  refine ⟨ε, hε, ?_⟩
  intro t ht
  dsimp only
  let F := canonicalBiparameterFamily R p q 0 t
  let b := F (conj (z : ℂ))
  let β := ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
    (harmonicBiparameterCoefficient R p q 0 t) F
  let φ : ℂ → ℂ := fun w => β w / (w - b) ^ 2
  have htB : ‖t‖ < εB := ht.trans_le (min_le_left _ _)
  have htG : ‖t‖ < εG := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htI : ‖t‖ < εI := ht.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htV : ‖t‖ < εV := ht.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hφm : AEStronglyMeasurable φ volume :=
    (hβ t htB).1.div₀ ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable
  have hzero (w : ℂ) (hw : ‖w - b‖ ≤ 2 * (d / 4)) : φ w = 0 := by
    have hout : w ∉ F '' upperHalf := by
      rintro ⟨y, hy, rfl⟩
      have hsep := hgap t htG y hy
      linarith
    change β w / (w - b) ^ 2 = 0
    have hβzero : β w = 0 := (hidentity t htI).2 w hout
    rw [hβzero, zero_div]
  have hfirst : Integrable (fun w : ℂ => φ w / (w - b)) volume := by
    simpa only [φ, div_div] using hvalue t htV b
  have hbound (w : ℂ) :
      ‖φ w / (w - b) ^ 2‖ ≤ d⁻¹ * ‖φ w / (w - b)‖ := by
    by_cases hw : φ w = 0
    · simp only [hw, zero_div, norm_zero, mul_zero, le_refl]
    · have himage : w ∈ F '' upperHalf := by
        by_contra hout
        apply hw
        change β w / (w - b) ^ 2 = 0
        have hβzero : β w = 0 := (hidentity t htI).2 w hout
        rw [hβzero, zero_div]
      obtain ⟨y, hy, rfl⟩ := himage
      have hsep := hgap t htG y hy
      calc
        _ = ‖φ (F y)‖ / ‖F y - b‖ ^ 2 := by
          rw [norm_div (φ (F y)) ((F y - b) ^ 2), Complex.norm_pow (F y - b) 2]
        _ = (‖φ (F y)‖ / ‖F y - b‖) / ‖F y - b‖ := by rw [div_div, pow_two]
        _ ≤ (‖φ (F y)‖ / ‖F y - b‖) / d :=
          div_le_div_of_nonneg_left (by positivity) hd hsep
        _ = d⁻¹ * (‖φ (F y)‖ / ‖F y - b‖) := by ring
        _ = d⁻¹ * ‖φ (F y) / (F y - b)‖ :=
          congrArg (fun r : ℝ => d⁻¹ * r) (norm_div (φ (F y)) (F y - b)).symm
  have hsquare : Integrable (fun w : ℂ => φ w / (w - b) ^ 2) volume :=
    (hfirst.norm.const_mul d⁻¹).mono'
      (hφm.div₀ ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall hbound)
  exact (cauchy_tail_hasDerivAt hφm (by positivity : 0 < d / 4)
    hzero hfirst hsquare).differentiableAt

private theorem normalized_resolvent_identity {z a w : ℂ}
    (hza : z ≠ a) (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hwz : w ≠ z) (hwa : w ≠ a) :
    (ahKer z w - ahKer a w - (z - a) *
        (1 / (w - a) ^ 2 - 1 / (w * (w - 1)))) / (z - a) ^ 2 =
      1 / ((w - a) ^ 2 * (w - z)) := by
  unfold ahKer
  field_simp [sub_ne_zero.mpr hza, sub_ne_zero.mpr hw1,
    sub_ne_zero.mpr hwz, sub_ne_zero.mpr hwa, hw0]
  ring

theorem actual_passive_normalized_resolvent
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
      let F := canonicalBiparameterFamily R p q 0 t
      let b := F (conj (z : ℂ))
      let β := ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
        (harmonicBiparameterCoefficient R p q 0 t) F
      ∃ D : ℂ, HasDerivAt (ahVar β) D b ∧
        ∀ ξ : ℂ, ξ ≠ b →
          (ahVar β ξ - ahVar β b - (ξ - b) * D) / (ξ - b) ^ 2 =
            cauchyT (fun w => β w / (w - b) ^ 2) ξ := by
  obtain ⟨εB, M, hεB, _, hβ⟩ := actual_passive_pushed_coefficient_measurable_bound R p hp q
  obtain ⟨εV, hεV, hvalue⟩ := actual_passive_weighted_target_cauchy_integrable R p hp q z
  obtain ⟨εT, hεT, hT⟩ := actual_passive_weighted_target_cauchy_at_pole R p hp q z
  let ε := min εB (min εV εT)
  have hε : 0 < ε := lt_min hεB (lt_min hεV hεT)
  refine ⟨ε, hε, ?_⟩
  intro t ht
  dsimp only
  let F := canonicalBiparameterFamily R p q 0 t
  let b := F (conj (z : ℂ))
  let β := ahT_dot (fun w : ℂ => if w.im < 0 then 0 else harmonicPlane R p q w)
    (harmonicBiparameterCoefficient R p q 0 t) F
  let φ : ℂ → ℂ := fun w => β w / (w - b) ^ 2
  let A : ℂ → ℂ → ℂ := fun ξ w => β w * ahKer ξ w
  let C : ℂ → ℂ := fun w => β w *
    (1 / (w - b) ^ 2 - 1 / (w * (w - 1)))
  let D : ℂ := -(1 / Real.pi : ℂ) * ∫ w : ℂ, C w
  have htB : ‖t‖ < εB := ht.trans_le (min_le_left _ _)
  have htV : ‖t‖ < εV := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htT : ‖t‖ < εT := ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hβm, hβbound⟩ := hβ t htB
  have hAi (ξ : ℂ) : Integrable (A ξ) volume :=
    (ah_ker_integrable ξ).bdd_mul hβm (Eventually.of_forall hβbound)
  have hCi : Integrable C volume := by
    have h0 : Integrable (fun w : ℂ => b ^ 2 * (β w / ((w - b) ^ 2 * w))) volume := by
      simpa only [sub_zero] using (hvalue t htV 0).const_mul (b ^ 2)
    have h1 : Integrable (fun w : ℂ => (b - 1) ^ 2 * (β w / ((w - b) ^ 2 * (w - 1)))) volume :=
      (hvalue t htV 1).const_mul ((b - 1) ^ 2)
    apply (h0.sub' h1).congr
    filter_upwards [volume.ae_ne (0 : ℂ), volume.ae_ne (1 : ℂ), volume.ae_ne b]
      with w hw0 hw1 hwb
    dsimp only [C]
    field_simp [hw0, sub_ne_zero.mpr hw1, sub_ne_zero.mpr hwb]
    ring
  have hrep (ξ : ℂ) : ahVar β ξ - ahVar β b - (ξ - b) * D =
      (ξ - b) ^ 2 * cauchyT φ ξ := by
    by_cases hξ : ξ = b
    · simp only [hξ, sub_self, zero_mul, zero_pow two_ne_zero]
    · have hpoint : (fun w : ℂ => A ξ w - A b w - (ξ - b) * C w) =ᵐ[volume]
          fun w => (ξ - b) ^ 2 * (β w / ((w - b) ^ 2 * (w - ξ))) := by
        filter_upwards [volume.ae_ne (0 : ℂ), volume.ae_ne (1 : ℂ),
          volume.ae_ne ξ, volume.ae_ne b] with w hw0 hw1 hwξ hwb
        have he := (div_eq_iff (pow_ne_zero 2 (sub_ne_zero.mpr hξ))).mp
          (normalized_resolvent_identity hξ hw0 hw1 hwξ hwb)
        calc
          A ξ w - A b w - (ξ - b) * C w = β w *
              (ahKer ξ w - ahKer b w - (ξ - b) *
                (1 / (w - b) ^ 2 - 1 / (w * (w - 1)))) := by
            dsimp only [A, C]
            ring
          _ = β w * (1 / ((w - b) ^ 2 * (w - ξ)) * (ξ - b) ^ 2) := by rw [he]
          _ = _ := by ring
      have hi : (∫ w : ℂ, A ξ w) - (∫ w : ℂ, A b w) - (ξ - b) * (∫ w : ℂ, C w) =
          (ξ - b) ^ 2 * ∫ w : ℂ, β w / ((w - b) ^ 2 * (w - ξ)) := by
        calc
          _ = ∫ w : ℂ, A ξ w - A b w - (ξ - b) * C w := by
            rw [integral_sub ((hAi ξ).sub' (hAi b)) (hCi.const_mul (ξ - b)),
              integral_sub (hAi ξ) (hAi b), integral_const_mul]
          _ = ∫ w : ℂ, (ξ - b) ^ 2 *
              (β w / ((w - b) ^ 2 * (w - ξ))) := integral_congr_ae hpoint
          _ = _ := integral_const_mul _ _
      calc
        ahVar β ξ - ahVar β b - (ξ - b) * D = -(1 / Real.pi : ℂ) *
            ((∫ w : ℂ, A ξ w) - (∫ w : ℂ, A b w) - (ξ - b) * (∫ w : ℂ, C w)) := by
          dsimp only [ahVar, D, A]
          ring
        _ = -(1 / Real.pi : ℂ) * ((ξ - b) ^ 2 *
            ∫ w : ℂ, β w / ((w - b) ^ 2 * (w - ξ))) := by rw [hi]
        _ = (ξ - b) ^ 2 * cauchyT φ ξ := by
          simp only [cauchyT, φ, div_div]
          ring
  have hformula (ξ : ℂ) : ahVar β ξ =
      ahVar β b + (ξ - b) * D + (ξ - b) ^ 2 * cauchyT φ ξ := by
    calc
      ahVar β ξ = (ahVar β ξ - ahVar β b - (ξ - b) * D) +
          ahVar β b + (ξ - b) * D := by ring
      _ = _ := by rw [hrep]; ring
  have hid : HasDerivAt (fun ξ : ℂ => ξ - b) 1 b := (hasDerivAt_id b).sub_const b
  have hquad : HasDerivAt (fun ξ : ℂ => (ξ - b) ^ 2 * cauchyT φ ξ) 0 b := by
    have hd : DifferentiableAt ℂ (cauchyT φ) b := hT t htT
    convert (hid.pow 2).fun_mul hd.hasDerivAt using 1; simp
  have hfull : HasDerivAt (fun ξ : ℂ =>
      ahVar β b + (ξ - b) * D + (ξ - b) ^ 2 * cauchyT φ ξ) D b := by
    simpa only [one_mul, add_zero] using
      ((hid.mul_const D).const_add (ahVar β b)).fun_add hquad
  refine ⟨D, hfull.congr_of_eventuallyEq (Eventually.of_forall hformula), ?_⟩
  intro ξ hξ
  apply (div_eq_iff (pow_ne_zero 2 (sub_ne_zero.mpr hξ))).2
  exact (hrep ξ).trans (mul_comm _ _)


end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
