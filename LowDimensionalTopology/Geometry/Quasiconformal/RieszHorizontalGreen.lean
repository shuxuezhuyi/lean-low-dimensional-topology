module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Horizontal integrals of a decaying subharmonic function

The rectangle divergence theorem expresses the Laplacian integral by
normal derivatives. For a C² subharmonic function on the upper half-plane,
uniform square decay of the function and its derivative allows the
rectangle boundaries to tend to infinity. Every horizontal integral is
then nonnegative.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Mathlib's finite rectangle formula written with the actual complex-plane
Laplacian. The C2 premise is local on the original upper half-plane, where
the book's Cauchy auxiliary function will supply it. -/
theorem riesz_rectangle_laplacian_flux {U : ℂ → ℝ}
    (hU : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 2 U z)
    (a b c d : ℝ) (hcd : 0 < min c d) :
    (∫ x : ℝ in a..b, ∫ y : ℝ in c..d,
      Laplacian.laplacian U ((x : ℂ) + (y : ℂ) * I)) =
      ((∫ x : ℝ in a..b, fderiv ℝ U ((x : ℂ) + (d : ℂ) * I) I) -
        ∫ x : ℝ in a..b, fderiv ℝ U ((x : ℂ) + (c : ℂ) * I) I) +
      (∫ y : ℝ in c..d, fderiv ℝ U ((b : ℂ) + (y : ℂ) * I) 1) -
        ∫ y : ℝ in c..d, fderiv ℝ U ((a : ℂ) + (y : ℂ) * I) 1 := by
  let e : (ℝ × ℝ) →L[ℝ] ℂ := Complex.equivRealProdCLM.symm
  let R : Set (ℝ × ℝ) := uIcc a b ×ˢ uIcc c d
  let H (q : ℝ × ℝ) := fderiv ℝ (fderiv ℝ U) (e q)
  let fx (q : ℝ × ℝ) := fderiv ℝ U (e q) (1 : ℂ)
  let fy (q : ℝ × ℝ) := fderiv ℝ U (e q) I
  let dx (q : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).comp ((H q).comp e)
  let dy (q : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ I).comp ((H q).comp e)
  have he (x y : ℝ) : e (x, y) = (x : ℂ) + (y : ℂ) * I :=
    Complex.mk_eq_add_mul_I x y
  have he_one : e (1, 0) = 1 := rfl
  have he_I : e (0, 1) = I := rfl
  have hupper (q : ℝ × ℝ) (hq : q ∈ R) : 0 < (e q).im := by
    have hmin : min c d ≤ q.2 := hq.2.1
    exact hcd.trans_le hmin
  have hgrad (q : ℝ × ℝ) (hq : q ∈ R) :
      ContDiffAt ℝ 1 (fderiv ℝ U) (e q) :=
    (hU (e q) (hupper q hq)).fderiv_right (by norm_num)
  have hcf : ContinuousOn fx R := by
    intro q hq
    exact (((hgrad q hq).continuousAt.comp e.continuous.continuousAt).clm_apply
      continuousAt_const).continuousWithinAt
  have hcg : ContinuousOn fy R := by
    intro q hq
    exact (((hgrad q hq).continuousAt.comp e.continuous.continuousAt).clm_apply
      continuousAt_const).continuousWithinAt
  have hdx (q : ℝ × ℝ) (hq : q ∈ R) : HasFDerivAt fx (dx q) q := by
    exact (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).hasFDerivAt.comp q
      (((hgrad q hq).differentiableAt one_ne_zero).hasFDerivAt.comp q e.hasFDerivAt)
  have hdy (q : ℝ × ℝ) (hq : q ∈ R) : HasFDerivAt fy (dy q) q := by
    exact (ContinuousLinearMap.apply ℝ ℝ I).hasFDerivAt.comp q
      (((hgrad q hq).differentiableAt one_ne_zero).hasFDerivAt.comp q e.hasFDerivAt)
  have htrace (q : ℝ × ℝ) :
      dx q (1, 0) + dy q (0, 1) = Laplacian.laplacian U (e q) := by
    simp only [dx, dy, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      he_one, he_I, H, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hct : ContinuousOn (fun q => dx q (1, 0) + dy q (0, 1)) R := by
    intro q hq
    have hh : ContinuousAt H q :=
      ((hgrad q hq).continuousAt_fderiv one_ne_zero).comp e.continuous.continuousAt
    have h11 : ContinuousAt (fun t => H t (1 : ℂ) (1 : ℂ)) q :=
      (hh.clm_apply continuousAt_const).clm_apply continuousAt_const
    have hII : ContinuousAt (fun t => H t I I) q :=
      (hh.clm_apply continuousAt_const).clm_apply continuousAt_const
    have ht := h11.add hII
    simpa only [dx, dy, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      he_one, he_I] using! ht.continuousWithinAt (s := R)
  have hi : IntegrableOn (fun q => dx q (1, 0) + dy q (0, 1)) R :=
    ContinuousOn.integrableOn_compact (μ := (volume : Measure (ℝ × ℝ)))
      (isCompact_uIcc.prod isCompact_uIcc) hct
  have hopen : Ioo (min a b) (max a b) ×ˢ Ioo (min c d) (max c d) ⊆ R := by
    intro q hq
    exact ⟨⟨hq.1.1.le, hq.1.2.le⟩, ⟨hq.2.1.le, hq.2.2.le⟩⟩
  have hflux := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    fx fy dx dy a c b d hcf hcg
    (fun q hq => hdx q (hopen hq)) (fun q hq => hdy q (hopen hq)) hi
  simp_rw [htrace] at hflux
  simpa only [fx, fy, he] using hflux

end LowDimensionalTopology.Geometry.Quasiconformal

namespace LowDimensionalTopology.Geometry.Quasiconformal

open Filter Topology

private theorem riesz_square_profile_integrable (C : ℝ) :
    Integrable (fun x : ℝ => C / (1 + ‖x‖) ^ 2) (volume : Measure ℝ) := by
  have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
    (by norm_num)).const_mul C
  exact h.congr (Filter.Eventually.of_forall fun x => by
    simp only [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), Real.rpow_two,
      div_eq_mul_inv])

private theorem riesz_square_horizontal_control {V : ℂ → ℝ}
    (hV : ∀ η : ℝ, 0 < η → Continuous (fun x : ℝ => V ((x : ℂ) + (η : ℂ) * I)))
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, δ ≤ z.im → ‖V z‖ ≤ C / (1 + ‖z‖) ^ 2) :
    (∀ η : ℝ, δ ≤ η → Integrable (fun x : ℝ => V ((x : ℂ) + (η : ℂ) * I))) ∧
      Filter.Tendsto (fun η : ℝ => ∫ x : ℝ, V ((x : ℂ) + (η : ℂ) * I))
        Filter.atTop (nhds 0) := by
  have hline (η : ℝ) (hη : δ ≤ η) (x : ℝ) :
      ‖V ((x : ℂ) + (η : ℂ) * I)‖ ≤ C / (1 + ‖x‖) ^ 2 := by
    have hxnorm : ‖x‖ ≤ ‖(x : ℂ) + (η : ℂ) * I‖ := by
      simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
        Real.norm_eq_abs] using Complex.abs_re_le_norm ((x : ℂ) + (η : ℂ) * I)
    have hz := hb ((x : ℂ) + (η : ℂ) * I) (by simpa using hη)
    exact hz.trans (by gcongr)
  have hint (η : ℝ) (hη : δ ≤ η) :
      Integrable (fun x : ℝ => V ((x : ℂ) + (η : ℂ) * I)) :=
    (riesz_square_profile_integrable C).mono'
      (hV η (hδ.trans_le hη)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hline η hη))
  have hscalar : Filter.Tendsto (fun η : ℝ => C / (1 + η) ^ 2)
      Filter.atTop (nhds (0 : ℝ)) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        (Filter.tendsto_atTop_add_const_left (Filter.atTop : Filter ℝ) 1 Filter.tendsto_id))
  have hpoint (x : ℝ) : Filter.Tendsto (fun η : ℝ => V ((x : ℂ) + (η : ℂ) * I))
      Filter.atTop (nhds (0 : ℝ)) := by
    apply (tendsto_zero_iff_norm_tendsto_zero
      (f := fun η : ℝ => V ((x : ℂ) + (η : ℂ) * I))).2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (f := fun η : ℝ => ‖V ((x : ℂ) + (η : ℂ) * I)‖)
      (g := fun _ : ℝ => (0 : ℝ)) (h := fun η : ℝ => C / (1 + η) ^ 2)
      tendsto_const_nhds hscalar
    · exact Filter.Eventually.of_forall fun η => norm_nonneg _
    · filter_upwards [Filter.eventually_ge_atTop δ] with η hη
      have hη0 : 0 < η := hδ.trans_le hη
      have hηnorm : η ≤ ‖(x : ℂ) + (η : ℂ) * I‖ := by
        simpa [abs_of_pos hη0] using
          Complex.abs_im_le_norm ((x : ℂ) + (η : ℂ) * I)
      exact (hb _ (by simpa using hη)).trans (by gcongr)
  refine ⟨hint, ?_⟩
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ)) (fun x : ℝ => C / (1 + ‖x‖) ^ 2)
    ((Filter.eventually_ge_atTop δ).mono fun η hη =>
      (hV η (hδ.trans_le hη)).aestronglyMeasurable)
    ((Filter.eventually_ge_atTop δ).mono fun η hη =>
      Filter.Eventually.of_forall (hline η hη))
    (riesz_square_profile_integrable C)
    (Filter.Eventually.of_forall hpoint)
  simpa using hlim

/-- The Green/decay passage used for the book's auxiliary function.
All premises are ordinary pointwise regularity, Laplacian and decay facts;
the integral inequality is derived, and no boundary identity is assumed.
The actual Cauchy-W calculation must supply these explicit premises. -/
theorem riesz_horizontal_integral_nonneg_of_laplacian_and_decay {U : ℂ → ℝ}
    (hU : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 2 U z)
    (hΔ : ∀ z : ℂ, 0 < z.im → 0 ≤ Laplacian.laplacian U z)
    (hdecay : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, δ ≤ z.im →
      ‖U z‖ ≤ C / (1 + ‖z‖) ^ 2 ∧ ‖fderiv ℝ U z‖ ≤ C / (1 + ‖z‖) ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    0 ≤ ∫ x : ℝ, U ((x : ℂ) + (ε : ℂ) * I) := by
  let V (z : ℂ) : ℝ := fderiv ℝ U z I
  let G (η : ℝ) : ℝ := ∫ x : ℝ, U ((x : ℂ) + (η : ℂ) * I)
  let H (η : ℝ) : ℝ := ∫ x : ℝ, V ((x : ℂ) + (η : ℂ) * I)
  have huc (η : ℝ) (hη : 0 < η) :
      Continuous (fun x : ℝ => U ((x : ℂ) + (η : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hU _ (by simpa using hη)).continuousAt.comp (by fun_prop)
  have hvc (η : ℝ) (hη : 0 < η) :
      Continuous (fun x : ℝ => V ((x : ℂ) + (η : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (((hU _ (by simpa using hη)).continuousAt_fderiv two_ne_zero).clm_apply
      continuousAt_const).comp (by fun_prop)
  have hvbound (z : ℂ) : ‖V z‖ ≤ ‖fderiv ℝ U z‖ :=
    (fderiv ℝ U z).unit_le_opNorm I (by simp)
  have hucontrol (δ : ℝ) (hδ : 0 < δ) :
      (∀ η : ℝ, δ ≤ η → Integrable (fun x : ℝ => U ((x : ℂ) + (η : ℂ) * I))) ∧
      Filter.Tendsto G Filter.atTop (nhds 0) := by
    obtain ⟨C, hC, hb⟩ := hdecay δ hδ
    exact riesz_square_horizontal_control huc hδ hC (fun z hz => (hb z hz).1)
  have hvcontrol (δ : ℝ) (hδ : 0 < δ) :
      (∀ η : ℝ, δ ≤ η → Integrable (fun x : ℝ => V ((x : ℂ) + (η : ℂ) * I))) ∧
      Filter.Tendsto H Filter.atTop (nhds 0) := by
    obtain ⟨C, hC, hb⟩ := hdecay δ hδ
    exact riesz_square_horizontal_control hvc hδ hC
      (fun z hz => (hvbound z).trans (hb z hz).2)
  have huid (η : ℝ) (hη : 0 < η) :
      Integrable (fun x : ℝ => U ((x : ℂ) + (η : ℂ) * I)) :=
    (hucontrol η hη).1 η le_rfl
  have hvid (η : ℝ) (hη : 0 < η) :
      Integrable (fun x : ℝ => V ((x : ℂ) + (η : ℂ) * I)) :=
    (hvcontrol η hη).1 η le_rfl
  have hGH (η : ℝ) (hη : 0 < η) : HasDerivAt G (H η) η := by
    let δ : ℝ := η / 2
    have hδ : 0 < δ := half_pos hη
    obtain ⟨C, hC, hb⟩ := hdecay δ hδ
    have hline (t : ℝ) (ht : δ < t) (x : ℝ) :
        ‖V ((x : ℂ) + (t : ℂ) * I)‖ ≤ C / (1 + ‖x‖) ^ 2 := by
      have hx : ‖x‖ ≤ ‖(x : ℂ) + (t : ℂ) * I‖ := by
        simpa [Real.norm_eq_abs] using
          Complex.abs_re_le_norm ((x : ℂ) + (t : ℂ) * I)
      exact ((hvbound _).trans (hb _ (by simpa using ht.le)).2).trans (by gcongr)
    have hvertical (x t : ℝ) (ht : δ < t) :
        HasDerivAt (fun y : ℝ => U ((x : ℂ) + (y : ℂ) * I))
          (V ((x : ℂ) + (t : ℂ) * I)) t := by
      have hm : HasDerivAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) I t := by
        simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
          ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (x : ℂ)
      exact (((hU ((x : ℂ) + (t : ℂ) * I) (by simpa using hδ.trans ht)).differentiableAt
        two_ne_zero).hasFDerivAt).comp_hasDerivAt t hm
    have hlocal : Ioi δ ∈ nhds η := Ioi_mem_nhds (by dsimp [δ]; linarith)
    have hevent : ∀ᶠ t : ℝ in nhds η, δ < t :=
      eventually_gt_nhds (by dsimp [δ]; linarith)
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure ℝ)) (F := fun t x : ℝ => U ((x : ℂ) + (t : ℂ) * I))
      (F' := fun t x : ℝ => V ((x : ℂ) + (t : ℂ) * I))
      (bound := fun x : ℝ => C / (1 + ‖x‖) ^ 2) hlocal
      (hevent.mono fun t ht => (huc t (hδ.trans ht)).aestronglyMeasurable)
      (huid η hη) (hvc η hη).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x t ht => hline t ht x)
      (riesz_square_profile_integrable C)
      (Filter.Eventually.of_forall hvertical)).2
  have hHmono : MonotoneOn H (Ioi (0 : ℝ)) := by
    intro c hc d hd hcd
    obtain ⟨C, hC, hb⟩ := hdecay c hc
    let B (r : ℝ) := C / (1 + ‖r‖) ^ 2 * |d - c|
    have hside (r : ℝ) :
        ‖∫ y : ℝ in c..d, fderiv ℝ U ((r : ℂ) + (y : ℂ) * I) 1‖ ≤ B r := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hyIoc : y ∈ Ioc c d := by simpa only [uIoc_of_le hcd] using hy
      have hyc : c ≤ y := hyIoc.1.le
      have hr : ‖r‖ ≤ ‖(r : ℂ) + (y : ℂ) * I‖ := by
        simpa [Real.norm_eq_abs] using
          Complex.abs_re_le_norm ((r : ℂ) + (y : ℂ) * I)
      calc
        _ ≤ ‖fderiv ℝ U ((r : ℂ) + (y : ℂ) * I)‖ :=
          (fderiv ℝ U _).unit_le_opNorm (1 : ℂ) (by simp)
        _ ≤ C / (1 + ‖(r : ℂ) + (y : ℂ) * I‖) ^ 2 :=
          (hb _ (by simpa using hyc)).2
        _ ≤ C / (1 + ‖r‖) ^ 2 := by gcongr
    have hB : Filter.Tendsto B Filter.atTop (nhds (0 : ℝ)) := by
      have hquot : Filter.Tendsto (fun r : ℝ => C / (1 + r) ^ 2)
          Filter.atTop (nhds (0 : ℝ)) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
            (Filter.tendsto_atTop_add_const_left (Filter.atTop : Filter ℝ) 1 Filter.tendsto_id))
      have hraw : Filter.Tendsto (fun r : ℝ => C / (1 + r) ^ 2 * |d - c|)
          Filter.atTop (nhds (0 : ℝ)) := by
        simpa using hquot.mul_const |d - c|
      exact hraw.congr' ((Filter.eventually_ge_atTop (0 : ℝ)).mono fun r hr => by
        simp only [B, Real.norm_eq_abs, abs_of_nonneg hr])
    have hright : Filter.Tendsto
        (fun r : ℝ => ∫ y : ℝ in c..d, fderiv ℝ U ((r : ℂ) + (y : ℂ) * I) 1)
        Filter.atTop (nhds 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le
        (f := fun r : ℝ => ‖∫ y : ℝ in c..d, fderiv ℝ U ((r : ℂ) + (y : ℂ) * I) 1‖)
        (g := fun _ : ℝ => (0 : ℝ)) (h := B)
        tendsto_const_nhds hB (fun r => norm_nonneg _) hside
    have hleft : Filter.Tendsto
        (fun r : ℝ => ∫ y : ℝ in c..d, fderiv ℝ U ((-r : ℂ) + (y : ℂ) * I) 1)
        Filter.atTop (nhds 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le
        (f := fun r : ℝ => ‖∫ y : ℝ in c..d, fderiv ℝ U ((-r : ℂ) + (y : ℂ) * I) 1‖)
        (g := fun _ : ℝ => (0 : ℝ)) (h := B)
        tendsto_const_nhds hB (fun r => norm_nonneg _)
        (fun r => by simpa only [B, norm_neg, Complex.ofReal_neg] using hside (-r))
    have htop : Tendsto
        (fun r : ℝ => ∫ x : ℝ in -r..r, V ((x : ℂ) + (d : ℂ) * I))
        atTop (nhds (H d)) :=
      MeasureTheory.intervalIntegral_tendsto_integral
        (a := fun r : ℝ => -r) (b := fun r : ℝ => r)
        (hvid d hd) tendsto_neg_atTop_atBot Filter.tendsto_id
    have hbottom : Tendsto
        (fun r : ℝ => ∫ x : ℝ in -r..r, V ((x : ℂ) + (c : ℂ) * I))
        atTop (nhds (H c)) :=
      MeasureTheory.intervalIntegral_tendsto_integral
        (a := fun r : ℝ => -r) (b := fun r : ℝ => r)
        (hvid c hc) tendsto_neg_atTop_atBot Filter.tendsto_id
    have hfluxlim := ((htop.sub hbottom).add hright).sub hleft
    have hnonneg : ∀ᶠ r : ℝ in Filter.atTop,
        0 ≤ ((∫ x : ℝ in -r..r, V ((x : ℂ) + (d : ℂ) * I)) -
          ∫ x : ℝ in -r..r, V ((x : ℂ) + (c : ℂ) * I)) +
          (∫ y : ℝ in c..d, fderiv ℝ U ((r : ℂ) + (y : ℂ) * I) 1) -
          ∫ y : ℝ in c..d, fderiv ℝ U ((-r : ℂ) + (y : ℂ) * I) 1 := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with r hr
      change 0 ≤ ((∫ x : ℝ in -r..r, fderiv ℝ U ((x : ℂ) + (d : ℂ) * I) I) -
        ∫ x : ℝ in -r..r, fderiv ℝ U ((x : ℂ) + (c : ℂ) * I) I) +
        (∫ y : ℝ in c..d, fderiv ℝ U ((r : ℂ) + (y : ℂ) * I) 1) -
        ∫ y : ℝ in c..d, fderiv ℝ U ((-r : ℂ) + (y : ℂ) * I) 1
      have hrect := riesz_rectangle_laplacian_flux hU (-r) r c d
        (by simpa [min_eq_left hcd] using hc)
      simp only [Complex.ofReal_neg] at hrect
      rw [← hrect]
      apply intervalIntegral.integral_nonneg_of_forall (by linarith)
      intro x
      apply intervalIntegral.integral_nonneg hcd
      intro y hy
      exact hΔ _ (by simpa using hc.trans_le hy.1)
    have hdiff : 0 ≤ H d - H c := by
      have hlim : Filter.Tendsto
          (fun r : ℝ => ((∫ x : ℝ in -r..r, V ((x : ℂ) + (d : ℂ) * I)) -
            ∫ x : ℝ in -r..r, V ((x : ℂ) + (c : ℂ) * I)) +
            (∫ y : ℝ in c..d, fderiv ℝ U ((r : ℂ) + (y : ℂ) * I) 1) -
            ∫ y : ℝ in c..d, fderiv ℝ U ((-r : ℂ) + (y : ℂ) * I) 1)
          Filter.atTop (nhds (H d - H c)) := by
        simpa only [add_zero, sub_zero] using! hfluxlim
      exact ge_of_tendsto hlim hnonneg
    exact sub_nonneg.1 hdiff
  have hHnonpos (η : ℝ) (hη : 0 < η) : H η ≤ 0 :=
    ge_of_tendsto (hvcontrol 1 (by norm_num)).2
      ((Filter.eventually_ge_atTop η).mono fun t ht =>
        hHmono hη (hη.trans_le ht) ht)
  have hGanti : AntitoneOn G (Ioi (0 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ))
    · exact fun η hη => (hGH η hη).continuousAt.continuousWithinAt
    · intro η hη
      exact (hGH η (by simpa only [interior_Ioi, Set.mem_Ioi] using hη)).differentiableAt.differentiableWithinAt
    · intro η hη
      have hη0 : 0 < η := by simpa only [interior_Ioi, Set.mem_Ioi] using hη
      rw [(hGH η hη0).deriv]
      exact hHnonpos η hη0
  exact le_of_tendsto (hucontrol 1 (by norm_num)).2
    ((Filter.eventually_ge_atTop ε).mono fun t ht =>
      hGanti hε (hε.trans_le ht) ht)

end LowDimensionalTopology.Geometry.Quasiconformal
