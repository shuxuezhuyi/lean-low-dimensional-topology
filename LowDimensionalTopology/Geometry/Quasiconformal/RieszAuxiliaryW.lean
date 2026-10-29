module

public import LowDimensionalTopology.External.LiZhongQC.Ch03.S15_Distortion
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The second derivative needed for the Riesz auxiliary function

The real Hilbert-transform estimate differentiates
`W = |F|^p - p/(p-1)|Re F|^p` twice, including zeros and the endpoint
`p=2`. The local helpers below supply precisely that elementary norm-power
calculation. Mathlib's existing first-derivative theorem is used throughout.
No Green formula, slice inequality or Hilbert-transform bound is assumed.

The off-zero norm-power derivative is reused from Wu Xiaobin's
Li-Zhong-QC-formalization, commit1c0d5473c020b66ed5106331a38a61536760b9b2,
`s15_ra_hasFDerivAt_norm_rpow` (Apache2.0, original notices retained there).
-/

@[expose] public section
noncomputable section

open Filter Topology
open scoped InnerProductSpace

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid

namespace LowDimensionalTopology.Geometry.Quasiconformal

private abbrev rieszRealInner : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := innerSL ℝ

private def rieszNormGradient (p : ℝ) (x : ℂ) : ℂ →L[ℝ] ℝ :=
  (p * ‖x‖ ^ (p - 2)) • innerSL ℝ x

private def rieszNormHessian (p : ℝ) (x : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (p * ‖x‖ ^ (p - 2)) • rieszRealInner +
    ((p * (p - 2) * ‖x‖ ^ (p - 4)) • innerSL ℝ x).smulRight (innerSL ℝ x)

private theorem rieszNormHessian_two (x : ℂ) :
    rieszNormHessian 2 x = (2 : ℝ) • rieszRealInner := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp [rieszNormHessian, smul_apply]

private theorem rieszNormHessian_zero {p : ℝ} (hp : 2 < p) :
    rieszNormHessian p 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp [rieszNormHessian, (sub_pos.2 hp).ne', smul_apply]

private theorem rieszRealInner_smul_norm_le (c : ℝ) (hc : 0 ≤ c) :
    ‖c • rieszRealInner‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro v
  simp only [smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hc, rieszRealInner]
  rw [innerSL_apply_norm ℝ v]

private theorem hasFDerivAt_rieszNormGradient_zero {p : ℝ} (hp : 2 < p) :
    HasFDerivAt (rieszNormGradient p) (0 : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (0 : ℂ) := by
  have hp1 : 1 < p := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have hnorm (x : ℂ) : ‖rieszNormGradient p x‖ = p * ‖x‖ ^ (p - 1) := by
    simpa only [rieszNormGradient, ← fderiv_norm_rpow x hp1] using
      norm_fderiv_norm_id_rpow x hp1
  have hlimit : Tendsto (fun x : ℂ => p * ‖x‖ ^ (p - 2)) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℂ => p * ‖x‖ ^ (p - 2)) 0 := by
      exact continuousAt_const.mul
        (continuousAt_id.norm.rpow_const (Or.inr hp2.le))
    simpa [hp2.ne'] using hc.tendsto
  rw [hasFDerivAt_iff_tendsto]
  simp only [rieszNormGradient, norm_zero, map_zero, smul_zero,
    sub_zero, zero_apply]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimit
  · intro x
    positivity
  · intro x
    change ‖x‖⁻¹ * ‖rieszNormGradient p x‖ ≤ p * ‖x‖ ^ (p - 2)
    rw [hnorm]
    by_cases hx : x = 0
    · simp [hx, hp2.ne']
    · have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one hxnorm]
      field_simp
      norm_num

private theorem hasFDerivAt_rieszNormGradient {p : ℝ} (hp : 2 ≤ p) (x : ℂ) :
    HasFDerivAt (rieszNormGradient p) (rieszNormHessian p x) x := by
  rcases hp.eq_or_lt with rfl | hp
  · rw [rieszNormHessian_two]
    convert! (rieszRealInner.hasFDerivAt (x := x)).const_smul (2 : ℝ) using 1
    funext y
    simp [rieszNormGradient, Pi.smul_apply, rieszRealInner]
  by_cases hx : x = 0
  · subst x
    rw [rieszNormHessian_zero hp]
    exact hasFDerivAt_rieszNormGradient_zero hp
  have hscalar : HasFDerivAt (fun y : ℂ => p * ‖y‖ ^ (p - 2))
      ((p * (p - 2) * ‖x‖ ^ (p - 4)) • innerSL ℝ x) x := by
    have h := (LiZhongQC.s15_ra_hasFDerivAt_norm_rpow hx (p - 2)).const_mul p
    rw [show p - 2 - 2 = p - 4 by ring] at h
    convert! h using 1
    all_goals ext v
    all_goals simp only [smul_apply, smul_eq_mul]
    all_goals ring
  convert! hscalar.smul rieszRealInner.hasFDerivAt using 1

private theorem norm_rieszNormHessian_le {p : ℝ} (hp : 2 ≤ p) (x : ℂ) :
    ‖rieszNormHessian p x‖ ≤ p * (p - 1) * ‖x‖ ^ (p - 2) := by
  rcases hp.eq_or_lt with rfl | hp
  · rw [rieszNormHessian_two]
    have htwo : (2 : ℝ) * (2 - 1) * ‖x‖ ^ ((2 : ℝ) - 2) = 2 := by norm_num
    rw [htwo]
    exact rieszRealInner_smul_norm_le 2 (by norm_num)
  by_cases hx : x = 0
  · subst x
    rw [rieszNormHessian_zero hp, ContinuousLinearMap.opNorm_zero]
    simp [(sub_pos.2 hp).ne']
  have hp0 : 0 ≤ p := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  have hfirst : ‖(p * ‖x‖ ^ (p - 2)) • rieszRealInner‖ ≤
      p * ‖x‖ ^ (p - 2) := by
    exact rieszRealInner_smul_norm_le _ (by positivity)
  have hpow : ‖x‖ ^ (p - 4) * ‖x‖ ^ 2 = ‖x‖ ^ (p - 2) := by
    rw [← Real.rpow_two, ← Real.rpow_add (norm_pos_iff.2 hx)]
    congr 1
    ring
  have hsecond : ‖((p * (p - 2) * ‖x‖ ^ (p - 4)) • innerSL ℝ x).smulRight
      (innerSL ℝ x)‖ = p * (p - 2) * ‖x‖ ^ (p - 2) := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), innerSL_apply_norm]
    calc
      (p * (p - 2) * ‖x‖ ^ (p - 4) * ‖x‖) * ‖x‖ =
          p * (p - 2) * (‖x‖ ^ (p - 4) * ‖x‖ ^ 2) := by ring
      _ = _ := by rw [hpow]
  calc
    ‖rieszNormHessian p x‖ ≤
        ‖(p * ‖x‖ ^ (p - 2)) • rieszRealInner‖ +
          ‖((p * (p - 2) * ‖x‖ ^ (p - 4)) • innerSL ℝ x).smulRight
            (innerSL ℝ x)‖ := by
      simp only [rieszNormHessian]
      exact ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ p * ‖x‖ ^ (p - 2) + p * (p - 2) * ‖x‖ ^ (p - 2) := by
      rw [hsecond]
      exact add_le_add hfirst le_rfl
    _ = _ := by ring

private theorem continuous_rieszNormHessian {p : ℝ} (hp : 2 ≤ p) :
    Continuous (rieszNormHessian p) := by
  rcases hp.eq_or_lt with rfl | hp
  · have htwo : rieszNormHessian 2 = (fun _ : ℂ => (2 : ℝ) • rieszRealInner) :=
      funext rieszNormHessian_two
    rw [htwo]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hp2 : 0 < p - 2 := by linarith
    have hzero : rieszNormHessian p 0 = 0 := rieszNormHessian_zero hp
    change Tendsto (rieszNormHessian p) (𝓝 0) (𝓝 (rieszNormHessian p 0))
    rw [hzero]
    let nrm : ℂ → ℝ := fun y => ‖rieszNormHessian p y‖
    let bound : ℂ → ℝ := fun y => p * (p - 1) * ‖y‖ ^ (p - 2)
    have hbound : Tendsto bound (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := by
      have hc : ContinuousAt bound 0 := continuousAt_const.mul
        (continuousAt_id.norm.rpow_const (Or.inr hp2.le))
      simpa [bound, hp2.ne'] using hc.tendsto
    have hlo : ∀ y : ℂ, (0 : ℝ) ≤ nrm y :=
      fun y => ContinuousLinearMap.opNorm_nonneg (rieszNormHessian p y)
    have hhi : ∀ y : ℂ, nrm y ≤ bound y :=
      fun y => norm_rieszNormHessian_le hp.le y
    have hn : Tendsto nrm (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        (f := nrm) (g := fun _ : ℂ => (0 : ℝ)) (h := bound)
        tendsto_const_nhds hbound hlo hhi
    exact (tendsto_zero_iff_norm_tendsto_zero
      (f := rieszNormHessian p) (a := 𝓝 (0 : ℂ))).2 hn
  · change ContinuousAt (fun y : ℂ =>
      (p * ‖y‖ ^ (p - 2)) • rieszRealInner +
        ((p * (p - 2) * ‖y‖ ^ (p - 4)) • innerSL ℝ y).smulRight (innerSL ℝ y)) x
    have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have ha : ContinuousAt (fun y : ℂ => p * ‖y‖ ^ (p - 2)) x :=
      continuousAt_const.mul (continuousAt_id.norm.rpow_const (Or.inl hxnorm))
    have hb : ContinuousAt (fun y : ℂ => p * (p - 2) * ‖y‖ ^ (p - 4)) x :=
      continuousAt_const.mul (continuousAt_id.norm.rpow_const (Or.inl hxnorm))
    have hinner : ContinuousAt (fun y : ℂ => innerSL ℝ y) x :=
      rieszRealInner.continuous.continuousAt
    have hright : ContinuousAt (fun y : ℂ =>
        ((p * (p - 2) * ‖y‖ ^ (p - 4)) • innerSL ℝ y).smulRight (innerSL ℝ y)) x :=
      (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := ℂ) (F := ℂ →L[ℝ] ℝ)).continuous.continuousAt.comp
        ((hb.smul hinner).prodMk hinner)
    let : ContinuousAdd (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
      (ContinuousLinearMap.isTopologicalAddGroup
        (E := ℂ) (F := ℂ →L[ℝ] ℝ) (σ := RingHom.id ℝ)).toContinuousAdd
    exact (ha.smul continuousAt_const).add hright

/-- The twice-continuous differentiability used in the book's `W` calculation.
The zeros of the function and the original endpoint `p=2` are included. -/
theorem contDiff_two_complex_norm_rpow_riesz {p : ℝ} (hp : 2 ≤ p) :
    ContDiff ℝ 2 (fun x : ℂ => ‖x‖ ^ p) := by
  have hp1 : 1 < p := by linarith
  apply (contDiff_succ_iff_fderiv (n := 1)).2
  refine ⟨differentiable_norm_rpow hp1, by simp, ?_⟩
  have hgrad : fderiv ℝ (fun x : ℂ => ‖x‖ ^ p) = rieszNormGradient p := by
    funext x
    exact fderiv_norm_rpow x hp1
  rw [hgrad, contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_rieszNormGradient hp x).differentiableAt, ?_⟩
  have hhess : fderiv ℝ (rieszNormGradient p) = rieszNormHessian p := by
    funext x
    exact (hasFDerivAt_rieszNormGradient hp x).fderiv
  rw [hhess]
  exact continuous_rieszNormHessian hp

/-- The literal auxiliary function on values of the book's Cauchy integral. -/
def rieszAuxiliaryValue (p : ℝ) (w : ℂ) : ℝ :=
  ‖w‖ ^ p - p / (p - 1) * ‖w.re‖ ^ p

/-- No nonvanishing hypothesis is needed for the book's auxiliary function. -/
theorem contDiff_two_rieszAuxiliaryValue {p : ℝ} (hp : 2 ≤ p) :
    ContDiff ℝ 2 (rieszAuxiliaryValue p) := by
  have hreal : ContDiff ℝ 2 (fun x : ℝ => ‖x‖ ^ p) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.norm_real] using
      (contDiff_two_complex_norm_rpow_riesz hp).comp Complex.ofRealCLM.contDiff
  exact (contDiff_two_complex_norm_rpow_riesz hp).sub
    (contDiff_const.mul (hreal.comp Complex.reCLM.contDiff))

/-! The exact value-space Laplacian of the auxiliary function. -/

private theorem riesz_inner_complex (z w : ℂ) :
    inner ℝ z w = z.re * w.re + z.im * w.im := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  change (w * (starRingEnd ℂ) z).re = z.re * w.re + z.im * w.im
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem riesz_rpow_quadratic {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    p * (p - 2) * r ^ (p - 4) * r ^ 2 = p * (p - 2) * r ^ (p - 2) := by
  by_cases hzero : r = 0
  · subst r
    rcases hp.eq_or_lt with rfl | hp
    · norm_num
    · simp [(sub_pos.2 hp).ne']
  have hr0 : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
  have hpow : r ^ (p - 4) * r ^ 2 = r ^ (p - 2) := by
    rw [← Real.rpow_two, ← Real.rpow_add hr0]
    congr 1
    ring
  calc
    _ = p * (p - 2) * (r ^ (p - 4) * r ^ 2) := by ring
    _ = _ := by rw [hpow]

private theorem riesz_second_norm {p : ℝ} (hp : 2 ≤ p) (z v w : ℂ) :
    fderiv ℝ (fderiv ℝ (fun q : ℂ => ‖q‖ ^ p)) z v w =
      p * ‖z‖ ^ (p - 2) * inner ℝ v w +
        p * (p - 2) * ‖z‖ ^ (p - 4) * inner ℝ z v * inner ℝ z w := by
  have hp1 : 1 < p := by linarith
  have hgrad : fderiv ℝ (fun q : ℂ => ‖q‖ ^ p) = rieszNormGradient p := by
    funext q
    exact fderiv_norm_rpow q hp1
  rw [hgrad, (hasFDerivAt_rieszNormGradient hp z).fderiv]
  have hreal : (rieszRealInner v) w = inner ℝ v w := rfl
  simp only [rieszNormHessian, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, hreal, innerSL_apply_apply, smul_eq_mul]

private theorem laplacian_complex_norm_rpow_riesz {p : ℝ} (hp : 2 ≤ p) (z : ℂ) :
    Laplacian.laplacian (fun q : ℂ => ‖q‖ ^ p) z = p ^ 2 * ‖z‖ ^ (p - 2) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    riesz_second_norm hp, riesz_inner_complex,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, zero_add]
  have hsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  calc
    _ = 2 * p * ‖z‖ ^ (p - 2) +
        p * (p - 2) * ‖z‖ ^ (p - 4) * (z.re ^ 2 + z.im ^ 2) := by ring
    _ = 2 * p * ‖z‖ ^ (p - 2) + p * (p - 2) * ‖z‖ ^ (p - 2) := by
      rw [hsq, riesz_rpow_quadratic hp (norm_nonneg z)]
    _ = _ := by ring

private theorem laplacian_realPart_norm_rpow_riesz {p : ℝ} (hp : 2 ≤ p) (z : ℂ) :
    Laplacian.laplacian (fun q : ℂ => ‖q.re‖ ^ p) z =
      p * (p - 1) * ‖z.re‖ ^ (p - 2) := by
  let P : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  have hnorm := contDiff_two_complex_norm_rpow_riesz hp
  have hfunc : (fun q : ℂ => ‖q.re‖ ^ p) = (fun q : ℂ => ‖q‖ ^ p) ∘ P := by
    funext q
    simp [P, Complex.norm_real]
  have hcomp := P.iteratedFDeriv_comp_right hnorm z (i := 2) (by norm_num)
  have hsecond (v w : ℂ) :
      iteratedFDeriv ℝ 2 (fun q : ℂ => ‖q.re‖ ^ p) z ![v, w] =
        fderiv ℝ (fderiv ℝ (fun q : ℂ => ‖q‖ ^ p)) (P z) (P v) (P w) := by
    rw [hfunc, hcomp]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, hsecond]
  simp only [riesz_second_norm hp, riesz_inner_complex]
  simp only [P, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
    Complex.ofRealCLM_apply, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.I_re, Complex.norm_real,
    mul_one, mul_zero, add_zero]
  have hsq : z.re ^ 2 = ‖z.re‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  calc
    _ = p * ‖z.re‖ ^ (p - 2) +
        p * (p - 2) * ‖z.re‖ ^ (p - 4) * z.re ^ 2 := by ring
    _ = p * ‖z.re‖ ^ (p - 2) + p * (p - 2) * ‖z.re‖ ^ (p - 2) := by
      rw [hsq, riesz_rpow_quadratic hp (norm_nonneg z.re)]
    _ = _ := by ring

/-- The exact value-space Laplacian in the book's auxiliary computation.
No nonvanishing restriction or exponent endpoint is dropped. -/
theorem laplacian_rieszAuxiliaryValue_eq {p : ℝ} (hp : 2 ≤ p) (z : ℂ) :
    Laplacian.laplacian (rieszAuxiliaryValue p) z =
      p ^ 2 * (‖z‖ ^ (p - 2) - ‖z.re‖ ^ (p - 2)) := by
  have hnorm := contDiff_two_complex_norm_rpow_riesz hp
  have hre : ContDiff ℝ 2 (fun q : ℂ => ‖q.re‖ ^ p) := by
    have hreal : ContDiff ℝ 2 (fun x : ℝ => ‖x‖ ^ p) := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.norm_real] using
        hnorm.comp Complex.ofRealCLM.contDiff
    exact hreal.comp Complex.reCLM.contDiff
  have hscaled : ContDiffAt ℝ 2
      ((p / (p - 1)) • (fun q : ℂ => ‖q.re‖ ^ p)) z := by
    simpa only [Pi.smul_def] using
      ((hre.const_smul (p / (p - 1))).contDiffAt (x := z))
  have hsub := (hnorm.contDiffAt (x := z)).laplacian_sub hscaled
  have hsmul := InnerProductSpace.laplacian_smul (p / (p - 1))
    (hre.contDiffAt (x := z))
  have hvalue : rieszAuxiliaryValue p =
      (fun q : ℂ => ‖q‖ ^ p) - (p / (p - 1)) • (fun q : ℂ => ‖q.re‖ ^ p) := by
    funext q
    simp only [rieszAuxiliaryValue, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hvalue, hsub, hsmul, laplacian_complex_norm_rpow_riesz hp,
    laplacian_realPart_norm_rpow_riesz hp, smul_eq_mul]
  have hm : p - 1 ≠ 0 := by linarith
  field_simp [hm]

/-- The original auxiliary function is subharmonic, including all its zeros. -/
theorem laplacian_rieszAuxiliaryValue_nonneg {p : ℝ} (hp : 2 ≤ p) (z : ℂ) :
    0 ≤ Laplacian.laplacian (rieszAuxiliaryValue p) z := by
  rw [laplacian_rieszAuxiliaryValue_eq hp]
  apply mul_nonneg (sq_nonneg p)
  apply sub_nonneg.2
  apply Real.rpow_le_rpow (norm_nonneg z.re)
  · simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm z
  · linarith

end LowDimensionalTopology.Geometry.Quasiconformal
