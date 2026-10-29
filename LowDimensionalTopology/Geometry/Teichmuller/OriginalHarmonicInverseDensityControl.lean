module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicFirstSpatialParameters
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicCompactImages
public import LowDimensionalTopology.Geometry.Teichmuller.HarmonicHyperbolicDensityVariation
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Compact control of the actual reciprocal harmonic density

Parameter Cauchy estimates control the actual first spatial derivatives.
The resulting positive Jacobian bound gives a uniform basepoint Lipschitz
estimate for the reciprocal density on each compact source set.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC

private theorem norm_sub_zero_le_of_holomorphic_bound
    {g : ℂ → ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hg : DifferentiableOn ℂ g (ball 0 δ))
    (hM : ∀ v ∈ ball 0 δ, ‖g v‖ ≤ M)
    {s : ℂ} (hs : ‖s‖ < δ / 2) :
    ‖g s - g 0‖ ≤ M / (δ / 2) * ‖s‖ := by
  have hd (w : ℂ) (hw : w ∈ ball 0 (δ / 2)) :
      ‖deriv g w‖ ≤ M / (δ / 2) := by
    have hsub : closedBall w (δ / 2) ⊆ ball 0 δ := by
      intro v hv
      rw [mem_closedBall] at hv
      rw [mem_ball] at hw ⊢
      linarith [dist_triangle v w 0]
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (hg.diffContOnCl_ball hsub)
      (fun v hv => hM v (hsub (sphere_subset_closedBall hv)))
  have hdiff (w : ℂ) (hw : w ∈ ball 0 (δ / 2)) : DifferentiableAt ℂ g w :=
    hg.differentiableAt (isOpen_ball.mem_nhds
      ((ball_subset_ball (by linarith : δ / 2 ≤ δ)) hw))
  have h := (convex_ball (0 : ℂ) (δ / 2)).norm_image_sub_le_of_norm_deriv_le
    hdiff hd (mem_ball_self (by positivity)) (mem_ball_zero_iff.mpr hs)
  simpa only [sub_zero] using h

private theorem density_norm_first_spatial_le_fderiv (f : ℂ → ℂ) (z : ℂ) :
    ‖dz f z‖ ≤ ‖fderiv ℝ f z‖ ∧ ‖dzbar f z‖ ≤ ‖fderiv ℝ f z‖ := by
  have h₁ := (fderiv ℝ f z).le_opNorm (1 : ℂ)
  have hI := (fderiv ℝ f z).le_opNorm I
  simp only [norm_one, norm_I, mul_one] at h₁ hI
  constructor
  · calc
      ‖dz f z‖ = ‖fderiv ℝ f z 1 - I * fderiv ℝ f z I‖ / 2 := by
        simp only [dz, norm_div, norm_ofNat]
      _ ≤ (‖fderiv ℝ f z 1‖ + ‖fderiv ℝ f z I‖) / 2 := by
        gcongr
        simpa only [norm_mul, norm_I, one_mul] using
          norm_sub_le (fderiv ℝ f z 1) (I * fderiv ℝ f z I)
      _ ≤ ‖fderiv ℝ f z‖ := by linarith
  · calc
      ‖dzbar f z‖ = ‖fderiv ℝ f z 1 + I * fderiv ℝ f z I‖ / 2 := by
        simp only [dzbar, norm_div, norm_ofNat]
      _ ≤ (‖fderiv ℝ f z 1‖ + ‖fderiv ℝ f z I‖) / 2 := by
        gcongr
        simpa only [norm_mul, norm_I, one_mul] using
          norm_add_le (fderiv ℝ f z 1) (I * fderiv ℝ f z I)
      _ ≤ ‖fderiv ℝ f z‖ := by linarith

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

private theorem canonicalFamily_first_spatial_compact_closeness
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (K : Set ℍ) (hK : IsCompact K) :
    ∃ ε A : ℝ, 0 < ε ∧ 0 ≤ A ∧ ∀ s : ℂ, ‖s‖ < ε → ∀ z ∈ K,
      ‖dz (canonicalFamily R p q s) z - 1‖ ≤ A * ‖s‖ ∧
        ‖dzbar (canonicalFamily R p q s) z‖ ≤ A * ‖s‖ := by
  obtain ⟨η, hη, _hC1, hfirst, hsecond, hcompact⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control R p hp q
  obtain ⟨δ, D, hδ, hδη, hD, hbound⟩ := hcompact K hK
  let f := canonicalBiparameterFamily R p q
  have hzero : f 0 0 = id := by
    simpa only [map_zero] using
      (canonicalBiparameterFamily_diagonal R p q 0).trans (canonicalFamily_zero R p q)
  have h0η : ‖(0 : ℂ)‖ < η := by simpa only [norm_zero] using hη
  have htwo (g : ℂ → ℂ → ℂ)
      (h₁ : ∀ t : ℂ, ‖t‖ < δ → DifferentiableOn ℂ (fun s => g s t) (ball 0 δ))
      (h₂ : DifferentiableOn ℂ (g 0) (ball 0 δ))
      (hM : ∀ a b : ℂ, ‖a‖ < δ → ‖b‖ < δ → ‖g a b‖ ≤ D)
      {s t : ℂ} (hs : ‖s‖ < δ / 2) (ht : ‖t‖ < δ / 2) :
      ‖g s t - g 0 0‖ ≤ D / (δ / 2) * (‖s‖ + ‖t‖) := by
    have htδ : ‖t‖ < δ := by linarith
    have h0δ : ‖(0 : ℂ)‖ < δ := by simpa only [norm_zero] using hδ
    have ha := norm_sub_zero_le_of_holomorphic_bound hδ (h₁ t htδ)
      (fun a ha => hM a t (mem_ball_zero_iff.mp ha) htδ) hs
    have hb := norm_sub_zero_le_of_holomorphic_bound hδ h₂
      (fun b hb => hM 0 b h0δ (mem_ball_zero_iff.mp hb)) ht
    calc
      ‖g s t - g 0 0‖ ≤ ‖g s t - g 0 t‖ + ‖g 0 t - g 0 0‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ D / (δ / 2) * ‖s‖ + D / (δ / 2) * ‖t‖ := add_le_add ha hb
      _ = D / (δ / 2) * (‖s‖ + ‖t‖) := by ring
  let A := D / (δ / 2) * 2
  refine ⟨δ / 2, A, by positivity, by positivity, ?_⟩
  intro s hs z hz
  have hconj : ‖conj s‖ < δ / 2 := by simpa only [norm_conj] using hs
  have hd₀ : dz (f 0 0) z = 1 := by rw [hzero]; norm_num [dz, fderiv_id]
  have hb₀ : dzbar (f 0 0) z = 0 := by rw [hzero]; norm_num [dzbar, fderiv_id]
  have hd := htwo (fun a b => dz (f a b) z)
    (fun b hb => ((hfirst b (hb.trans_le hδη) z (Or.inl z.im_pos)).1).mono
      (ball_subset_ball hδη))
    (((hsecond 0 h0η z (Or.inl z.im_pos)).1).mono (ball_subset_ball hδη))
    (fun a b ha hb => (density_norm_first_spatial_le_fderiv (f a b) z).1.trans
      (hbound a b ha hb z hz)) hs hconj
  have hb := htwo (fun a b => dzbar (f a b) z)
    (fun b hb => ((hfirst b (hb.trans_le hδη) z (Or.inl z.im_pos)).2).mono
      (ball_subset_ball hδη))
    (((hsecond 0 h0η z (Or.inl z.im_pos)).2).mono (ball_subset_ball hδη))
    (fun a b ha hb => (density_norm_first_spatial_le_fderiv (f a b) z).2.trans
      (hbound a b ha hb z hz)) hs hconj
  rw [hd₀] at hd
  rw [hb₀, sub_zero] at hb
  have hdiag : f s (conj s) = canonicalFamily R p q s :=
    canonicalBiparameterFamily_diagonal R p q s
  rw [hdiag] at hd hb
  constructor
  · simpa only [norm_conj, ← two_mul, A, mul_assoc] using hd
  · simpa only [norm_conj, ← two_mul, A, mul_assoc] using hb

/-- The actual reciprocal transported density has one basepoint Lipschitz
bound on each compact upper-half-plane source set. -/
theorem canonicalFamily_inverse_density_compact_lipschitz
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (K : Set ℍ) (hK : IsCompact K) :
    ∃ ε L : ℝ, 0 < ε ∧ 0 ≤ L ∧
      ∀ s : ℂ, ‖s‖ < ε → ∀ z ∈ K,
        ‖((transportedHyperbolicDensity R p q s z)⁻¹ : ℂ) -
          (z.im ^ 2 : ℂ)‖ ≤ L * ‖s‖ := by
  obtain ⟨ε₁, A, hε₁, _hA, hjetBound⟩ :=
    canonicalFamily_first_spatial_compact_closeness R p hp q K hK
  obtain ⟨ε₂, hε₂, _hqc, hlinear⟩ := canonicalBiparameterFamily_bounded_closeness R p hp q
  obtain ⟨B₀, hB₀⟩ := hK.bddAbove_image UpperHalfPlane.continuous_coe.norm.continuousOn
  let H : ℝ := max B₀ 1
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hnorm (z : ℍ) (hz : z ∈ K) : ‖(z : ℂ)‖ ≤ H :=
    (hB₀ (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  obtain ⟨C, _hC, hclose⟩ := hlinear H hH
  let L₀ : ℝ := max 1 (max A (2 * C))
  have hL₀ : 0 < L₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hAL : A ≤ L₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hCL : 2 * C ≤ L₀ := (le_max_right _ _).trans (le_max_right _ _)
  let ε : ℝ := min ε₁ (min ε₂ (1 / (4 * L₀)))
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ (by positivity))
  let L : ℝ := L₀ * (6 * H ^ 2 + 4 * H + 2)
  refine ⟨ε, L, hε, by dsimp only [L]; positivity, ?_⟩
  intro s hs z hz
  have hs₁ : ‖s‖ < ε₁ := hs.trans_le (min_le_left _ _)
  have hs₂ : ‖s‖ < ε₂ := hs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsL : ‖s‖ * (4 * L₀) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < 4 * L₀)).mp
      (hs.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hsmall : L₀ * ‖s‖ ≤ 1 / 4 := by nlinarith
  let f := canonicalFamily R p q s
  let a := dz f (z : ℂ)
  let b := dzbar f (z : ℂ)
  let y : ℝ := (z : ℂ).im
  let Y : ℝ := (f z).im
  let J : ℝ := jacobian f z
  have ha : ‖a - 1‖ ≤ L₀ * ‖s‖ :=
    (hjetBound s hs₁ z hz).1.trans (mul_le_mul_of_nonneg_right hAL (norm_nonneg _))
  have hbar : ‖b‖ ≤ L₀ * ‖s‖ :=
    (hjetBound s hs₁ z hz).2.trans (mul_le_mul_of_nonneg_right hAL (norm_nonneg _))
  have hfc : ‖f z - (z : ℂ)‖ ≤ (2 * C) * ‖s‖ := by
    have h := hclose s (conj s) hs₂ (by simpa only [norm_conj] using hs₂) z (hnorm z hz)
    calc
      ‖f z - (z : ℂ)‖ ≤ C * (‖s‖ + ‖conj s‖) := by
        simpa only [canonicalBiparameterFamily_diagonal] using h
      _ = (2 * C) * ‖s‖ := by rw [norm_conj]; ring
  have hY : |Y - y| ≤ L₀ * ‖s‖ := by
    have h := Complex.abs_im_le_norm (f z - (z : ℂ))
    rw [Complex.sub_im] at h
    exact h.trans (hfc.trans (mul_le_mul_of_nonneg_right hCL (norm_nonneg _)))
  have hy : |y| ≤ H := (Complex.abs_im_le_norm (z : ℂ)).trans (hnorm z hz)
  have hna : |‖a‖ - 1| ≤ L₀ * ‖s‖ := by
    simpa only [norm_one] using (abs_norm_sub_norm_le a (1 : ℂ)).trans ha
  have hal : (3 / 4 : ℝ) ≤ ‖a‖ := by
    have h := (abs_le.mp hna).1
    linarith
  have hau : ‖a‖ ≤ (5 / 4 : ℝ) := by
    have h := (abs_le.mp hna).2
    linarith
  have hbu : ‖b‖ ≤ (1 / 4 : ℝ) := hbar.trans hsmall
  have hJlower : (1 / 2 : ℝ) ≤ J := by
    change (1 / 2 : ℝ) ≤ ‖a‖ ^ 2 - ‖b‖ ^ 2
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hal 2,
      pow_le_pow_left₀ (norm_nonneg b) hbu 2]
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hJlower
  have hJne : J ≠ 0 := hJpos.ne'
  have hja : |‖a‖ ^ 2 - 1| ≤ (9 / 4 : ℝ) * (L₀ * ‖s‖) := by
    calc
      |‖a‖ ^ 2 - 1| = |‖a‖ - 1| * (‖a‖ + 1) := by
        rw [show ‖a‖ ^ 2 - 1 = (‖a‖ - 1) * (‖a‖ + 1) by ring, abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ ‖a‖ + 1)]
      _ ≤ (L₀ * ‖s‖) * (9 / 4) :=
        mul_le_mul hna (by linarith) (by positivity) (by positivity)
      _ = (9 / 4) * (L₀ * ‖s‖) := by ring
  have hjb : ‖b‖ ^ 2 ≤ (1 / 4 : ℝ) * (L₀ * ‖s‖) := by
    simpa only [pow_two] using mul_le_mul hbu hbar (norm_nonneg b) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hJdiff : |J - 1| ≤ 3 * L₀ * ‖s‖ := by
    have heq : J - 1 = (‖a‖ ^ 2 - 1) - ‖b‖ ^ 2 := by dsimp only [J, jacobian, a, b]; ring
    rw [heq]
    have h : |(‖a‖ ^ 2 - 1) - ‖b‖ ^ 2| ≤ |‖a‖ ^ 2 - 1| + |‖b‖ ^ 2| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (‖a‖ ^ 2 - 1) (‖b‖ ^ 2)
    rw [abs_of_nonneg (sq_nonneg ‖b‖)] at h
    nlinarith [mul_nonneg hL₀.le (norm_nonneg s)]
  have hYabs : |Y| ≤ H + 1 / 4 := by
    have h : |Y| ≤ |Y - y| + |y| := by
      simpa only [sub_add_cancel] using abs_add_le (Y - y) y
    linarith
  have hYsum : |Y + y| ≤ 2 * H + 1 := by
    have h := abs_add_le Y y
    linarith
  have hYsq : |Y ^ 2 - y ^ 2| ≤ (2 * H + 1) * L₀ * ‖s‖ := by
    calc
      |Y ^ 2 - y ^ 2| = |Y - y| * |Y + y| := by
        rw [show Y ^ 2 - y ^ 2 = (Y - y) * (Y + y) by ring, abs_mul]
      _ ≤ (L₀ * ‖s‖) * (2 * H + 1) :=
        mul_le_mul hY hYsum (abs_nonneg _) (by positivity)
      _ = (2 * H + 1) * L₀ * ‖s‖ := by ring
  have hinv : |J⁻¹| ≤ 2 := by
    rw [abs_of_pos (inv_pos.mpr hJpos), inv_eq_one_div]
    exact (div_le_iff₀ hJpos).mpr (by linarith)
  have hinvdiff : |J⁻¹ - 1| ≤ 6 * L₀ * ‖s‖ := by
    have heq : J⁻¹ - 1 = (1 - J) * J⁻¹ := by field_simp [hJne]
    rw [heq, abs_mul]
    calc
      |1 - J| * |J⁻¹| ≤ (3 * L₀ * ‖s‖) * 2 :=
        mul_le_mul (by simpa only [abs_sub_comm] using hJdiff) hinv
          (abs_nonneg _) (by positivity)
      _ = 6 * L₀ * ‖s‖ := by ring
  have hy2 : y ^ 2 ≤ H ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hrho : (transportedHyperbolicDensity R p q s z)⁻¹ = Y ^ 2 / J := by
    dsimp only [transportedHyperbolicDensity, Y, J, f]
    rw [inv_div]
  have hreal : |(transportedHyperbolicDensity R p q s z)⁻¹ - y ^ 2| ≤ L * ‖s‖ := by
    rw [hrho]
    have heq : Y ^ 2 / J - y ^ 2 =
        (Y ^ 2 - y ^ 2) * J⁻¹ + y ^ 2 * (J⁻¹ - 1) := by field_simp [hJne]; ring
    rw [heq]
    calc
      |(Y ^ 2 - y ^ 2) * J⁻¹ + y ^ 2 * (J⁻¹ - 1)| ≤
          |(Y ^ 2 - y ^ 2) * J⁻¹| + |y ^ 2 * (J⁻¹ - 1)| := abs_add_le _ _
      _ = |Y ^ 2 - y ^ 2| * |J⁻¹| + y ^ 2 * |J⁻¹ - 1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg y)]
      _ ≤ ((2 * H + 1) * L₀ * ‖s‖) * 2 + H ^ 2 * (6 * L₀ * ‖s‖) :=
        add_le_add (mul_le_mul hYsq hinv (abs_nonneg _) (by positivity))
          (mul_le_mul hy2 hinvdiff (abs_nonneg _) (sq_nonneg H))
      _ = L * ‖s‖ := by dsimp only [L]; ring
  simpa only [y, UpperHalfPlane.coe_im, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hreal

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
