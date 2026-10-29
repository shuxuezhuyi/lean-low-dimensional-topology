module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicFirstSpatialParameters
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The actual passive regular Cauchy kernel in planar L²

The difference between the pulled conformal square kernel and the original
square kernel has a uniform local bound after its constant and linear terms
cancel. Actual image separation and ordinary area substitution control its
far part. The diagonal is assigned zero by total division; this point value
does not claim to be the removable limiting value.
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

private theorem actual_passive_conformal_data
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

private theorem regular_kernel_dslope_identity
    {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U)
    (hyx : y ≠ x) (hg : dslope F x y ≠ 0) :
    deriv F x * deriv F y / (F x - F y) ^ 2 - 1 / (x - y) ^ 2 =
      (deriv F x * deriv (dslope (dslope F x) x) y -
        (dslope (dslope F x) x y) ^ 2) / (dslope F x y) ^ 2 := by
  let g := dslope F x
  let h := dslope g x
  have hgd : DifferentiableOn ℂ g U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hx)).2 hF
  have hhd : DifferentiableOn ℂ h U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hx)).2 hgd
  have hFid (w : ℂ) : (w - x) * g w + F x = F w := by
    rw [← smul_eq_mul, sub_smul_dslope]
    exact sub_add_cancel _ _
  have hgid (w : ℂ) : (w - x) * h w + g x = g w := by
    rw [← smul_eq_mul, sub_smul_dslope]
    exact sub_add_cancel _ _
  have hdg : DifferentiableAt ℂ g y := hgd.differentiableAt (hU.mem_nhds hy)
  have hdh : DifferentiableAt ℂ h y := hhd.differentiableAt (hU.mem_nhds hy)
  have hFy : deriv F y = g y + (y - x) * deriv g y := by
    have hd := (((hasDerivAt_id y).sub_const x).fun_mul hdg.hasDerivAt).add_const (F x)
    simp only [id_eq] at hd
    rw [funext hFid] at hd
    simpa only [one_mul] using hd.deriv
  have hgy : deriv g y = h y + (y - x) * deriv h y := by
    have hd := (((hasDerivAt_id y).sub_const x).fun_mul hdh.hasDerivAt).add_const (g x)
    simp only [id_eq] at hd
    rw [funext hgid] at hd
    simpa only [one_mul] using hd.deriv
  have hgx : g x = deriv F x := dslope_same F x
  have hfxy : F x - F y = -(y - x) * g y := by
    calc
      F x - F y = F x - ((y - x) * g y + F x) := by rw [hFid]
      _ = -(y - x) * g y := by ring
  change deriv F x * deriv F y / (F x - F y) ^ 2 - 1 / (x - y) ^ 2 =
    (deriv F x * deriv h y - h y ^ 2) / g y ^ 2
  rw [← hgx, hFy, hgy, hfxy, show x - y = -(y - x) by ring]
  have hg' : g y ≠ 0 := hg
  field_simp [sub_ne_zero.mpr hyx, hg']
  simp only [← hgid y]
  ring

private theorem regular_kernel_bound_of_dslope
    {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U)
    (hyx : y ≠ x) {G H D : ℝ}
    (hg : 1 / 2 ≤ ‖dslope F x y‖) (hG : ‖deriv F x‖ ≤ G)
    (hH : ‖dslope (dslope F x) x y‖ ≤ H)
    (hD : ‖deriv (dslope (dslope F x) x) y‖ ≤ D) :
    ‖deriv F x * deriv F y / (F x - F y) ^ 2 - 1 / (x - y) ^ 2‖ ≤
      4 * (G * D + H ^ 2) := by
  have hgpos : 0 < ‖dslope F x y‖ := lt_of_lt_of_le (by norm_num) hg
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  have hH0 : 0 ≤ H := (norm_nonneg _).trans hH
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hD
  have hsq : (1 / 4 : ℝ) ≤ ‖dslope F x y‖ ^ 2 := by nlinarith
  rw [regular_kernel_dslope_identity hU hF hx hy hyx (norm_pos_iff.mp hgpos),
    norm_div, norm_pow]
  apply (div_le_iff₀ (pow_pos hgpos 2)).2
  calc
    ‖deriv F x * deriv (dslope (dslope F x) x) y -
        dslope (dslope F x) x y ^ 2‖ ≤
      ‖deriv F x‖ * ‖deriv (dslope (dslope F x) x) y‖ +
        ‖dslope (dslope F x) x y‖ ^ 2 := by
      calc
        _ ≤ ‖deriv F x * deriv (dslope (dslope F x) x) y‖ +
            ‖dslope (dslope F x) x y ^ 2‖ := norm_sub_le _ _
        _ = _ := by rw [norm_mul, Complex.norm_pow]
    _ ≤ G * D + H ^ 2 := by gcongr
    _ ≤ 4 * (G * D + H ^ 2) * ‖dslope F x y‖ ^ 2 := by
      have hnonneg : 0 ≤ G * D + H ^ 2 := by positivity
      nlinarith

private theorem actual_passive_regular_kernel_local_bound
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : ℍ) :
    ∃ ε r C : ℝ, 0 < ε ∧ 0 < r ∧ 0 ≤ C ∧ ball (x : ℂ) r ⊆ upperHalf ∧
      ∀ t : ℂ, ‖t‖ < ε → ∀ y ∈ ball (x : ℂ) r,
        let F := canonicalBiparameterFamily R p q 0 t
        ‖deriv F x * deriv F y / (F x - F y) ^ 2 - 1 / ((x : ℂ) - y) ^ 2‖ ≤ C := by
  obtain ⟨εQ, hεQ, hqc⟩ := actual_passive_conformal_data R p hp q
  obtain ⟨εP, hεP, _, _, hparam, _⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control R p hp q
  let F := fun t => canonicalBiparameterFamily R p q 0 t
  have hF0 : F 0 = id := by
    simpa only [F, map_zero] using
      (canonicalBiparameterFamily_diagonal R p q 0).trans (canonicalFamily_zero R p q)
  have hc0 : dz (F 0) x = 1 := by
    rw [hF0, dz_eq_deriv differentiableAt_id, deriv_id]
  have hc : ContinuousAt (fun t : ℂ => dz (F t) x) 0 :=
    ((hparam 0 (by simpa only [norm_zero] using hεP) x (Or.inl x.im_pos)).1.differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hεP))).continuousAt
  have hnear : ∀ᶠ t : ℂ in 𝓝 0, dz (F t) x ∈ ball (1 : ℂ) (1 / 4) :=
    hc.eventually_mem (by rw [hc0]; exact ball_mem_nhds _ (by norm_num))
  obtain ⟨τ, hτ, hτnear⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨ρ, hρ, hρH⟩ := Metric.isOpen_iff.mp isOpen_upperHalf (x : ℂ) x.im_pos
  let ε := min εQ (min εP τ)
  have hε : 0 < ε := lt_min hεQ (lt_min hεP hτ)
  have heQ : ε ≤ εQ := min_le_left _ _
  have heτ : ε ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  have hdata (t : ℂ) (ht : ‖t‖ < ε) :=
    hqc t (mem_ball_zero_iff.mpr (ht.trans_le heQ))
  let T := ‖(x : ℂ)‖ + ρ + 1
  have hT : 0 < T := by dsimp only [T]; positivity
  let M := lambdaInv (3 * quadLambda T)
  have hM (t : ℂ) (ht : ‖t‖ < ε) (y : ℂ) (hy : y ∈ ball (x : ℂ) ρ) :
      ‖F t y‖ ≤ M := by
    have hyT : ‖y‖ ≤ T := by
      have hd : ‖y - (x : ℂ)‖ < ρ := by simpa only [mem_ball, dist_eq_norm] using hy
      have hn := norm_sub_norm_le y (x : ℂ)
      dsimp only [T]
      linarith
    exact UniversalTeichmuller.ut2_nb_upper (hdata t ht).1 hT hyT
  have hzε : ‖(0 : ℂ)‖ < ε := by simpa only [norm_zero] using hε
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 hzε x (mem_ball_self hρ))
  let G := 2 * M / ρ
  let H := 2 * G / ρ
  let D := 4 * H / ρ
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  let g := fun t => dslope (F t) (x : ℂ)
  let h := fun t => dslope (g t) (x : ℂ)
  have hFd (t : ℂ) (ht : ‖t‖ < ε) : DifferentiableOn ℂ (F t) (ball (x : ℂ) ρ) :=
    (hdata t ht).2.mono hρH
  have hgd (t : ℂ) (ht : ‖t‖ < ε) : DifferentiableOn ℂ (g t) (ball (x : ℂ) ρ) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds _ hρ)).2 (hFd t ht)
  have hhd (t : ℂ) (ht : ‖t‖ < ε) : DifferentiableOn ℂ (h t) (ball (x : ℂ) ρ) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds _ hρ)).2 (hgd t ht)
  have hgnorm (t : ℂ) (ht : ‖t‖ < ε) (y : ℂ) (hy : y ∈ ball (x : ℂ) ρ) :
      ‖g t y‖ ≤ G := by
    apply Complex.norm_dslope_le_div_of_mapsTo_ball (hFd t ht) ?_ hy
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    simpa only [two_mul] using
      (norm_sub_le _ _).trans (add_le_add (hM t ht w hw) (hM t ht x (mem_ball_self hρ)))
  have hhnorm (t : ℂ) (ht : ‖t‖ < ε) (y : ℂ) (hy : y ∈ ball (x : ℂ) ρ) :
      ‖h t y‖ ≤ H := by
    apply Complex.norm_dslope_le_div_of_mapsTo_ball (hgd t ht) ?_ hy
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    simpa only [two_mul] using (norm_sub_le _ _).trans
      (add_le_add (hgnorm t ht w hw) (hgnorm t ht x (mem_ball_self hρ)))
  have hdnorm (t : ℂ) (ht : ‖t‖ < ε) (y : ℂ) (hy : y ∈ ball (x : ℂ) (ρ / 2)) :
      ‖deriv (h t) y‖ ≤ D := by
    have hsub : ball y (ρ / 2) ⊆ ball (x : ℂ) ρ := by
      intro w hw
      rw [mem_ball] at hw hy ⊢
      exact (dist_triangle w y x).trans_lt (by linarith)
    have hyρ : y ∈ ball (x : ℂ) ρ :=
      ball_subset_ball (by linarith) hy
    calc
      ‖deriv (h t) y‖ ≤ (2 * H) / (ρ / 2) :=
        Complex.norm_deriv_le_div_of_mapsTo_ball ((hhd t ht).mono hsub) (by
          intro w hw
          rw [mem_closedBall, dist_eq_norm]
          simpa only [two_mul] using (norm_sub_le _ _).trans
            (add_le_add (hhnorm t ht w (hsub hw)) (hhnorm t ht y hyρ))) (by linarith)
      _ = D := by dsimp only [D]; ring
  let r := min (ρ / 2) (1 / (4 * (H + 1)))
  have hr : 0 < r := lt_min (by linarith) (by positivity)
  let C := 4 * (G * D + H ^ 2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨ε, r, C, hε, hr, hC,
    (ball_subset_ball ((min_le_left _ _).trans (by linarith))).trans hρH, ?_⟩
  intro t ht y hy
  dsimp only
  have hyhalf : y ∈ ball (x : ℂ) (ρ / 2) := ball_subset_ball (min_le_left _ _) hy
  have hyρ : y ∈ ball (x : ℂ) ρ := ball_subset_ball (by linarith) hyhalf
  by_cases hyx : y = (x : ℂ)
  · subst y
    simpa only [sub_self, zero_pow two_ne_zero, div_zero, norm_zero] using hC
  have hdiff : ‖g t y - g t x‖ ≤ 1 / 4 := by
    have hsmall : ‖y - (x : ℂ)‖ < 1 / (4 * (H + 1)) :=
      (mem_ball_iff_norm.mp hy).trans_le (min_le_right _ _)
    have hprod : ‖y - (x : ℂ)‖ * H ≤ 1 / 4 := by
      have hs := (lt_div_iff₀ (by positivity : 0 < 4 * (H + 1))).mp hsmall
      nlinarith [norm_nonneg (y - (x : ℂ))]
    calc
      ‖g t y - g t x‖ = ‖y - (x : ℂ)‖ * ‖h t y‖ := by
        rw [← sub_smul_dslope (g t) (x : ℂ) y, norm_smul]
      _ ≤ ‖y - (x : ℂ)‖ * H :=
        mul_le_mul_of_nonneg_left (hhnorm t ht y hyρ) (norm_nonneg _)
      _ ≤ 1 / 4 := hprod
  have hcenter : ‖g t x - 1‖ < 1 / 4 := by
    have hn := hτnear (mem_ball_zero_iff.mpr (ht.trans_le heτ))
    change ‖dslope (F t) (x : ℂ) x - 1‖ < 1 / 4
    rw [dslope_same, ← dz_eq_deriv
      ((hdata t ht).2.differentiableAt (isOpen_upperHalf.mem_nhds x.im_pos))]
    simpa only [Set.mem_ofPred_eq, F, mem_ball, dist_eq_norm] using hn
  have hglower : 1 / 2 ≤ ‖g t y‖ := by
    have hclose : ‖g t y - 1‖ ≤ 1 / 2 :=
      (norm_sub_le_norm_sub_add_norm_sub (g t y) (g t x) 1).trans (by linarith)
    have hn := norm_sub_norm_le (1 : ℂ) (g t y)
    rw [norm_one, norm_sub_rev] at hn
    linarith
  exact regular_kernel_bound_of_dslope isOpen_ball (hFd t ht)
    (mem_ball_self hρ) hyρ hyx hglower
    (by simpa only [g, dslope_same] using hgnorm t ht x (mem_ball_self hρ))
    (hhnorm t ht y hyρ) (hdnorm t ht y hyhalf)

private theorem actual_passive_regular_kernel_far_separation
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ ε d : ℝ, 0 < ε ∧ 0 < d ∧ ∀ t : ℂ, ‖t‖ < ε → ∀ y : ℂ,
      r ≤ ‖y - x‖ →
        d ≤ ‖canonicalBiparameterFamily R p q 0 t y -
          canonicalBiparameterFamily R p q 0 t x‖ := by
  obtain ⟨E, hE, hsharp, hlinear⟩ :=
    canonicalBiparameterFamily_bounded_closeness R p hp q
  let U := ‖x‖ + r + 1
  have hU : 0 < U := by dsimp only [U]; positivity
  let L := lambdaInv (3 * quadLambda U)
  let T := max ‖x‖ (max L 1)
  have hT : 0 < T := zero_lt_one.trans_le ((le_max_right _ _).trans (le_max_right _ _))
  have hxT : ‖x‖ ≤ T := le_max_left _ _
  have hLT : L ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨C, hC, hlin⟩ := hlinear T hT
  let ε := min E (r / (16 * C))
  have hε : 0 < ε := lt_min hE (by positivity)
  refine ⟨ε, r / 4, hε, by positivity, ?_⟩
  intro t ht y hy
  let F := canonicalBiparameterFamily R p q 0 t
  have htE : ‖t‖ < E := ht.trans_le (min_le_left _ _)
  have hzE : ‖(0 : ℂ)‖ < E := by simpa only [norm_zero] using hE
  have hqc : IsKQCNormalizedPlane F 3 := hsharp 0 t hzE htE
  have hsmall : C * ‖t‖ < r / 16 := by
    have hs := (lt_div_iff₀ (by positivity : 0 < 16 * C)).mp
      (ht.trans_le (min_le_right _ _))
    nlinarith
  have hclose (w : ℂ) (hw : ‖w‖ ≤ T) : ‖F w - w‖ < r / 16 := by
    have hb : ‖F w - w‖ ≤ C * ‖t‖ := by
      simpa only [F, norm_zero, zero_add] using hlin 0 t hzE htE w hw
    exact hb.trans_lt hsmall
  have hxclose := hclose x hxT
  by_contra hsep
  have hnear : ‖F y - F x‖ < r / 4 := lt_of_not_ge hsep
  have hFy : ‖F y‖ ≤ U := by
    have hxbound := norm_sub_norm_le (F x) x
    have hybound := norm_sub_norm_le (F y) (F x)
    dsimp only [U]
    linarith
  have hyT : ‖y‖ ≤ T :=
    (UniversalTeichmuller.ut2_nb_lower hqc hU hFy).trans hLT
  have hyclose := hclose y hyT
  have htri := norm_sub_le_norm_sub_add_norm_sub y (F y) x
  have htri' := norm_sub_le_norm_sub_add_norm_sub (F y) (F x) x
  rw [norm_sub_rev y (F y)] at htri
  linarith

private theorem separated_square_kernel_norm_sq_le_profile
    {c w : ℂ} {d B : ℝ} (hd : 0 < d) (hc : ‖c‖ ≤ B)
    (hgap : d ≤ ‖w - c‖) :
    ‖(1 : ℂ) / (w - c) ^ 2‖ ^ 2 ≤
      ((1 + B + d) / d) ^ 4 * ((1 + ‖w‖) ^ 3)⁻¹ := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hc
  have hpos : 0 < ‖w - c‖ := hd.trans_le hgap
  have hs1 : 0 < 1 + ‖w‖ := by positivity
  have htriangle := norm_sub_norm_le w c
  have hsep : d * (1 + ‖w‖) ≤ (1 + B + d) * ‖w - c‖ := by
    have h₁ : d * ‖w‖ ≤ d * (‖w - c‖ + B) :=
      mul_le_mul_of_nonneg_left (by linarith) hd.le
    have h₂ : d * (1 + B) ≤ ‖w - c‖ * (1 + B) :=
      mul_le_mul_of_nonneg_right hgap (by positivity)
    nlinarith
  have hkey : (1 + ‖w‖) * ‖w - c‖⁻¹ ≤ (1 + B + d) / d := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ hpos hd]
    nlinarith
  have hinv : ‖(w - c)⁻¹‖ ≤ (1 + B + d) / d * (1 + ‖w‖)⁻¹ := by
    rw [norm_inv]
    calc
      ‖w - c‖⁻¹ = (1 + ‖w‖)⁻¹ * ((1 + ‖w‖) * ‖w - c‖⁻¹) := by field_simp
      _ ≤ (1 + ‖w‖)⁻¹ * ((1 + B + d) / d) := by gcongr
      _ = (1 + B + d) / d * (1 + ‖w‖)⁻¹ := by ring
  have hi0 : 0 ≤ (1 + ‖w‖)⁻¹ := by positivity
  have hi1 : (1 + ‖w‖)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by linarith [norm_nonneg w])
  calc
    ‖(1 : ℂ) / (w - c) ^ 2‖ ^ 2 = ‖(w - c)⁻¹‖ ^ 4 := by
      rw [one_div, ← inv_pow, norm_pow, ← pow_mul]
    _ ≤ ((1 + B + d) / d * (1 + ‖w‖)⁻¹) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) hinv 4
    _ = ((1 + B + d) / d) ^ 4 * (1 + ‖w‖)⁻¹ ^ 4 := by rw [mul_pow]
    _ ≤ ((1 + B + d) / d) ^ 4 * (1 + ‖w‖)⁻¹ ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hi0 hi1 (by norm_num)) (by positivity)
    _ = ((1 + B + d) / d) ^ 4 * ((1 + ‖w‖) ^ 3)⁻¹ := by rw [inv_pow]

private theorem actual_passive_pulled_square_far_integrable
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ t : ℂ, ‖t‖ < ε →
      let F := canonicalBiparameterFamily R p q 0 t
      IntegrableOn (fun y : ℂ => ‖deriv F y / (F y - F x) ^ 2‖ ^ 2)
        (upperHalf \ closedBall x r) ∧
      (∫ y : ℂ in upperHalf \ closedBall x r,
        ‖deriv F y / (F y - F x) ^ 2‖ ^ 2) ≤ C := by
  obtain ⟨E₁, d, hE₁, hd, hgap⟩ :=
    actual_passive_regular_kernel_far_separation R p hp q x hr
  obtain ⟨E₂, hE₂, hdata⟩ := actual_passive_conformal_data R p hp q
  let ε := min E₁ E₂
  have hε : 0 < ε := lt_min hE₁ hE₂
  let B := max (lambdaInv (3 * quadLambda (‖x‖ + 1))) 1
  let A := (1 + B + d) / d
  let C := A ^ 4 * ∫ w : ℂ, ((1 + ‖w‖) ^ 3)⁻¹
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by positivity) (integral_nonneg (fun w : ℂ => by positivity))
  refine ⟨ε, C, hε, hC, ?_⟩
  intro t ht
  dsimp only
  let F := canonicalBiparameterFamily R p q 0 t
  let U := upperHalf \ closedBall x r
  have hU : IsOpen U := isOpen_upperHalf.sdiff isClosed_closedBall
  obtain ⟨hqc, hhol⟩ := hdata t
    (mem_ball_zero_iff.mpr (ht.trans_le (min_le_right _ _)))
  have hFd : DifferentiableOn ℂ F U := hhol.mono sdiff_subset
  have hinj : InjOn F U := hqc.1.2.2.1.2.1.mono (subset_univ _)
  have himage : IsOpen (F '' U) := isOpen_image_of_isKQC
    (ac_t_isKQC_restrict hqc.1 hU (subset_univ _))
  have hcenter : ‖F x‖ ≤ B :=
    (UniversalTeichmuller.ut2_nb_upper hqc (by positivity : 0 < ‖x‖ + 1)
      (by linarith : ‖x‖ ≤ ‖x‖ + 1)).trans (le_max_left _ _)
  let J := fun w : ℂ => ‖(1 : ℂ) / (w - F x) ^ 2‖ ^ 2
  have hJm : Measurable J := by dsimp only [J]; fun_prop
  have hprofile : Integrable (fun w : ℂ => A ^ 4 * ((1 + ‖w‖) ^ 3)⁻¹) volume :=
    b36_p_profile_integrable.const_mul _
  have hbound (w : ℂ) (hw : w ∈ F '' U) :
      J w ≤ A ^ 4 * ((1 + ‖w‖) ^ 3)⁻¹ := by
    obtain ⟨y, hy, rfl⟩ := hw
    have hyr : r < ‖y - x‖ := by
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hy.2
    exact separated_square_kernel_norm_sq_le_profile hd hcenter
      (hgap t (ht.trans_le (min_le_left _ _)) y hyr.le)
  have hJint : IntegrableOn J (F '' U) volume := by
    apply hprofile.integrableOn.mono' hJm.aestronglyMeasurable
    exact ae_restrict_of_forall_mem himage.measurableSet (fun w hw => by
      simpa only [J, Real.norm_of_nonneg (sq_nonneg _)] using hbound w hw)
  have hweight (y : ℂ) : ‖deriv F y‖ ^ 2 • J (F y) =
      ‖deriv F y / (F y - F x) ^ 2‖ ^ 2 := by
    simp only [J, smul_eq_mul, norm_div, norm_pow, norm_one, div_pow]
    ring
  have hPull := (ahP_integrableOn_image hU hFd hinj J).1 hJint
  have hPull' : IntegrableOn (fun y : ℂ =>
      ‖deriv F y / (F y - F x) ^ 2‖ ^ 2) U volume :=
    hPull.congr_fun (fun y _ => hweight y) hU.measurableSet
  refine ⟨hPull', ?_⟩
  calc
    (∫ y : ℂ in U, ‖deriv F y / (F y - F x) ^ 2‖ ^ 2) =
        ∫ y : ℂ in U, ‖deriv F y‖ ^ 2 • J (F y) :=
      setIntegral_congr_fun hU.measurableSet (fun y _ => (hweight y).symm)
    _ = ∫ w : ℂ in F '' U, J w := (ahP_integral_image hU hFd hinj J).symm
    _ ≤ ∫ w : ℂ in F '' U, A ^ 4 * ((1 + ‖w‖) ^ 3)⁻¹ :=
      integral_mono_ae hJint hprofile.integrableOn
        (ae_restrict_of_forall_mem himage.measurableSet hbound)
    _ ≤ ∫ w : ℂ, A ^ 4 * ((1 + ‖w‖) ^ 3)⁻¹ :=
      setIntegral_le_integral hprofile (Eventually.of_forall (fun w => by positivity))
    _ = C := integral_const_mul _ _

private theorem norm_dz_le_real_derivative (F : ℂ → ℂ) (x : ℂ) :
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

private theorem actual_passive_regular_kernel_l2
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : ℍ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ t : ℂ, ‖t‖ < ε →
      let F := canonicalBiparameterFamily R p q 0 t
      let S := fun y : ℂ => dz F x * dz F y / (F x - F y) ^ 2 -
        1 / ((x : ℂ) - y) ^ 2
      MemLp (upperHalf.indicator S) 2 (volume : Measure ℂ) ∧
        (∫ y : ℂ, ‖upperHalf.indicator S y‖ ^ 2) ≤ C := by
  classical
  obtain ⟨E₁, r, C₁, hE₁, hr, hC₁, hrH, hlocal⟩ :=
    actual_passive_regular_kernel_local_bound R p hp q x
  obtain ⟨E₂, C₂, hE₂, hC₂, hpull⟩ :=
    actual_passive_pulled_square_far_integrable R p hp q (x : ℂ) (half_pos hr)
  obtain ⟨E₃, hE₃, hdata⟩ := actual_passive_conformal_data R p hp q
  obtain ⟨E₄, hE₄, _, _, _, hcompact⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control R p hp q
  obtain ⟨δ, D, hδ, _, hD, hderiv⟩ := hcompact {x} isCompact_singleton
  let ε := min E₁ (min E₂ (min E₃ δ))
  have hε : 0 < ε := lt_min hE₁ (lt_min hE₂ (lt_min hE₃ hδ))
  have he₁ : ε ≤ E₁ := min_le_left _ _
  have he₂ : ε ≤ E₂ := (min_le_right _ _).trans (min_le_left _ _)
  have he₃ : ε ≤ E₃ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have heδ : ε ≤ δ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  let U := upperHalf \ closedBall (x : ℂ) (r / 2)
  have hU : IsOpen U := isOpen_upperHalf.sdiff isClosed_closedBall
  let N := (ball (x : ℂ) r).indicator (fun _ : ℂ => C₁ ^ 2)
  have hN0 (y : ℂ) : 0 ≤ N y := indicator_nonneg (fun _ _ => sq_nonneg _) y
  have hballfinite : volume (ball (x : ℂ) r) ≠ ⊤ :=
    measure_ball_ne_top
  have hNi : Integrable N (volume : Measure ℂ) :=
    (integrableOn_const hballfinite).integrable_indicator isOpen_ball.measurableSet
  let A := (1 + ‖(x : ℂ)‖ + r / 2) / (r / 2)
  let C₀ := A ^ 4 * ∫ y : ℂ, ((1 + ‖y‖) ^ 3)⁻¹
  have hC₀ : 0 ≤ C₀ := by
    dsimp only [C₀]
    exact mul_nonneg (by positivity) (integral_nonneg (fun y : ℂ => by positivity))
  let C := (∫ y : ℂ, N y) + 2 * D ^ 2 * C₂ + 2 * C₀
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (add_nonneg (integral_nonneg hN0) (by positivity)) (by positivity)
  refine ⟨ε, C, hε, hC, ?_⟩
  intro t ht
  dsimp only
  let F := canonicalBiparameterFamily R p q 0 t
  let P := fun y : ℂ => dz F x * dz F y / (F x - F y) ^ 2
  let k := fun y : ℂ => (1 : ℂ) / ((x : ℂ) - y) ^ 2
  let S := fun y : ℂ => P y - k y
  let Z := upperHalf.indicator S
  obtain ⟨hqc, hhol⟩ := hdata t (mem_ball_zero_iff.mpr (ht.trans_le he₃))
  have hFm : Measurable F := (continuousOn_univ.mp hqc.1.2.2.1.1).measurable
  have hPm : Measurable P :=
    (measurable_const.fun_mul (measurable_dz F)).fun_div
      ((measurable_const.fun_sub hFm).pow_const 2)
  have hkm : Measurable k := by dsimp only [k]; fun_prop
  have hSm : Measurable S := hPm.fun_sub hkm
  have hZm : Measurable Z := hSm.indicator isOpen_upperHalf.measurableSet
  have hdz (y : ℂ) (hy : y ∈ upperHalf) : dz F y = deriv F y :=
    dz_eq_deriv (hhol.differentiableAt (isOpen_upperHalf.mem_nhds hy))
  have hcenter : ‖dz F x‖ ≤ D :=
    (norm_dz_le_real_derivative F x).trans
      (hderiv 0 t (by simpa only [norm_zero] using hδ) (ht.trans_le heδ) x (mem_singleton x))
  obtain ⟨hQi, hQbound⟩ := hpull t (ht.trans_le he₂)
  have hPnorm (y : ℂ) (hy : y ∈ U) : ‖P y‖ ^ 2 =
      ‖dz F x‖ ^ 2 * ‖deriv F y / (F y - F x) ^ 2‖ ^ 2 := by
    rw [show P y = dz F x * dz F y / (F x - F y) ^ 2 from rfl,
      hdz y hy.1]
    simp only [norm_mul, norm_div, norm_pow, norm_sub_rev (F x) (F y), div_pow]
    ring
  have hPi : IntegrableOn (fun y : ℂ => ‖P y‖ ^ 2) U volume :=
    IntegrableOn.congr_fun (hQi.const_mul (‖dz F x‖ ^ 2))
      (fun y hy => (hPnorm y hy).symm) hU.measurableSet
  have hPbound : (∫ y : ℂ in U, ‖P y‖ ^ 2) ≤ D ^ 2 * C₂ := by
    calc
      (∫ y : ℂ in U, ‖P y‖ ^ 2) =
          ∫ y : ℂ in U, ‖dz F x‖ ^ 2 * ‖deriv F y / (F y - F x) ^ 2‖ ^ 2 :=
        setIntegral_congr_fun hU.measurableSet hPnorm
      _ = ‖dz F x‖ ^ 2 * ∫ y : ℂ in U, ‖deriv F y / (F y - F x) ^ 2‖ ^ 2 :=
        integral_const_mul _ _
      _ ≤ D ^ 2 * C₂ := mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) hcenter 2) hQbound
        (integral_nonneg (fun y : ℂ => sq_nonneg _)) (sq_nonneg _)
  have hkprofile : Integrable (fun y : ℂ => A ^ 4 * ((1 + ‖y‖) ^ 3)⁻¹) volume :=
    b36_p_profile_integrable.const_mul _
  have hkbound (y : ℂ) (hy : y ∈ U) :
      ‖k y‖ ^ 2 ≤ A ^ 4 * ((1 + ‖y‖) ^ 3)⁻¹ := by
    have hyr : r / 2 < ‖y - (x : ℂ)‖ := by
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hy.2
    have h := separated_square_kernel_norm_sq_le_profile (half_pos hr)
      (le_refl ‖(x : ℂ)‖) hyr.le
    simpa only [k, norm_div, norm_one, norm_pow, norm_sub_rev (x : ℂ) y] using h
  have hki : IntegrableOn (fun y : ℂ => ‖k y‖ ^ 2) U volume := by
    apply hkprofile.integrableOn.mono' (hkm.norm.pow_const 2).aestronglyMeasurable
    exact ae_restrict_of_forall_mem hU.measurableSet (fun y hy => by
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hkbound y hy)
  have hkMass : (∫ y : ℂ in U, ‖k y‖ ^ 2) ≤ C₀ := by
    calc
      (∫ y : ℂ in U, ‖k y‖ ^ 2) ≤ ∫ y : ℂ in U, A ^ 4 * ((1 + ‖y‖) ^ 3)⁻¹ :=
        integral_mono_ae hki hkprofile.integrableOn
          (ae_restrict_of_forall_mem hU.measurableSet hkbound)
      _ ≤ ∫ y : ℂ, A ^ 4 * ((1 + ‖y‖) ^ 3)⁻¹ :=
        setIntegral_le_integral hkprofile (Eventually.of_forall (fun y => by positivity))
      _ = C₀ := integral_const_mul _ _
  let B := U.indicator (fun y : ℂ => 2 * ‖P y‖ ^ 2 + 2 * ‖k y‖ ^ 2)
  have hB0 (y : ℂ) : 0 ≤ B y := indicator_nonneg (fun _ _ => by positivity) y
  have hBi : Integrable B (volume : Measure ℂ) :=
    IntegrableOn.integrable_indicator ((hPi.const_mul 2).add (hki.const_mul 2)) hU.measurableSet
  have hbound (y : ℂ) : ‖Z y‖ ^ 2 ≤ N y + B y := by
    by_cases hyH : y ∈ upperHalf
    · rw [show Z y = S y from indicator_of_mem hyH _]
      by_cases hyr : y ∈ ball (x : ℂ) r
      · have hs : ‖S y‖ ≤ C₁ := by
          have h := hlocal t (ht.trans_le he₁) y hyr
          simpa only [S, P, k, hdz x x.im_pos, hdz y hyH] using h
        calc
          ‖S y‖ ^ 2 ≤ C₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
          _ ≤ N y + B y := by rw [show N y = C₁ ^ 2 from indicator_of_mem hyr _]; linarith [hB0 y]
      · have hyU : y ∈ U := ⟨hyH, by
          intro hyc
          have hd : dist y x ≤ r / 2 := mem_closedBall.mp hyc
          exact hyr (mem_ball.mpr (hd.trans_lt (half_lt_self hr)))⟩
        rw [show N y = 0 from indicator_of_notMem hyr _, zero_add,
          show B y = 2 * ‖P y‖ ^ 2 + 2 * ‖k y‖ ^ 2 from indicator_of_mem hyU _]
        have hs : ‖S y‖ ≤ ‖P y‖ + ‖k y‖ := norm_sub_le _ _
        nlinarith [norm_nonneg (S y), norm_nonneg (P y), norm_nonneg (k y),
          sq_nonneg (‖P y‖ - ‖k y‖)]
    · rw [show Z y = 0 from indicator_of_notMem hyH _, norm_zero, zero_pow two_ne_zero]
      exact add_nonneg (hN0 y) (hB0 y)
  have henv : Integrable (N + B) volume := hNi.add hBi
  have hZi : Integrable (fun y : ℂ => ‖Z y‖ ^ 2) volume := by
    apply henv.mono' (hZm.norm.pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall (fun y => by
      simpa only [Pi.add_apply, Real.norm_of_nonneg (sq_nonneg _)] using hbound y)
  have hmass : (∫ y : ℂ, N y + B y) ≤ C := by
    calc
      (∫ y : ℂ, N y + B y) = (∫ y : ℂ, N y) + ∫ y : ℂ, B y := integral_add hNi hBi
      _ = (∫ y : ℂ, N y) + ∫ y : ℂ in U, 2 * ‖P y‖ ^ 2 + 2 * ‖k y‖ ^ 2 := by
        simp only [B, integral_indicator hU.measurableSet]
      _ = (∫ y : ℂ, N y) + 2 * (∫ y : ℂ in U, ‖P y‖ ^ 2) +
          2 * (∫ y : ℂ in U, ‖k y‖ ^ 2) := by
        rw [integral_add (hPi.const_mul 2) (hki.const_mul 2),
          integral_const_mul, integral_const_mul]
        ring
      _ ≤ C := by dsimp only [C]; nlinarith [hPbound, hkMass]
  exact ⟨(memLp_two_iff_integrable_sq_norm hZm.aestronglyMeasurable).2 hZi,
    (integral_mono_ae hZi henv (Eventually.of_forall hbound)).trans hmass⟩

/-- The actual regular kernel is extended by zero off the original upper
half-plane. Its diagonal point value is zero. -/
def canonicalPassiveRegularKernelInput
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : ℍ) (t : ℂ) : ℂ → ℂ :=
  upperHalf.indicator (fun y : ℂ =>
    dz (canonicalBiparameterFamily R p q 0 t) x *
      dz (canonicalBiparameterFamily R p q 0 t) y /
      (canonicalBiparameterFamily R p q 0 t x -
        canonicalBiparameterFamily R p q 0 t y) ^ 2 - 1 / ((x : ℂ) - y) ^ 2)

/-- The same actual regular input has a uniform planar square-integral bound
on one parameter disk. Actual image domains remain unchanged. -/
theorem canonicalPassiveRegularKernelInput_uniform_memLp_two
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : ℍ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ t : ℂ, ‖t‖ < ε →
      MemLp (canonicalPassiveRegularKernelInput R p q x t) 2 (volume : Measure ℂ) ∧
        (∫ y : ℂ, ‖canonicalPassiveRegularKernelInput R p q x t y‖ ^ 2) ≤ C := by
  simpa only [canonicalPassiveRegularKernelInput] using
    actual_passive_regular_kernel_l2 R p hp q x

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
