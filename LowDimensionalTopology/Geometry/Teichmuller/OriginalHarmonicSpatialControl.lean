module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicAsymmetricControl
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicConformalQuotient
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Data.Finset.Max
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Spatial control for the actual independent harmonic family

Actual conformal quotient disks give common spatial C1 regularity and
locally uniform real derivative bounds. Finite covers give the bound
on each compact subset of the original upper half-plane.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped UpperHalfPlane ComplexConjugate ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

private theorem biparameter_coefficient_reflection
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (s t z : ℂ) :
    conj (harmonicBiparameterCoefficient R p q (conj t) (conj s) (conj z)) =
      harmonicBiparameterCoefficient R p q s t z := by
  by_cases hz : z.im < 0
  · have hc : ¬(conj z).im < 0 := by rw [conj_im]; linarith
    simp only [harmonicBiparameterCoefficient, ite_eq_right hc, ite_eq_left hz,
      map_mul, conj_conj]
  · by_cases hzero : z.im = 0
    · simp only [harmonicBiparameterCoefficient, harmonicPlane, conj_im, hzero,
        neg_zero, ofReal_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero,
        ite_self, map_zero]
    · have hpos : 0 < z.im := lt_of_le_of_ne (le_of_not_gt hz) (Ne.symm hzero)
      have hc : (conj z).im < 0 := by rw [conj_im]; linarith only [hpos]
      simp only [harmonicBiparameterCoefficient, ite_eq_left hc, ite_eq_right hz,
        map_mul, conj_conj]

private theorem biparameter_reflection
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε →
      canonicalBiparameterFamily R p q s t =
        fun z => conj (canonicalBiparameterFamily R p q (conj t) (conj s) (conj z)) := by
  obtain ⟨ε, hε, hspec, _, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  refine ⟨ε, hε, ?_⟩
  intro s t hs ht
  let f := canonicalBiparameterFamily R p q s t
  let g := canonicalBiparameterFamily R p q (conj t) (conj s)
  let h : ℂ → ℂ := fun z => conj (g (conj z))
  have hf := (hspec s t hs ht).2
  have hg := (hspec (conj t) (conj s) (by simpa only [norm_conj] using ht)
    (by simpa only [norm_conj] using hs)).2
  obtain ⟨K, hgK⟩ := hg.1
  have hhK : IsKQC h univ K := by
    simpa only [preimage_univ] using abR_x_isKQC_conj hgK
  have hhs : h '' univ = univ := by
    apply eq_univ_of_forall
    intro w
    have hw : conj w ∈ g '' univ := by rw [hg.2.1]; exact mem_univ _
    obtain ⟨z, _, hz⟩ := hw
    exact ⟨conj z, mem_univ _, by simp only [h, conj_conj, hz]⟩
  have hgd : ∀ᵐ z : ℂ, DifferentiableAt ℝ g z := by
    simpa only [Measure.restrict_univ] using thm9_3_differentiable_ae hgK
  have hmu : ∀ᵐ z : ℂ, complexDilatation f z = complexDilatation h z := by
    filter_upwards [hf.2.2.2.2,
      gzE_conj_measurePreserving.quasiMeasurePreserving.ae hg.2.2.2.2,
      gzE_conj_measurePreserving.quasiMeasurePreserving.ae hgd] with z hfz hgz hdz
    obtain ⟨_, hz, hzb⟩ := abR_x_dz_dzbar_conj hdz
    have he : complexDilatation h z = conj (complexDilatation g (conj z)) := by
      simp only [complexDilatation, h, hz, hzb, map_div₀]
    rw [he, hfz, hgz, biparameter_coefficient_reflection]
  exact thm13_5_uniqueness_plane hf.1 ⟨K, hhK⟩ hf.2.1 hhs hmu
    hf.2.2.1 hf.2.2.2.1
    (by simp only [map_zero, hg.2.2.1])
    (by simp only [map_one, hg.2.2.2.1])

private theorem biparameter_upper_spatial_analytic
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε →
      AnalyticOnNhd ℝ (canonicalBiparameterFamily R p q s t) upperHalf := by
  obtain ⟨ε₁, hε₁, hAW⟩ := canonicalBiparameterFamily_asymmetric_ahlforsWeill R p hp q
  obtain ⟨ε₂, hε₂, hquot⟩ := canonicalBiparameterFamily_conformal_quotient R p hp q
  obtain ⟨ε₃, hε₃, hspec, _, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  let ε := min ε₁ (min ε₂ ε₃)
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ hε₃)
  refine ⟨ε, hε, ?_⟩
  intro s t hs ht z hz
  have hs₁ : ‖s‖ < ε₁ := hs.trans_le (min_le_left _ _)
  have hs₂ : ‖s‖ < ε₂ := hs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht₂ : ‖t‖ < ε₂ := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs₃ : ‖s‖ < ε₃ := hs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let A := canonicalBiparameterFamily R p q s 0
  let G := canonicalBiparameterFamily R p q s t ∘ Function.invFunOn A upperHalf
  obtain ⟨K, hK⟩ := (hspec s 0 hs₃ (by simpa only [norm_zero] using hε₃)).2.1
  have hA : IsKQC A upperHalf K :=
    ac_t_isKQC_restrict hK isOpen_upperHalf (subset_univ _)
  have hD : IsOpen (A '' upperHalf) := isOpen_image_of_isKQC hA
  have hG : DifferentiableOn ℂ G (A '' upperHalf) :=
    ((hquot s hs₂).1 t (mem_ball_zero_iff.mpr ht₂)).1
  have hGa : AnalyticAt ℝ G (A z) :=
    (hG.analyticAt (hD.mem_nhds (mem_image_of_mem A hz))).restrictScalars
  have hAa : AnalyticAt ℝ A z := (hAW s hs₁).2.1 z hz
  apply (hGa.comp hAa).congr
  filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
  change canonicalBiparameterFamily R p q s t
      (Function.invFunOn A upperHalf (A w)) = canonicalBiparameterFamily R p q s t w
  rw [hA.2.2.1.2.1.leftInvOn_invFunOn hw]

private theorem biparameter_spatial_c1
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε →
      ContDiffOn ℝ 1 (canonicalBiparameterFamily R p q s t) (upperHalf ∪ lowerHalf) := by
  obtain ⟨ε₁, hε₁, hupper⟩ := biparameter_upper_spatial_analytic R p hp q
  obtain ⟨ε₂, hε₂, hreflect⟩ := biparameter_reflection R p hp q
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro s t hs ht z hz
  have hs₁ : ‖s‖ < ε₁ := hs.trans_le (min_le_left _ _)
  have ht₁ : ‖t‖ < ε₁ := ht.trans_le (min_le_left _ _)
  rcases hz with hz | hz
  · exact ((hupper s t hs₁ ht₁) z hz).contDiffAt.contDiffWithinAt
  · have hcz : conj z ∈ upperHalf := by
      change 0 < (conj z).im
      rw [conj_im]
      exact neg_pos.mpr hz
    have hG : ContDiffAt ℝ 1
        (canonicalBiparameterFamily R p q (conj t) (conj s)) (conj z) :=
      ((hupper (conj t) (conj s) (by simpa only [norm_conj] using ht₁)
        (by simpa only [norm_conj] using hs₁)) (conj z) hcz).contDiffAt
    have hc : ContDiff ℝ 1 (fun w : ℂ => conj w) :=
      (conjCLE : ℂ →L[ℝ] ℂ).contDiff
    rw [hreflect s t (hs.trans_le (min_le_right _ _)) (ht.trans_le (min_le_right _ _))]
    exact (hc.contDiffAt.comp z (hG.comp z hc.contDiffAt)).contDiffWithinAt

private theorem biparameter_local_spatial_bound
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s₀ ∈ ball (0 : ℂ) ε, ∀ z₀ ∈ upperHalf,
      ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
        ball s₀ r ⊆ ball (0 : ℂ) ε ∧ ball z₀ r ⊆ upperHalf ∧
        ∀ s ∈ ball s₀ r, ∀ t ∈ ball (0 : ℂ) ε, ∀ z ∈ ball z₀ r,
          ‖fderiv ℝ (canonicalBiparameterFamily R p q s t) z‖ ≤ C := by
  obtain ⟨ε₁, hε₁, hC1⟩ := biparameter_spatial_c1 R p hp q
  obtain ⟨ε₂, hε₂, hAs⟩ :=
    canonicalBiparameterFamily_asymmetric_local_spatial_derivative_bound R p hp q
  obtain ⟨ε₃, hε₃, hdisks⟩ :=
    canonicalBiparameterFamily_asymmetric_local_image_disks R p hp q
  obtain ⟨ε₄, hε₄, hquot⟩ := canonicalBiparameterFamily_conformal_quotient R p hp q
  obtain ⟨ε₅, hε₅, hspec, hfirst, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  let ε := min ε₁ (min ε₂ (min ε₃ (min ε₄ ε₅)))
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ (lt_min hε₃ (lt_min hε₄ hε₅)))
  have he₁ : ε ≤ ε₁ := min_le_left _ _
  have he₂ : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have he₃ : ε ≤ ε₃ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he₄ : ε ≤ ε₄ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have he₅ : ε ≤ ε₅ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨ε, hε, ?_⟩
  intro s₀ hs₀ z₀ hz₀
  obtain ⟨a, C, ha, hC, _haP, haH, hAderiv⟩ :=
    hAs s₀ (ball_subset_ball he₂ hs₀) z₀ hz₀
  obtain ⟨b, d, B, hb, hd, hB, _hbP, hbounds⟩ :=
    hdisks s₀ (ball_subset_ball he₃ hs₀) z₀ hz₀
  let w₀ := canonicalBiparameterFamily R p q s₀ 0 z₀
  have hzero₅ : ‖(0 : ℂ)‖ < ε₅ := by simpa only [norm_zero] using hε₅
  have hc : ContinuousAt (fun s : ℂ => canonicalBiparameterFamily R p q s 0 z₀) s₀ :=
    ((hfirst 0 hzero₅ z₀).differentiableAt
      (isOpen_ball.mem_nhds (ball_subset_ball he₅ hs₀))).continuousAt
  have hn : (fun s : ℂ => canonicalBiparameterFamily R p q s 0 z₀) ⁻¹'
      ball w₀ (d / 4) ∈ 𝓝 s₀ :=
    hc.preimage_mem_nhds (ball_mem_nhds _ (by positivity))
  obtain ⟨c, hcpos, hcsub⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨e, hepos, heP⟩ := Metric.isOpen_iff.mp isOpen_ball s₀ hs₀
  let r := min a (min b (min c (min e (d / (4 * (C + 1))))))
  have hr : 0 < r := lt_min ha (lt_min hb (lt_min hcpos
    (lt_min hepos (by positivity))))
  have hra : r ≤ a := min_le_left _ _
  have hrb : r ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hrc : r ≤ c :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hre : r ≤ e :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hrd : r ≤ d / (4 * (C + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hrprod : (C + 1) * r ≤ d / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (C + 1))).mp hrd
    linarith
  refine ⟨r, B / (d / 2) * C, hr, by positivity,
    (ball_subset_ball hre).trans heP, (ball_subset_ball hra).trans haH, ?_⟩
  intro s hs t ht z hz
  have hsa : s ∈ ball s₀ a := ball_subset_ball hra hs
  have hsb : s ∈ ball s₀ b := ball_subset_ball hrb hs
  have hsε : ‖s‖ < ε := mem_ball_zero_iff.mp (heP (ball_subset_ball hre hs))
  have hs₁ : ‖s‖ < ε₁ := hsε.trans_le he₁
  have hs₄ : ‖s‖ < ε₄ := hsε.trans_le he₄
  have hs₅ : ‖s‖ < ε₅ := hsε.trans_le he₅
  have hza : z ∈ ball z₀ a := ball_subset_ball hra hz
  have hzH : z ∈ upperHalf := haH hza
  let A := canonicalBiparameterFamily R p q s 0
  let G := canonicalBiparameterFamily R p q s t ∘ Function.invFunOn A upperHalf
  have hAc1 : ContDiffOn ℝ 1 A upperHalf :=
    (hC1 s 0 hs₁ (by simpa only [norm_zero] using hε₁)).mono (fun _ hw => Or.inl hw)
  have hAd (w : ℂ) (hw : w ∈ upperHalf) : DifferentiableAt ℝ A w :=
    (hAc1.differentiableOn_one w hw).differentiableAt (isOpen_upperHalf.mem_nhds hw)
  have hspace : ‖A z - A z₀‖ ≤ C * ‖z - z₀‖ :=
    (convex_ball z₀ a).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw => hAd w (haH hw)) (fun w hw => hAderiv s hsa w hw)
      (mem_ball_self ha) hza
  have hspatial : ‖A z - A z₀‖ < d / 4 := by
    apply hspace.trans_lt
    calc
      C * ‖z - z₀‖ ≤ (C + 1) * ‖z - z₀‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C + 1) * r :=
        mul_lt_mul_of_pos_left (by simpa only [mem_ball, dist_eq_norm] using hz)
          (by linarith)
      _ ≤ d / 4 := hrprod
  have hcenter : ‖A z₀ - w₀‖ < d / 4 := by
    have h := hcsub (ball_subset_ball hrc hs)
    simpa only [mem_preimage, mem_ball, dist_eq_norm] using h
  have hAz : ‖A z - w₀‖ < d / 2 := by
    linarith [norm_sub_le_norm_sub_add_norm_sub (A z) (A z₀) w₀]
  have hsmallDisk : closedBall (A z) (d / 2) ⊆ closedBall w₀ d := by
    intro w hw
    have hw' : ‖w - A z‖ ≤ d / 2 := by
      simpa only [mem_closedBall, dist_eq_norm] using hw
    rw [mem_closedBall, dist_eq_norm]
    linarith [norm_sub_le_norm_sub_add_norm_sub w (A z) w₀]
  have hfixed := hbounds s hsb
  have hDdisk : closedBall (A z) (d / 2) ⊆ A '' upperHalf :=
    hsmallDisk.trans hfixed.1
  have hG : DifferentiableOn ℂ G (A '' upperHalf) :=
    ((hquot s hs₄).1 t (ball_subset_ball he₄ ht)).1
  have hGbound : ∀ w ∈ closedBall w₀ d, ‖G w‖ ≤ B :=
    hfixed.2.2 t (ball_subset_ball he₃ ht)
  have hCauchy : ‖deriv G (A z)‖ ≤ B / (d / 2) :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (hG.diffContOnCl_ball hDdisk)
      (fun w hw => hGbound w (hsmallDisk (sphere_subset_closedBall hw)))
  obtain ⟨Q, hQ⟩ := (hspec s 0 hs₅ hzero₅).2.1
  have hAqc : IsKQC A upperHalf Q := ac_t_isKQC_restrict hQ isOpen_upperHalf (subset_univ _)
  have hD : IsOpen (A '' upperHalf) := isOpen_image_of_isKQC hAqc
  have hGdiff : DifferentiableAt ℂ G (A z) :=
    hG.differentiableAt (hD.mem_nhds (mem_image_of_mem A hzH))
  have hGnorm : ‖fderiv ℝ G (A z)‖ ≤ B / (d / 2) := by
    calc
      ‖fderiv ℝ G (A z)‖ = ‖fderiv ℂ G (A z)‖ := by
        rw [hGdiff.fderiv_restrictScalars ℝ, ContinuousLinearMap.norm_restrictScalars]
      _ = ‖deriv G (A z)‖ := norm_deriv_eq_norm_fderiv.symm
      _ ≤ B / (d / 2) := hCauchy
  have hsame : (G ∘ A) =ᶠ[𝓝 z] canonicalBiparameterFamily R p q s t := by
    filter_upwards [isOpen_upperHalf.mem_nhds hzH] with w hw
    change canonicalBiparameterFamily R p q s t
        (Function.invFunOn A upperHalf (A w)) = canonicalBiparameterFamily R p q s t w
    rw [hAqc.2.2.1.2.1.leftInvOn_invFunOn hw]
  have hchain := (hGdiff.restrictScalars ℝ).hasFDerivAt.comp z (hAd z hzH).hasFDerivAt
  rw [← hsame.fderiv_eq, hchain.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hGnorm (hAderiv s hsa z hza) (norm_nonneg _)
      (by positivity : 0 ≤ B / (d / 2)))

/-- The same actual family has common spatial C1 regularity, reflection,
local derivative control at every parameter center, and compact bounds. -/
theorem canonicalBiparameterFamily_spatial_c1_compact_control
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε →
        ContDiffOn ℝ 1 (canonicalBiparameterFamily R p q s t)
          (upperHalf ∪ lowerHalf)) ∧
      (∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε →
        canonicalBiparameterFamily R p q s t =
          fun z => conj (canonicalBiparameterFamily R p q
            (conj t) (conj s) (conj z))) ∧
      (∀ s₀ ∈ ball (0 : ℂ) ε, ∀ z₀ ∈ upperHalf,
        ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
          ball s₀ r ⊆ ball (0 : ℂ) ε ∧ ball z₀ r ⊆ upperHalf ∧
          ∀ s ∈ ball s₀ r, ∀ t ∈ ball (0 : ℂ) ε,
            ∀ z ∈ ball z₀ r,
              ‖fderiv ℝ (canonicalBiparameterFamily R p q s t) z‖ ≤ C) ∧
      ∀ K : Set ℍ, IsCompact K →
        ∃ δ D : ℝ, 0 < δ ∧ δ ≤ ε ∧ 0 ≤ D ∧
          ∀ s t : ℂ, ‖s‖ < δ → ‖t‖ < δ → ∀ z ∈ K,
            ‖fderiv ℝ (canonicalBiparameterFamily R p q s t) (z : ℂ)‖ ≤ D := by
  classical
  obtain ⟨ε₁, hε₁, hC1⟩ := biparameter_spatial_c1 R p hp q
  obtain ⟨ε₂, hε₂, hreflect⟩ := biparameter_reflection R p hp q
  obtain ⟨ε₃, hε₃, hlocal⟩ := biparameter_local_spatial_bound R p hp q
  let ε := min ε₁ (min ε₂ ε₃)
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ hε₃)
  have he₁ : ε ≤ ε₁ := min_le_left _ _
  have he₂ : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have he₃ : ε ≤ ε₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hlocal' : ∀ s₀ ∈ ball (0 : ℂ) ε, ∀ z₀ ∈ upperHalf,
      ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
        ball s₀ r ⊆ ball (0 : ℂ) ε ∧ ball z₀ r ⊆ upperHalf ∧
        ∀ s ∈ ball s₀ r, ∀ t ∈ ball (0 : ℂ) ε, ∀ z ∈ ball z₀ r,
          ‖fderiv ℝ (canonicalBiparameterFamily R p q s t) z‖ ≤ C := by
    intro s₀ hs₀ z₀ hz₀
    obtain ⟨r, C, hr, hC, _hrP, hrH, hbound⟩ :=
      hlocal s₀ (ball_subset_ball he₃ hs₀) z₀ hz₀
    obtain ⟨a, ha, haP⟩ := Metric.isOpen_iff.mp isOpen_ball s₀ hs₀
    refine ⟨min r a, C, lt_min hr ha, hC,
      (ball_subset_ball (min_le_right _ _)).trans haP,
      (ball_subset_ball (min_le_left _ _)).trans hrH, ?_⟩
    intro s hs t ht z hz
    exact hbound s (ball_subset_ball (min_le_left _ _) hs)
      t (ball_subset_ball he₃ ht) z (ball_subset_ball (min_le_left _ _) hz)
  refine ⟨ε, hε,
    fun s t hs ht => hC1 s t (hs.trans_le he₁) (ht.trans_le he₁),
    fun s t hs ht => hreflect s t (hs.trans_le he₂) (ht.trans_le he₂), hlocal', ?_⟩
  intro K hK
  have hloc (z : K) := hlocal' 0 (mem_ball_self hε) (z.val : ℂ) z.val.im_pos
  choose r C hr _hC _hrP _hrH hbound using hloc
  let U : K → Set ℍ := fun i => {z | (z : ℂ) ∈ ball (i.val : ℂ) (r i)}
  have hU (i : K) : IsOpen (U i) := isOpen_ball.preimage UpperHalfPlane.continuous_coe
  have hcover : K ⊆ ⋃ i : K, U i := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr ⟨z, hz⟩)⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover U hU hcover
  let rs : Finset ℝ := insert ε (T.image r)
  have hrs : rs.Nonempty := Finset.insert_nonempty _ _
  let δ : ℝ := rs.min' hrs
  have hpositive (a : ℝ) (ha : a ∈ rs) : 0 < a := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hε
    · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ha
      exact hr i
  have hδ : 0 < δ := hpositive _ (Finset.min'_mem rs hrs)
  have hδε : δ ≤ ε := Finset.min'_le rs ε (Finset.mem_insert_self _ _)
  have hδr (i : K) (hi : i ∈ T) : δ ≤ r i :=
    Finset.min'_le rs (r i) (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  let cs : Finset ℝ := insert 0 (T.image C)
  have hcs : cs.Nonempty := Finset.insert_nonempty _ _
  let D : ℝ := cs.max' hcs
  have hD : 0 ≤ D := Finset.le_max' cs 0 (Finset.mem_insert_self _ _)
  have hCD (i : K) (hi : i ∈ T) : C i ≤ D :=
    Finset.le_max' cs (C i) (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  refine ⟨δ, D, hδ, hδε, hD, ?_⟩
  intro s t hs ht z hz
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hT hz)
  exact (hbound i s (mem_ball_zero_iff.mpr (hs.trans_le (hδr i hi)))
    t (mem_ball_zero_iff.mpr (ht.trans_le hδε)) (z : ℂ) hzi).trans (hCD i hi)

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
