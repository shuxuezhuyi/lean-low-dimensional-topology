module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicAhlforsWeillFormula
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicCompactImages
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Local control for the actual asymmetric harmonic family

Finite lower derivatives and the actual rational expression give locally
uniform first spatial derivative bounds at every parameter center. Scalar
Cauchy estimates and normalized quasiconformal properness give fixed disks
in the true moving image domain and bounds for the actual relative family.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC

private theorem norm_sub_center_le_of_holomorphic_bound
    {g : ℂ → ℂ} {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r))
    (hM : ∀ v ∈ ball c r, ‖g v‖ ≤ M)
    {s : ℂ} (hs : ‖s - c‖ < r / 2) :
    ‖g s - g c‖ ≤ M / (r / 2) * ‖s - c‖ := by
  have hd (w : ℂ) (hw : w ∈ ball c (r / 2)) :
      ‖deriv g w‖ ≤ M / (r / 2) := by
    have hsub : closedBall w (r / 2) ⊆ ball c r := by
      intro v hv
      rw [mem_closedBall] at hv
      rw [mem_ball] at hw ⊢
      linarith [dist_triangle v w c]
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (hg.diffContOnCl_ball hsub)
      (fun v hv => hM v (hsub (sphere_subset_closedBall hv)))
  have hdiff (w : ℂ) (hw : w ∈ ball c (r / 2)) : DifferentiableAt ℂ g w :=
    hg.differentiableAt (isOpen_ball.mem_nhds
      ((ball_subset_ball (by linarith : r / 2 ≤ r)) hw))
  exact (convex_ball c (r / 2)).norm_image_sub_le_of_norm_deriv_le
    hdiff hd (mem_ball_self (by positivity)) (by rwa [mem_ball, dist_eq_norm])

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

private theorem asymmetric_lower_jets
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, n ≤ 3 →
      (∀ w ∈ lowerHalf, DifferentiableOn ℂ
        (fun s => iteratedDeriv n (canonicalBiparameterFamily R p q s 0) w) (ball 0 ε)) ∧
      (∀ s ∈ ball (0 : ℂ) ε, DifferentiableOn ℂ
        (iteratedDeriv n (canonicalBiparameterFamily R p q s 0)) lowerHalf) ∧
      (∀ s₀ ∈ ball (0 : ℂ) ε, ∀ w₀ ∈ lowerHalf, ∃ r > 0,
        ball s₀ r ⊆ ball (0 : ℂ) ε ∧ ball w₀ r ⊆ lowerHalf ∧
        ∃ M : ℝ, ∀ s ∈ ball s₀ r, ∀ w ∈ ball w₀ r,
          ‖iteratedDeriv n (canonicalBiparameterFamily R p q s 0) w‖ ≤ M) := by
  obtain ⟨ε₁, hε₁, hAW⟩ := canonicalBiparameterFamily_asymmetric_ahlforsWeill R p hp q
  obtain ⟨ε₂, hε₂, _, hfirst, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  obtain ⟨ε₃, hε₃, hsharp, _⟩ := canonicalBiparameterFamily_bounded_closeness R p hp q
  let ε := min ε₁ (min ε₂ ε₃)
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ hε₃)
  have he₁ : ε ≤ ε₁ := min_le_left _ _
  have he₂ : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have he₃ : ε ≤ ε₃ := (min_le_right _ _).trans (min_le_right _ _)
  let A := fun s => canonicalBiparameterFamily R p q s 0
  have ha : ∀ w ∈ lowerHalf, DifferentiableOn ℂ (fun s => A s w) (ball 0 ε) := by
    intro w _
    exact (hfirst 0 (by simpa only [norm_zero] using hε₂) w).mono (ball_subset_ball he₂)
  have hb : ∀ s ∈ ball (0 : ℂ) ε, DifferentiableOn ℂ (A s) lowerHalf :=
    fun s hs => (hAW s ((mem_ball_zero_iff.mp hs).trans_le he₁)).1
  have hc : ∀ s₀ ∈ ball (0 : ℂ) ε, ∀ w₀ ∈ lowerHalf, ∃ r > 0,
      ball s₀ r ⊆ ball (0 : ℂ) ε ∧ ball w₀ r ⊆ lowerHalf ∧
      ∃ M : ℝ, ∀ s ∈ ball s₀ r, ∀ w ∈ ball w₀ r, ‖A s w‖ ≤ M := by
    intro s₀ hs₀ w₀ hw₀
    obtain ⟨a, ha, haP⟩ := Metric.isOpen_iff.mp isOpen_ball s₀ hs₀
    obtain ⟨b, hb, hbL⟩ := Metric.isOpen_iff.mp isOpen_lowerHalf w₀ hw₀
    let r := min a (min b 1)
    have hr : 0 < r := lt_min ha (lt_min hb zero_lt_one)
    have hrP : ball s₀ r ⊆ ball (0 : ℂ) ε :=
      (ball_subset_ball (min_le_left _ _)).trans haP
    have hrL : ball w₀ r ⊆ lowerHalf :=
      (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))).trans hbL
    refine ⟨r, hr, hrP, hrL, lambdaInv (3 * quadLambda (‖w₀‖ + 1)), ?_⟩
    intro s hs w hw
    have hsε : ‖s‖ < ε₃ := (mem_ball_zero_iff.mp (hrP hs)).trans_le he₃
    have hw1 : ‖w - w₀‖ < 1 := by
      rw [mem_ball, dist_eq_norm] at hw
      exact hw.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hn : ‖w‖ ≤ ‖w₀‖ + 1 := by linarith [norm_sub_norm_le w w₀]
    exact UniversalTeichmuller.ut2_nb_upper
      (hsharp s 0 hsε (by simpa only [norm_zero] using hε₃)) (by positivity) hn
  refine ⟨ε, hε, ?_⟩
  intro n _
  exact bB_h0_iteratedDeriv isOpen_lowerHalf ha hb hc n

private theorem asymmetric_lower_jets_continuous
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, n ≤ 3 →
      ∀ s₀ ∈ ball (0 : ℂ) ε, ∀ w₀ ∈ lowerHalf,
        ContinuousAt (fun x : ℂ × ℂ =>
          iteratedDeriv n (canonicalBiparameterFamily R p q x.1 0) x.2) (s₀, w₀) := by
  obtain ⟨ε, hε, hjets⟩ := asymmetric_lower_jets R p hp q
  refine ⟨ε, hε, ?_⟩
  intro n hn s₀ hs₀ w₀ hw₀
  obtain ⟨ha, hb, hc⟩ := hjets n hn
  obtain ⟨r, hr, hrP, hrL, M, hM⟩ := hc s₀ hs₀ w₀ hw₀
  let F := fun s w => iteratedDeriv n (canonicalBiparameterFamily R p q s 0) w
  let C := max (M / (r / 2)) 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hleC : M / (r / 2) ≤ C := le_max_left _ _
  rw [Metric.continuousAt_iff]
  intro η hη
  let δ := min (r / 2) (η / (2 * C))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hx₁ : ‖x.1 - s₀‖ < δ := by
    have h := (le_max_left (dist x.1 s₀) (dist x.2 w₀)).trans_lt
      (show max (dist x.1 s₀) (dist x.2 w₀) < δ from hx)
    rwa [dist_eq_norm] at h
  have hx₂ : ‖x.2 - w₀‖ < δ := by
    have h := (le_max_right (dist x.1 s₀) (dist x.2 w₀)).trans_lt
      (show max (dist x.1 s₀) (dist x.2 w₀) < δ from hx)
    rwa [dist_eq_norm] at h
  have hx₁r : ‖x.1 - s₀‖ < r / 2 := hx₁.trans_le (min_le_left _ _)
  have hx₂r : ‖x.2 - w₀‖ < r / 2 := hx₂.trans_le (min_le_left _ _)
  have hx₂B : x.2 ∈ ball w₀ r := by
    rw [mem_ball, dist_eq_norm]
    linarith
  have h₁ : ‖F x.1 x.2 - F s₀ x.2‖ ≤ C * ‖x.1 - s₀‖ :=
    (norm_sub_center_le_of_holomorphic_bound hr
      ((ha x.2 (hrL hx₂B)).mono hrP) (fun s hs => hM s hs x.2 hx₂B) hx₁r).trans
        (mul_le_mul_of_nonneg_right hleC (norm_nonneg _))
  have h₂ : ‖F s₀ x.2 - F s₀ w₀‖ ≤ C * ‖x.2 - w₀‖ :=
    (norm_sub_center_le_of_holomorphic_bound hr ((hb s₀ hs₀).mono hrL)
      (fun w hw => hM s₀ (mem_ball_self hr) w hw) hx₂r).trans
        (mul_le_mul_of_nonneg_right hleC (norm_nonneg _))
  have he₁ : C * ‖x.1 - s₀‖ < η / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp
      (hx₁.trans_le (min_le_right _ _))
    nlinarith
  have he₂ : C * ‖x.2 - w₀‖ < η / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp
      (hx₂.trans_le (min_le_right _ _))
    nlinarith
  rw [dist_eq_norm]
  change ‖F x.1 x.2 - F s₀ w₀‖ < η
  calc
    _ ≤ ‖F x.1 x.2 - F s₀ x.2‖ + ‖F s₀ x.2 - F s₀ w₀‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * ‖x.1 - s₀‖ + C * ‖x.2 - w₀‖ := add_le_add h₁ h₂
    _ < η := by linarith

/-- The same asymmetric normalized family has locally uniform real spatial
derivative bounds at every center of a common parameter disk. -/
theorem canonicalBiparameterFamily_asymmetric_local_spatial_derivative_bound
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s₀ ∈ ball (0 : ℂ) ε, ∀ z₀ ∈ upperHalf,
      ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
        ball s₀ r ⊆ ball (0 : ℂ) ε ∧ ball z₀ r ⊆ upperHalf ∧
        ∀ s ∈ ball s₀ r, ∀ z ∈ ball z₀ r,
          ‖fderiv ℝ (canonicalBiparameterFamily R p q s 0) z‖ ≤ C := by
  obtain ⟨ε₁, hε₁, hjetc⟩ := asymmetric_lower_jets_continuous R p hp q
  obtain ⟨ε₂, hε₂, hjetd⟩ := asymmetric_lower_jets R p hp q
  obtain ⟨ε₃, hε₃, hAW⟩ := canonicalBiparameterFamily_asymmetric_ahlforsWeill R p hp q
  let ε := min ε₁ (min ε₂ ε₃)
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ hε₃)
  have he₁ : ε ≤ ε₁ := min_le_left _ _
  have he₂ : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have he₃ : ε ≤ ε₃ := (min_le_right _ _).trans (min_le_right _ _)
  let A := fun s => canonicalBiparameterFamily R p q s 0
  refine ⟨ε, hε, ?_⟩
  intro s₀ hs₀ z₀ hz₀
  have hs₀₁ : s₀ ∈ ball (0 : ℂ) ε₁ := ball_subset_ball he₁ hs₀
  have hw₀ : conj z₀ ∈ lowerHalf := by
    change (conj z₀).im < 0
    simpa only [conj_im] using neg_lt_zero.mpr hz₀
  have hc₀ : ContinuousAt (fun x : ℂ × ℂ => A x.1 x.2) (s₀, conj z₀) := by
    simpa only [iteratedDeriv_zero] using
      hjetc 0 (by decide) s₀ hs₀₁ (conj z₀) hw₀
  have hc₁ : ContinuousAt (fun x : ℂ × ℂ => deriv (A x.1) x.2) (s₀, conj z₀) := by
    simpa only [iteratedDeriv_one] using
      hjetc 1 (by decide) s₀ hs₀₁ (conj z₀) hw₀
  have hc₂ : ContinuousAt (fun x : ℂ × ℂ => deriv (deriv (A x.1)) x.2)
      (s₀, conj z₀) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hjetc 2 (by decide) s₀ hs₀₁ (conj z₀) hw₀
  let c : ℂ × (ℂ × ℂ) := (s₀, (z₀, conj z₀))
  let D : ℂ × (ℂ × ℂ) → ℂ := fun x =>
    2 * deriv (A x.1) x.2.2 - (x.2.1 - x.2.2) * deriv (deriv (A x.1)) x.2.2
  let T : ℂ × (ℂ × ℂ) → ℂ := fun x =>
    A x.1 x.2.2 + 2 * (x.2.1 - x.2.2) * deriv (A x.1) x.2.2 ^ 2 / D x
  have hproj : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => (x.1, x.2.2)) c :=
    continuous_fst.continuousAt.prodMk (continuous_snd.comp continuous_snd).continuousAt
  have h₀ : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => A x.1 x.2.2) c :=
    hc₀.comp (f := fun x : ℂ × (ℂ × ℂ) => (x.1, x.2.2)) (x := c) hproj
  have h₁ : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => deriv (A x.1) x.2.2) c :=
    hc₁.comp (f := fun x : ℂ × (ℂ × ℂ) => (x.1, x.2.2)) (x := c) hproj
  have h₂ : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => deriv (deriv (A x.1)) x.2.2) c :=
    hc₂.comp (f := fun x : ℂ × (ℂ × ℂ) => (x.1, x.2.2)) (x := c) hproj
  have hsub : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => x.2.1 - x.2.2) c :=
    ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)).continuousAt
  have hD : ContinuousAt D c :=
    (continuousAt_const.mul h₁).sub (hsub.mul h₂)
  have hD₀ : D c ≠ 0 :=
    ((hAW s₀ ((mem_ball_zero_iff.mp hs₀).trans_le he₃)).2.2 z₀ hz₀).1
  have hT : ContinuousAt T c :=
    h₀.add (((continuousAt_const.mul hsub).mul (h₁.pow 2)).div hD hD₀)
  let B : ℝ := ‖T c‖ + 1
  have hB : 0 ≤ B := by positivity
  have hlocal : ∀ᶠ x : ℂ × (ℂ × ℂ) in 𝓝 c,
      x.1 ∈ ball (0 : ℂ) ε ∧ x.2.1 ∈ upperHalf ∧ x.2.2 ∈ lowerHalf ∧
        D x ≠ 0 ∧ ‖T x‖ ≤ B := by
    have hs : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => x.1) c := continuous_fst.continuousAt
    have hz : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => x.2.1) c :=
      (continuous_fst.comp continuous_snd).continuousAt
    have hw : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => x.2.2) c :=
      (continuous_snd.comp continuous_snd).continuousAt
    filter_upwards [hs.eventually_mem (isOpen_ball.mem_nhds hs₀),
      hz.eventually_mem (isOpen_upperHalf.mem_nhds hz₀),
      hw.eventually_mem (isOpen_lowerHalf.mem_nhds hw₀), hD.eventually_ne hD₀,
      hT.eventually_mem (ball_mem_nhds (T c) zero_lt_one)] with x hsx hzx hwx hDx hTx
    refine ⟨hsx, hzx, hwx, hDx, ?_⟩
    have hn : ‖T x‖ ≤ ‖T x - T c‖ + ‖T c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (T x - T c) (T c)
    rw [mem_ball, dist_eq_norm] at hTx
    dsimp only [B]
    linarith
  obtain ⟨a, ha, hloc⟩ := Metric.eventually_nhds_iff_ball.mp hlocal
  have hrad : 0 < a / 4 := by positivity
  have hpar : ball s₀ (a / 4) ⊆ ball (0 : ℂ) ε := by
    intro s hs
    have hsa : dist s s₀ < a := by linarith [mem_ball.mp hs]
    have hx : (s, (z₀, conj z₀)) ∈ ball c a := by
      simp only [mem_ball, Prod.dist_eq, c, dist_self]
      exact max_lt_iff.mpr ⟨hsa, ha⟩
    exact (hloc _ hx).1
  have hspace : ball z₀ (a / 4) ⊆ upperHalf := by
    intro z hz
    have hza : dist z z₀ < a := by linarith [mem_ball.mp hz]
    have hx : (s₀, (z, conj z₀)) ∈ ball c a := by
      simp only [mem_ball, Prod.dist_eq, c, dist_self]
      exact max_lt_iff.mpr ⟨ha, max_lt_iff.mpr ⟨hza, ha⟩⟩
    exact (hloc _ hx).2.1
  refine ⟨a / 4, 2 * B / (a / 4), hrad, by positivity, hpar, hspace, ?_⟩
  intro s hs z hz
  let v : ℂ × ℂ := (z, conj z)
  let v₀ : ℂ × ℂ := (z₀, conj z₀)
  let Rs : ℂ × ℂ → ℂ := fun x => T (s, x)
  have hsa : dist s s₀ < a := by linarith [mem_ball.mp hs]
  have hv : dist v v₀ < a / 4 := by
    simpa only [v, v₀, Prod.dist_eq, dist_conj_conj, max_self] using mem_ball.mp hz
  have hdata (x : ℂ × ℂ) (hx : dist x v₀ < a) :
      s ∈ ball (0 : ℂ) ε ∧ x.1 ∈ upperHalf ∧ x.2 ∈ lowerHalf ∧
        D (s, x) ≠ 0 ∧ ‖Rs x‖ ≤ B := by
    apply hloc (s, x)
    change max (dist s s₀) (dist x v₀) < a
    exact max_lt_iff.mpr ⟨hsa, hx⟩
  have hnear (x : ℂ × ℂ) (hx : x ∈ ball v (a / 4)) : dist x v₀ < a := by
    have h := mem_ball.mp hx
    linarith [dist_triangle x v v₀]
  have hs₂ : s ∈ ball (0 : ℂ) ε₂ := ball_subset_ball he₂ (hpar hs)
  have hd₀ : DifferentiableOn ℂ (A s) lowerHalf := by
    simpa only [iteratedDeriv_zero] using (hjetd 0 (by decide)).2.1 s hs₂
  have hd₁ : DifferentiableOn ℂ (deriv (A s)) lowerHalf := by
    simpa only [iteratedDeriv_one] using (hjetd 1 (by decide)).2.1 s hs₂
  have hd₂ : DifferentiableOn ℂ (deriv (deriv (A s))) lowerHalf := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (hjetd 2 (by decide)).2.1 s hs₂
  have hRs : DifferentiableOn ℂ Rs (ball v (a / 4)) := by
    intro x hx
    have hxx := hdata x (hnear x hx)
    have h₀ : DifferentiableAt ℂ (fun y : ℂ × ℂ => A s y.2) x :=
      (hd₀.differentiableAt (isOpen_lowerHalf.mem_nhds hxx.2.2.1)).comp x
        differentiableAt_snd
    have h₁ : DifferentiableAt ℂ (fun y : ℂ × ℂ => deriv (A s) y.2) x :=
      (hd₁.differentiableAt (isOpen_lowerHalf.mem_nhds hxx.2.2.1)).comp x
        differentiableAt_snd
    have h₂ : DifferentiableAt ℂ (fun y : ℂ × ℂ => deriv (deriv (A s)) y.2) x :=
      (hd₂.differentiableAt (isOpen_lowerHalf.mem_nhds hxx.2.2.1)).comp x
        differentiableAt_snd
    have hdif : DifferentiableAt ℂ (fun y : ℂ × ℂ => y.1 - y.2) x :=
      differentiableAt_fst.sub differentiableAt_snd
    have hden := (h₁.const_mul 2).sub (hdif.mul h₂)
    have hnum := (hdif.const_mul 2).mul (h₁.fun_pow 2)
    let U : ℂ × ℂ → ℂ := fun y => A s y.2 +
      2 * (y.1 - y.2) * deriv (A s) y.2 ^ 2 *
        (2 * deriv (A s) y.2 - (y.1 - y.2) * deriv (deriv (A s)) y.2)⁻¹
    have hU : DifferentiableAt ℂ U x :=
      h₀.add (hnum.mul (hden.inv hxx.2.2.2.1))
    have heq : Rs = U := by
      funext y
      simp only [Rs, T, D, U, div_eq_mul_inv]
    rw [heq]
    exact hU.differentiableWithinAt
  have hRv : ‖Rs v‖ ≤ B := (hdata v (by linarith)).2.2.2.2
  have hmaps : MapsTo Rs (ball v (a / 4)) (closedBall (Rs v) (2 * B)) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm]
    have hxB := (hdata x (hnear x hx)).2.2.2.2
    exact (norm_sub_le (Rs x) (Rs v)).trans (by linarith)
  have hC := Complex.norm_fderiv_le_div_of_mapsTo_ball hRs hmaps hrad
  have hRc : DifferentiableAt ℂ Rs v :=
    hRs.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrad))
  let d : ℂ →L[ℝ] ℂ × ℂ :=
    (ContinuousLinearMap.id ℝ ℂ).prod (conjCLE : ℂ →L[ℝ] ℂ)
  have hd : ‖d‖ ≤ 1 := by
    apply d.opNorm_le_bound zero_le_one
    intro u
    change max ‖u‖ ‖conj u‖ ≤ 1 * ‖u‖
    simpa only [norm_conj, max_self, one_mul] using (le_rfl : ‖u‖ ≤ ‖u‖)
  have hcomp : HasFDerivAt (Rs ∘ d)
      (((fderiv ℂ Rs v).restrictScalars ℝ).comp d) z :=
    (hRc.hasFDerivAt.restrictScalars ℝ).comp z d.hasFDerivAt
  have heq : A s =ᶠ[𝓝 z] Rs ∘ d := by
    filter_upwards [isOpen_upperHalf.mem_nhds (hspace hz)] with u hu
    change A s u = A s (conj u) + 2 * (u - conj u) * deriv (A s) (conj u) ^ 2 /
      (2 * deriv (A s) (conj u) - (u - conj u) * deriv (deriv (A s)) (conj u))
    exact ((hAW s ((mem_ball_zero_iff.mp (hpar hs)).trans_le he₃)).2.2 u hu).2
  rw [(hcomp.congr_of_eventuallyEq heq).fderiv]
  calc
    ‖((fderiv ℂ Rs v).restrictScalars ℝ).comp d‖ ≤
        ‖(fderiv ℂ Rs v).restrictScalars ℝ‖ * ‖d‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(fderiv ℂ Rs v).restrictScalars ℝ‖ := by
      nlinarith [norm_nonneg ((fderiv ℂ Rs v).restrictScalars ℝ)]
    _ = ‖fderiv ℂ Rs v‖ := ContinuousLinearMap.norm_restrictScalars _
    _ ≤ 2 * B / (a / 4) := hC

private theorem asymmetric_bounded_center_closeness
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε →
        IsKQCNormalizedPlane (canonicalBiparameterFamily R p q s t) 3) ∧
      ∀ s₀ ∈ ball (0 : ℂ) ε, ∀ T : ℝ, 0 < T →
        ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ball s₀ r ⊆ ball (0 : ℂ) ε ∧
          ∀ s ∈ ball s₀ r, ∀ w : ℂ, ‖w‖ ≤ T →
            ‖canonicalBiparameterFamily R p q s 0 w -
              canonicalBiparameterFamily R p q s₀ 0 w‖ ≤ C * ‖s - s₀‖ := by
  obtain ⟨ε₁, hε₁, _, hfirst, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  obtain ⟨ε₂, hε₂, hsharp, _⟩ := canonicalBiparameterFamily_bounded_closeness R p hp q
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have he₁ : ε ≤ ε₁ := min_le_left _ _
  have he₂ : ε ≤ ε₂ := min_le_right _ _
  refine ⟨ε, hε, fun s t hs ht => hsharp s t (hs.trans_le he₂) (ht.trans_le he₂), ?_⟩
  intro s₀ hs₀ T hT
  obtain ⟨a, ha, haP⟩ := Metric.isOpen_iff.mp isOpen_ball s₀ hs₀
  let M : ℝ := max (lambdaInv (3 * quadLambda T)) 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hzero : ‖(0 : ℂ)‖ < ε₁ := by simpa only [norm_zero] using hε₁
  have hzero₂ : ‖(0 : ℂ)‖ < ε₂ := by simpa only [norm_zero] using hε₂
  refine ⟨a / 2, M / (a / 2), by positivity, by positivity,
    (ball_subset_ball (by linarith : a / 2 ≤ a)).trans haP, ?_⟩
  intro s hs w hw
  have hg : DifferentiableOn ℂ (fun v => canonicalBiparameterFamily R p q v 0 w)
      (ball s₀ a) :=
    (hfirst 0 hzero w).mono (haP.trans (ball_subset_ball he₁))
  have hb (v : ℂ) (hv : v ∈ ball s₀ a) :
      ‖canonicalBiparameterFamily R p q v 0 w‖ ≤ M :=
    (UniversalTeichmuller.ut2_nb_upper
      (hsharp v 0 ((mem_ball_zero_iff.mp (haP hv)).trans_le he₂) hzero₂) hT hw).trans
        (le_max_left _ _)
  exact norm_sub_center_le_of_holomorphic_bound ha hg hb
    (by simpa only [mem_ball, dist_eq_norm] using hs)

/-- A fixed disk in the actual image at any parameter center remains in
every nearby true image, with bounded actual inverse and relative family. -/
theorem canonicalBiparameterFamily_asymmetric_local_image_disks
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s₀ ∈ ball (0 : ℂ) ε, ∀ z₀ ∈ upperHalf,
      ∃ r d B : ℝ, 0 < r ∧ 0 < d ∧ 0 < B ∧ ball s₀ r ⊆ ball (0 : ℂ) ε ∧
        ∀ s ∈ ball s₀ r,
          let A := canonicalBiparameterFamily R p q s 0
          let w₀ := canonicalBiparameterFamily R p q s₀ 0 z₀
          closedBall w₀ d ⊆ A '' upperHalf ∧
          (∀ w ∈ closedBall w₀ d, ‖Function.invFunOn A upperHalf w‖ ≤ B) ∧
          ∀ t ∈ ball (0 : ℂ) ε, ∀ w ∈ closedBall w₀ d,
            ‖canonicalBiparameterFamily R p q s t (Function.invFunOn A upperHalf w)‖ ≤ B := by
  obtain ⟨ε, hε, hsharp, hclose⟩ := asymmetric_bounded_center_closeness R p hp q
  have hzero : ‖(0 : ℂ)‖ < ε := by simpa only [norm_zero] using hε
  refine ⟨ε, hε, ?_⟩
  intro s₀ hs₀ z₀ hz₀
  let A₀ := canonicalBiparameterFamily R p q s₀ 0
  let w₀ := A₀ z₀
  have hqc₀ : IsKQCNormalizedPlane A₀ 3 := hsharp s₀ 0 (mem_ball_zero_iff.mp hs₀) hzero
  have hD₀ : IsOpen (A₀ '' upperHalf) :=
    isOpen_image_of_isKQC (ac_t_isKQC_restrict hqc₀.1 isOpen_upperHalf (subset_univ _))
  obtain ⟨b, hb, hbD⟩ := Metric.isOpen_iff.mp hD₀ w₀ (mem_image_of_mem A₀ hz₀)
  let U : ℝ := ‖w₀‖ + b + 1
  have hU : 0 < U := by dsimp only [U]; positivity
  let T : ℝ := max (lambdaInv (3 * quadLambda U)) 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨a, C, ha, hC, haP, hlin⟩ := hclose s₀ hs₀ T hT
  let r : ℝ := min a (b / (8 * C))
  have hr : 0 < r := lt_min ha (by positivity)
  have hrP : ball s₀ r ⊆ ball (0 : ℂ) ε :=
    (ball_subset_ball (min_le_left _ _)).trans haP
  let B : ℝ := max T (max (lambdaInv (3 * quadLambda T)) 1)
  have hB : 0 < B := hT.trans_le (le_max_left _ _)
  refine ⟨r, b / 4, B, hr, by positivity, hB, hrP, ?_⟩
  intro s hs
  dsimp only
  let A := canonicalBiparameterFamily R p q s 0
  have hsε : ‖s‖ < ε := mem_ball_zero_iff.mp (hrP hs)
  have hqc : IsKQCNormalizedPlane A 3 := hsharp s 0 hsε hzero
  have hsa : s ∈ ball s₀ a := ball_subset_ball (min_le_left _ _) hs
  have hsmall : C * ‖s - s₀‖ < b / 8 := by
    have hsr : ‖s - s₀‖ < b / (8 * C) := by
      have h := mem_ball.mp hs
      rw [dist_eq_norm] at h
      exact h.trans_le (min_le_right _ _)
    have h := (lt_div_iff₀ (by positivity : 0 < 8 * C)).mp hsr
    nlinarith
  have hbounded (w : ℂ) (hw : w ∈ closedBall w₀ (b / 4)) : ‖w‖ ≤ U := by
    rw [mem_closedBall, dist_eq_norm] at hw
    have hn := norm_sub_norm_le w w₀
    dsimp only [U]
    linarith
  have hprebound (w : ℂ) (hw : w ∈ closedBall w₀ (b / 4)) (u : ℂ) (hu : A u = w) :
      ‖u‖ ≤ T :=
    (UniversalTeichmuller.ut2_nb_lower hqc hU
      (by rw [hu]; exact hbounded w hw)).trans (le_max_left _ _)
  have hpreupper (w : ℂ) (hw : w ∈ closedBall w₀ (b / 4)) (u : ℂ) (hu : A u = w) :
      u ∈ upperHalf := by
    have huT := hprebound w hw u hu
    have hdiff : ‖A u - A₀ u‖ < b / 8 := (hlin s hsa u huT).trans_lt hsmall
    have hw₀ : ‖w - w₀‖ ≤ b / 4 := by
      simpa only [mem_closedBall, dist_eq_norm] using hw
    have huD : A₀ u ∈ ball w₀ b := by
      rw [mem_ball, dist_eq_norm]
      have htriangle := norm_sub_le_norm_sub_add_norm_sub (A₀ u) (A u) w₀
      rw [norm_sub_rev (A₀ u) (A u)] at htriangle
      have hwA : ‖A u - w₀‖ ≤ b / 4 := by rwa [hu]
      linarith
    obtain ⟨v, hv, hve⟩ := hbD huD
    have hvu : v = u := hqc₀.1.2.2.1.2.1 (mem_univ _) (mem_univ _) hve
    rwa [hvu] at hv
  have hball : closedBall w₀ (b / 4) ⊆ A '' upperHalf := by
    intro w hw
    have hsurj : w ∈ A '' univ := by rw [hqc.2.1]; exact mem_univ _
    obtain ⟨u, _, hu⟩ := hsurj
    exact ⟨u, hpreupper w hw u hu, hu⟩
  refine ⟨hball, ?_, ?_⟩
  · intro w hw
    exact (hprebound w hw _ (Function.invFunOn_eq (hball hw))).trans (le_max_left _ _)
  · intro t ht w hw
    have hi : ‖Function.invFunOn A upperHalf w‖ ≤ T :=
      hprebound w hw _ (Function.invFunOn_eq (hball hw))
    exact (UniversalTeichmuller.ut2_nb_upper
      (hsharp s t hsε (mem_ball_zero_iff.mp ht)) hT hi).trans
        ((le_max_left _ _).trans (le_max_right _ _))

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
