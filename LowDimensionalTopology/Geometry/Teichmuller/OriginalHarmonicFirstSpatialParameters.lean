module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicBiparameterFamily
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicConformalQuotient
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicSpatialControl
public import Mathlib.Analysis.Calculus.ParametricCircleIntegral
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Parameter holomorphy of the actual first spatial derivatives

Spatial difference quotients give measurable directional derivatives on
the parameter circles. The finite spatial bound then justifies one real
directional derivative under the original parameter Cauchy integral.
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

private theorem real_affine_line_hasDerivAt (z v : ℂ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => z + x • v) v u := by
  rw [hasDerivAt_iff_hasFDerivAt]
  refine .of_isLittleOTVS ((Asymptotics.IsLittleOTVS.zero _ _).congr_left ?_)
  intro x
  simp only [Pi.zero_apply, ContinuousLinearMap.toSpanSingleton_apply, sub_smul]
  abel

private theorem first_directional_parameter_stronglyMeasurable
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {ε : ℝ}
    (hparam : ∀ t ∈ ball (0 : ℂ) ε, ∀ w : ℂ,
      DifferentiableOn ℂ (fun s => canonicalBiparameterFamily R p q s t w) (ball 0 ε))
    (hC1 : ∀ s t : ℂ, s ∈ ball (0 : ℂ) ε → t ∈ ball (0 : ℂ) ε →
      ContDiffOn ℝ 1 (canonicalBiparameterFamily R p q s t) (upperHalf ∪ lowerHalf))
    {t z : ℂ} (ht : t ∈ ball (0 : ℂ) ε) (hz : z ∈ upperHalf) (v : ℂ) :
    StronglyMeasurable (fun s : ball (0 : ℂ) ε =>
      fderiv ℝ (canonicalBiparameterFamily R p q s t) z v) := by
  obtain ⟨a, ha⟩ := Filter.exists_seq_tendsto (𝓝[>] (0 : ℝ))
  let F : ℕ → ball (0 : ℂ) ε → ℂ := fun n s => (a n)⁻¹ •
    (canonicalBiparameterFamily R p q s t (z + a n • v) -
      canonicalBiparameterFamily R p q s t z)
  have hFm (n : ℕ) : StronglyMeasurable (F n) := by
    have h₁ : Continuous (fun s : ball (0 : ℂ) ε =>
        canonicalBiparameterFamily R p q s t (z + a n • v)) :=
      (hparam t ht _).continuousOn.domRestrict
    have h₂ : Continuous (fun s : ball (0 : ℂ) ε =>
        canonicalBiparameterFamily R p q s t z) :=
      (hparam t ht z).continuousOn.domRestrict
    exact ((h₁.sub h₂).const_smul ((a n)⁻¹)).stronglyMeasurable
  apply stronglyMeasurable_of_tendsto atTop hFm
  rw [tendsto_pi_nhds]
  intro s
  have hd : DifferentiableAt ℝ (canonicalBiparameterFamily R p q s t) z :=
    (hC1 s t s.property ht).differentiableOn_one.differentiableAt
      ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds (Or.inl hz))
  have hline : HasDerivAt (fun x : ℝ => z + x • v) v 0 :=
    real_affine_line_hasDerivAt z v 0
  have hdir : HasDerivAt
      (fun x : ℝ => canonicalBiparameterFamily R p q s t (z + x • v))
      (fderiv ℝ (canonicalBiparameterFamily R p q s t) z v) 0 := by
    simpa only [Function.comp_def] using
      hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp only [zero_smul, add_zero])
  simpa only [F, Function.comp_def, zero_add, zero_smul, add_zero] using
    hdir.tendsto_slope_zero_right.comp ha

set_option maxHeartbeats 800000 in
private theorem first_directional_parameter_cauchy
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {ε : ℝ}
    (hparam : ∀ t ∈ ball (0 : ℂ) ε, ∀ w : ℂ,
      DifferentiableOn ℂ (fun s => canonicalBiparameterFamily R p q s t w) (ball 0 ε))
    (hC1 : ∀ s t : ℂ, s ∈ ball (0 : ℂ) ε → t ∈ ball (0 : ℂ) ε →
      ContDiffOn ℝ 1 (canonicalBiparameterFamily R p q s t) (upperHalf ∪ lowerHalf))
    {t z a : ℂ} (ht : t ∈ ball (0 : ℂ) ε) (hz : z ∈ upperHalf)
    {r ρ C : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hcircle : closedBall a r ⊆ ball (0 : ℂ) ε)
    (hspace : ball z ρ ⊆ upperHalf)
    (hbound : ∀ η ∈ sphere a r, ∀ w ∈ ball z ρ,
      ‖fderiv ℝ (canonicalBiparameterFamily R p q η t) w‖ ≤ C)
    (v : ℂ) (hv : ‖v‖ = 1) :
    CircleIntegrable (fun η => fderiv ℝ (canonicalBiparameterFamily R p q η t) z v) a r ∧
      ∀ b ∈ ball a r,
        fderiv ℝ (canonicalBiparameterFamily R p q b t) z v =
          (2 * Real.pi * I : ℂ)⁻¹ • ∮ η in C(a, r),
            (η - b)⁻¹ • fderiv ℝ (canonicalBiparameterFamily R p q η t) z v := by
  let D : ℂ → ℂ := fun η => fderiv ℝ (canonicalBiparameterFamily R p q η t) z v
  have hηP (η : ℂ) (hη : η ∈ sphere a r) : η ∈ ball (0 : ℂ) ε :=
    hcircle (sphere_subset_closedBall hη)
  have hγ (θ : ℝ) : circleMap a r θ ∈ sphere a r := by
    simpa only [abs_of_pos hr] using circleMap_mem_sphere' a r θ
  have hγc : Continuous (fun θ : ℝ =>
      (⟨circleMap a r θ, hηP _ (hγ θ)⟩ : ball (0 : ℂ) ε)) :=
    (continuous_circleMap a r).subtype_mk _
  have hDm : StronglyMeasurable (fun θ : ℝ => D (circleMap a r θ)) :=
    (first_directional_parameter_stronglyMeasurable R p q hparam hC1 ht hz v).comp_measurable
      hγc.measurable
  dsimp only [D] at hDm
  clear D
  generalize hfamily : canonicalBiparameterFamily R p q = f at *
  let D : ℂ → ℂ := fun η => fderiv ℝ (f η t) z v
  have hDnorm (η : ℂ) (hη : η ∈ sphere a r) : ‖D η‖ ≤ C := by
    calc
      ‖D η‖ ≤ ‖fderiv ℝ (f η t) z‖ * ‖v‖ :=
        (fderiv ℝ (f η t) z).le_opNorm v
      _ ≤ C := by rw [hv, mul_one]; exact hbound η hη z (mem_ball_self hρ)
  have hDi : CircleIntegrable D a r := by
    rw [CircleIntegrable, intervalIntegrable_iff]
    have hconst : IntegrableOn (fun _ : ℝ => C) (Set.uIoc 0 (2 * Real.pi)) volume :=
      intervalIntegrable_iff.mp intervalIntegrable_const
    apply hconst.norm.mono' hDm.aestronglyMeasurable
    exact Eventually.of_forall fun θ => by
      simpa only [Real.norm_of_nonneg hC] using hDnorm _ (hγ θ)
  refine ⟨hDi, ?_⟩
  intro b hb
  have hbs : b ∉ sphere a r := by
    simpa only [mem_sphere] using (ne_of_lt (mem_ball.mp hb))
  have hc : ContinuousOn (fun η : ℂ => (η - b)⁻¹) (sphere a r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun η hη =>
      sub_ne_zero.mpr (ne_of_mem_of_not_mem hη hbs)
  let F : ℝ → ℂ → ℂ := fun u η =>
    (η - b)⁻¹ * f η t (z + u • v)
  let F' : ℝ → ℂ → ℂ := fun u η =>
    (η - b)⁻¹ * fderiv ℝ (f η t) (z + u • v) v
  have hFcont (u : ℝ) : ContinuousOn (F u) (sphere a r) :=
    hc.mul ((hparam t ht (z + u • v)).continuousOn.mono hηP)
  have hFmeas : ∀ᶠ u : ℝ in 𝓝 0,
      AEStronglyMeasurable (fun θ : ℝ => F u (circleMap a r θ))
        (volume.restrict (Set.uIoc 0 (2 * Real.pi))) :=
    Eventually.of_forall fun u =>
      ((hFcont u).comp_continuous (continuous_circleMap a r) hγ).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (fun θ : ℝ => F' 0 (circleMap a r θ))
      (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    simp only [F', zero_smul, add_zero]
    exact ((hc.comp_continuous (continuous_circleMap a r) hγ).aestronglyMeasurable).fun_mul
      hDm.aestronglyMeasurable
  have hw (u : ℝ) (hu : u ∈ ball (0 : ℝ) ρ) : z + u • v ∈ ball z ρ := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv,
      mul_one, sub_zero] using hu
  have hdiff (η : ℂ) (hη : η ∈ sphere a r) (u : ℝ) (hu : u ∈ ball (0 : ℝ) ρ) :
      HasDerivAt (fun x : ℝ => F x η) (F' u η) u := by
    have hd : DifferentiableAt ℝ (f η t) (z + u • v) :=
      (hC1 η t (hηP η hη) ht).differentiableOn_one.differentiableAt
        ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds (Or.inl (hspace (hw u hu))))
    have hline : HasDerivAt (fun x : ℝ => z + x • v) v u :=
      real_affine_line_hasDerivAt z v u
    simpa only [F, F', Function.comp_def] using
      (hd.hasFDerivAt.comp_hasDerivAt u hline).const_mul ((η - b)⁻¹)
  have hnorm (η : ℂ) (hη : η ∈ sphere a r) (u : ℝ) (hu : u ∈ ball (0 : ℝ) ρ) :
      ‖F' u η‖ ≤ C * ‖(η - b)⁻¹‖ := by
    dsimp only [F']
    rw [norm_mul]
    have hlin := (fderiv ℝ (f η t) (z + u • v)).le_opNorm v
    rw [hv, mul_one] at hlin
    have hle := hlin.trans (hbound η hη _ (hw u hu))
    simpa only [mul_comm C] using mul_le_mul_of_nonneg_left hle (norm_nonneg ((η - b)⁻¹))
  obtain ⟨_, hI⟩ := hasDerivAt_circleIntegral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun η => C * ‖(η - b)⁻¹‖)
    (ball_mem_nhds (0 : ℝ) hρ) hFmeas ((hFcont 0).circleIntegrable hr.le) hF'meas
    (by simpa only [abs_of_pos hr] using hnorm) ((hc.norm.const_mul C).circleIntegrable hr.le)
    (by simpa only [abs_of_pos hr] using hdiff)
  have hformula (u : ℝ) :
      (2 * Real.pi * I : ℂ)⁻¹ • (∮ η in C(a, r), F u η) =
        f b t (z + u • v) := by
    have hfCauchy := (hparam t ht (z + u • v)).diffContOnCl_ball hcircle
    simpa only [F, smul_eq_mul] using
      hfCauchy.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hb
  have hactual : HasDerivAt
      (fun u : ℝ => f b t (z + u • v))
      ((2 * Real.pi * I : ℂ)⁻¹ * ∮ η in C(a, r), F' 0 η) 0 := by
    apply (hI.const_mul ((2 * Real.pi * I : ℂ)⁻¹)).congr_of_eventuallyEq
    exact Eventually.of_forall fun u => by simpa only [smul_eq_mul] using (hformula u).symm
  have hdb : DifferentiableAt ℝ (f b t) z :=
    (hC1 b t (hcircle (ball_subset_closedBall hb)) ht).differentiableOn_one.differentiableAt
      ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds (Or.inl hz))
  have hline : HasDerivAt (fun u : ℝ => z + u • v) v 0 :=
    real_affine_line_hasDerivAt z v 0
  have hdir : HasDerivAt
      (fun u : ℝ => f b t (z + u • v))
      (fderiv ℝ (f b t) z v) 0 := by
    simpa only [Function.comp_def] using
      hdb.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp only [zero_smul, add_zero])
  simpa only [F', zero_smul, add_zero, smul_eq_mul] using hdir.unique hactual

private theorem first_directional_parameter_holomorphic
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {ε : ℝ}
    (hparam : ∀ t ∈ ball (0 : ℂ) ε, ∀ w : ℂ,
      DifferentiableOn ℂ (fun s => canonicalBiparameterFamily R p q s t w) (ball 0 ε))
    (hC1 : ∀ s t : ℂ, s ∈ ball (0 : ℂ) ε → t ∈ ball (0 : ℂ) ε →
      ContDiffOn ℝ 1 (canonicalBiparameterFamily R p q s t) (upperHalf ∪ lowerHalf))
    (hlocal : ∀ s₀ ∈ ball (0 : ℂ) ε, ∀ z₀ ∈ upperHalf,
      ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
        ball s₀ r ⊆ ball (0 : ℂ) ε ∧ ball z₀ r ⊆ upperHalf ∧
        ∀ s ∈ ball s₀ r, ∀ t ∈ ball (0 : ℂ) ε, ∀ z ∈ ball z₀ r,
          ‖fderiv ℝ (canonicalBiparameterFamily R p q s t) z‖ ≤ C)
    {t z : ℂ} (ht : t ∈ ball (0 : ℂ) ε) (hz : z ∈ upperHalf) (v : ℂ) (hv : ‖v‖ = 1) :
    DifferentiableOn ℂ
      (fun s => fderiv ℝ (canonicalBiparameterFamily R p q s t) z v) (ball 0 ε) := by
  intro a ha
  obtain ⟨r, C, hr, hC, hrP, hrZ, hbound⟩ := hlocal a ha z hz
  have hhalf : 0 < r / 2 := by positivity
  have hcircle : closedBall a (r / 2) ⊆ ball (0 : ℂ) ε :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans hrP
  have hcircle_bound : ∀ η ∈ sphere a (r / 2), ∀ w ∈ ball z r,
      ‖fderiv ℝ (canonicalBiparameterFamily R p q η t) w‖ ≤ C := by
    intro η hη w hw
    have hηr : η ∈ ball a r :=
      (closedBall_subset_ball (by linarith : r / 2 < r)) (sphere_subset_closedBall hη)
    exact hbound η hηr t ht w hw
  obtain ⟨hDi, hformula⟩ := first_directional_parameter_cauchy R p q hparam hC1 ht hz
    hhalf hr hC hcircle hrZ hcircle_bound v hv
  have hnot : a ∉ sphere a |r / 2| := by
    simpa only [mem_sphere, dist_self, abs_of_pos hhalf] using ne_of_lt hhalf
  have hhol := (Complex.hasDerivAt_circleIntegral_sub_inv_smul hDi hnot).const_mul
    ((2 * Real.pi * I : ℂ)⁻¹)
  have heq : (fun s => fderiv ℝ (canonicalBiparameterFamily R p q s t) z v) =ᶠ[𝓝 a]
      fun b => (2 * Real.pi * I : ℂ)⁻¹ * ∮ η in C(a, r / 2),
        (η - b)⁻¹ • fderiv ℝ (canonicalBiparameterFamily R p q η t) z v :=
    Filter.mem_of_superset (ball_mem_nhds a hhalf) fun b hb => by
      change fderiv ℝ (canonicalBiparameterFamily R p q b t) z v = _
      simpa only [smul_eq_mul] using hformula b hb
  exact (hhol.differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt

private theorem upper_active_first_spatial_parameters
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → ∀ z ∈ upperHalf,
      DifferentiableOn ℂ (fun s => dz (canonicalBiparameterFamily R p q s t) z) (ball 0 ε) ∧
      DifferentiableOn ℂ (fun s => dzbar (canonicalBiparameterFamily R p q s t) z) (ball 0 ε) := by
  obtain ⟨ε₁, hε₁, hC1, _, hlocal, _⟩ :=
    canonicalBiparameterFamily_spatial_c1_compact_control R p hp q
  obtain ⟨ε₂, hε₂, _, hfirst, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have he₁ : ε ≤ ε₁ := min_le_left _ _
  have he₂ : ε ≤ ε₂ := min_le_right _ _
  have hC1' : ∀ s t : ℂ, s ∈ ball (0 : ℂ) ε → t ∈ ball (0 : ℂ) ε →
      ContDiffOn ℝ 1 (canonicalBiparameterFamily R p q s t) (upperHalf ∪ lowerHalf) :=
    fun s t hs ht => hC1 s t ((mem_ball_zero_iff.mp hs).trans_le he₁)
      ((mem_ball_zero_iff.mp ht).trans_le he₁)
  have hparam : ∀ t ∈ ball (0 : ℂ) ε, ∀ w : ℂ,
      DifferentiableOn ℂ (fun s => canonicalBiparameterFamily R p q s t w) (ball 0 ε) :=
    fun t ht w => (hfirst t ((mem_ball_zero_iff.mp ht).trans_le he₂) w).mono
      (ball_subset_ball he₂)
  have hlocal' : ∀ s₀ ∈ ball (0 : ℂ) ε, ∀ z₀ ∈ upperHalf,
      ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
        ball s₀ r ⊆ ball (0 : ℂ) ε ∧ ball z₀ r ⊆ upperHalf ∧
        ∀ s ∈ ball s₀ r, ∀ t ∈ ball (0 : ℂ) ε, ∀ z ∈ ball z₀ r,
          ‖fderiv ℝ (canonicalBiparameterFamily R p q s t) z‖ ≤ C := by
    intro s₀ hs₀ z₀ hz₀
    obtain ⟨r, C, hr, hC, _, hrZ, hbound⟩ :=
      hlocal s₀ (ball_subset_ball he₁ hs₀) z₀ hz₀
    obtain ⟨a, ha, haP⟩ := Metric.isOpen_iff.mp isOpen_ball s₀ hs₀
    refine ⟨min r a, C, lt_min hr ha, hC,
      (ball_subset_ball (min_le_right _ _)).trans haP,
      (ball_subset_ball (min_le_left _ _)).trans hrZ, ?_⟩
    intro s hs t ht z hz
    exact hbound s (ball_subset_ball (min_le_left _ _) hs) t (ball_subset_ball he₁ ht)
      z (ball_subset_ball (min_le_left _ _) hz)
  refine ⟨ε, hε, ?_⟩
  intro t ht z hz
  let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
  have h₁ := first_directional_parameter_holomorphic R p q hparam hC1' hlocal'
    (mem_ball_zero_iff.mpr ht) hz 1 (by simp only [norm_one])
  have hI := first_directional_parameter_holomorphic R p q hparam hC1' hlocal'
    (mem_ball_zero_iff.mpr ht) hz I norm_I
  constructor
  · change DifferentiableOn ℂ (fun s =>
      (fderiv ℝ (canonicalBiparameterFamily R p q s t) z 1 -
        I * fderiv ℝ (canonicalBiparameterFamily R p q s t) z I) / 2) (ball 0 ε)
    exact (h₁.sub (hI.const_mul I)).div_const 2
  · change DifferentiableOn ℂ (fun s =>
      (fderiv ℝ (canonicalBiparameterFamily R p q s t) z 1 +
        I * fderiv ℝ (canonicalBiparameterFamily R p q s t) z I) / 2) (ball 0 ε)
    exact (h₁.add (hI.const_mul I)).div_const 2

private theorem upper_passive_first_spatial_parameters
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℂ, ‖s‖ < ε → ∀ z ∈ upperHalf,
      DifferentiableOn ℂ (fun t => dz (canonicalBiparameterFamily R p q s t) z) (ball 0 ε) ∧
      DifferentiableOn ℂ (fun t => dzbar (canonicalBiparameterFamily R p q s t) z) (ball 0 ε) := by
  obtain ⟨ε₁, hε₁, hC1, _, _, _⟩ :=
    canonicalBiparameterFamily_spatial_c1_compact_control R p hp q
  obtain ⟨ε₂, hε₂, hquot⟩ := canonicalBiparameterFamily_conformal_quotient R p hp q
  obtain ⟨ε₃, hε₃, hspec, _, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  let ε := min ε₁ (min ε₂ ε₃)
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ hε₃)
  have he₁ : ε ≤ ε₁ := min_le_left _ _
  have he₂ : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have he₃ : ε ≤ ε₃ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hε, ?_⟩
  intro s hs z hz
  let A := canonicalBiparameterFamily R p q s 0
  let G := fun t => canonicalBiparameterFamily R p q s t ∘ Function.invFunOn A upperHalf
  have hs₂ : ‖s‖ < ε₂ := hs.trans_le he₂
  obtain ⟨K, hK⟩ := (hspec s 0 (hs.trans_le he₃)
    (by simpa only [norm_zero] using hε₃)).2.1
  have hAqc : IsKQC A upperHalf K := ac_t_isKQC_restrict hK isOpen_upperHalf (subset_univ _)
  have hD : IsOpen (A '' upperHalf) := isOpen_image_of_isKQC hAqc
  have hC1s := hC1 s 0 (hs.trans_le he₁) (by simpa only [norm_zero] using hε₁)
  have hAd : DifferentiableAt ℝ A z :=
    hC1s.differentiableOn_one.differentiableAt
      ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds (Or.inl hz))
  have hparam : DifferentiableOn ℂ (fun t => deriv (G t) (A z)) (ball (0 : ℂ) ε) := by
    simpa only [iteratedDeriv_one] using
      (((hquot s hs₂).2 1).1 (A z) (mem_image_of_mem A hz)).mono (ball_subset_ball he₂)
  have hchain (t : ℂ) (ht : t ∈ ball (0 : ℂ) ε) :
      dz (canonicalBiparameterFamily R p q s t) z = deriv (G t) (A z) * dz A z ∧
      dzbar (canonicalBiparameterFamily R p q s t) z = deriv (G t) (A z) * dzbar A z := by
    have hG : DifferentiableAt ℂ (G t) (A z) :=
      (((hquot s hs₂).1 t (ball_subset_ball he₂ ht)).1).differentiableAt
        (hD.mem_nhds (mem_image_of_mem A hz))
    have heq : canonicalBiparameterFamily R p q s t =ᶠ[𝓝 z] (G t) ∘ A := by
      filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
      change canonicalBiparameterFamily R p q s t w =
        canonicalBiparameterFamily R p q s t (Function.invFunOn A upperHalf (A w))
      rw [hAqc.2.2.1.2.1.leftInvOn_invFunOn hw]
    have hdz : dz (canonicalBiparameterFamily R p q s t) z = dz ((G t) ∘ A) z := by
      unfold dz
      rw [heq.fderiv_eq (𝕜 := ℝ)]
    have hdzbar : dzbar (canonicalBiparameterFamily R p q s t) z = dzbar ((G t) ∘ A) z := by
      unfold dzbar
      rw [heq.fderiv_eq (𝕜 := ℝ)]
    exact ⟨hdz.trans (eq6_5 hAd hG).1, hdzbar.trans (eq6_5 hAd hG).2⟩
  exact ⟨(hparam.mul_const (dz A z)).congr (fun t ht => (hchain t ht).1),
    (hparam.mul_const (dzbar A z)).congr (fun t ht => (hchain t ht).2)⟩

/-- The same normalized family is spatially C1 off the real axis. Its two
first spatial derivatives are separately holomorphic on one common
parameter bidisk, and its real derivative is bounded on each compact
upper-half-plane set after shrinking only the compact parameter radius. -/
theorem canonicalBiparameterFamily_first_spatial_parameter_control
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    let f := canonicalBiparameterFamily R p q
    ∃ ε : ℝ, 0 < ε ∧
      (∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε →
        ContDiffOn ℝ 1 (f s t) (upperHalf ∪ lowerHalf)) ∧
      (∀ t : ℂ, ‖t‖ < ε → ∀ z ∈ upperHalf ∪ lowerHalf,
        DifferentiableOn ℂ (fun s => dz (f s t) z) (ball 0 ε) ∧
        DifferentiableOn ℂ (fun s => dzbar (f s t) z) (ball 0 ε)) ∧
      (∀ s : ℂ, ‖s‖ < ε → ∀ z ∈ upperHalf ∪ lowerHalf,
        DifferentiableOn ℂ (fun t => dz (f s t) z) (ball 0 ε) ∧
        DifferentiableOn ℂ (fun t => dzbar (f s t) z) (ball 0 ε)) ∧
      ∀ K : Set ℍ, IsCompact K →
        ∃ δ C : ℝ, 0 < δ ∧ δ ≤ ε ∧ 0 ≤ C ∧
          ∀ s t : ℂ, ‖s‖ < δ → ‖t‖ < δ → ∀ z ∈ K,
            ‖fderiv ℝ (f s t) (z : ℂ)‖ ≤ C := by
  dsimp only
  obtain ⟨ε₀, hε₀, hC1, hreflect, _, hcompact⟩ :=
    canonicalBiparameterFamily_spatial_c1_compact_control R p hp q
  obtain ⟨ε₁, hε₁, hactive⟩ := upper_active_first_spatial_parameters R p hp q
  obtain ⟨ε₂, hε₂, hpassive⟩ := upper_passive_first_spatial_parameters R p hp q
  let ε := min ε₀ (min ε₁ ε₂)
  have hε : 0 < ε := lt_min hε₀ (lt_min hε₁ hε₂)
  have he₀ : ε ≤ ε₀ := min_le_left _ _
  have he₁ : ε ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have he₂ : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hact (t : ℂ) (ht : ‖t‖ < ε) (z : ℂ) (hz : z ∈ upperHalf) :
      DifferentiableOn ℂ (fun s => dz (canonicalBiparameterFamily R p q s t) z) (ball 0 ε) ∧
      DifferentiableOn ℂ (fun s => dzbar (canonicalBiparameterFamily R p q s t) z) (ball 0 ε) :=
    ⟨((hactive t (ht.trans_le he₁) z hz).1).mono (ball_subset_ball he₁),
      ((hactive t (ht.trans_le he₁) z hz).2).mono (ball_subset_ball he₁)⟩
  have hpass (s : ℂ) (hs : ‖s‖ < ε) (z : ℂ) (hz : z ∈ upperHalf) :
      DifferentiableOn ℂ (fun t => dz (canonicalBiparameterFamily R p q s t) z) (ball 0 ε) ∧
      DifferentiableOn ℂ (fun t => dzbar (canonicalBiparameterFamily R p q s t) z) (ball 0 ε) :=
    ⟨((hpassive s (hs.trans_le he₂) z hz).1).mono (ball_subset_ball he₂),
      ((hpassive s (hs.trans_le he₂) z hz).2).mono (ball_subset_ball he₂)⟩
  have hconj (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball (0 : ℂ) ε)) :
      DifferentiableOn ℂ (fun a => conj (g (conj a))) (ball (0 : ℂ) ε) := by
    intro a ha
    have hca : conj a ∈ ball (0 : ℂ) ε := by
      simpa only [mem_ball_zero_iff, norm_conj] using ha
    have hc := (hg.differentiableAt (isOpen_ball.mem_nhds hca)).conj_conj
    simpa only [conj_conj, Function.comp_def] using hc.differentiableWithinAt
  have hreflectJets (s t : ℂ) (hs : ‖s‖ < ε) (ht : ‖t‖ < ε)
      (z : ℂ) (hz : z ∈ lowerHalf) :
      dz (canonicalBiparameterFamily R p q s t) z =
        conj (dz (canonicalBiparameterFamily R p q (conj t) (conj s)) (conj z)) ∧
      dzbar (canonicalBiparameterFamily R p q s t) z =
        conj (dzbar (canonicalBiparameterFamily R p q (conj t) (conj s)) (conj z)) := by
    have hcz : conj z ∈ upperHalf := by
      change 0 < (conj z).im
      simpa only [conj_im] using neg_pos.mpr hz
    have hd : DifferentiableAt ℝ
        (canonicalBiparameterFamily R p q (conj t) (conj s)) (conj z) :=
      (hC1 (conj t) (conj s) (by simpa only [norm_conj] using ht.trans_le he₀)
        (by simpa only [norm_conj] using hs.trans_le he₀)).differentiableOn_one.differentiableAt
          ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds (Or.inl hcz))
    rw [hreflect s t (hs.trans_le he₀) (ht.trans_le he₀)]
    exact (abR_x_dz_dzbar_conj hd).2
  refine ⟨ε, hε, fun s t hs ht => hC1 s t (hs.trans_le he₀) (ht.trans_le he₀), ?_, ?_, ?_⟩
  · intro t ht z hz
    rcases hz with hz | hz
    · exact hact t ht z hz
    · have hcz : conj z ∈ upperHalf := by
        change 0 < (conj z).im
        simpa only [conj_im] using neg_pos.mpr hz
      have h := hpass (conj t) (by simpa only [norm_conj] using ht) (conj z) hcz
      exact ⟨(hconj _ h.1).congr (fun s hs =>
          (hreflectJets s t (mem_ball_zero_iff.mp hs) ht z hz).1),
        (hconj _ h.2).congr (fun s hs =>
          (hreflectJets s t (mem_ball_zero_iff.mp hs) ht z hz).2)⟩
  · intro s hs z hz
    rcases hz with hz | hz
    · exact hpass s hs z hz
    · have hcz : conj z ∈ upperHalf := by
        change 0 < (conj z).im
        simpa only [conj_im] using neg_pos.mpr hz
      have h := hact (conj s) (by simpa only [norm_conj] using hs) (conj z) hcz
      exact ⟨(hconj _ h.1).congr (fun t ht =>
          (hreflectJets s t hs (mem_ball_zero_iff.mp ht) z hz).1),
        (hconj _ h.2).congr (fun t ht =>
          (hreflectJets s t hs (mem_ball_zero_iff.mp ht) z hz).2)⟩
  · intro K hK
    obtain ⟨δ, C, hδ, _hδε, hC, hbound⟩ := hcompact K hK
    refine ⟨min δ ε, C, lt_min hδ hε, min_le_right _ _, hC, ?_⟩
    intro s t hs ht z hz
    exact hbound s t (hs.trans_le (min_le_left _ _)) (ht.trans_le (min_le_left _ _)) z hz

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
