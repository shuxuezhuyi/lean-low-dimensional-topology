module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticCayleyL1Transport
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.IsometricCircle.BoundaryIsometricCircles
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic.Ring

/-!
# The actual disc Poincare series under Cayley conjugation

Every transformation of the original projective half-plane group is carried
bijectively to its actual Cayley conjugate. The finite-coordinate action and
its squared derivative transport each quadratic summand. Unweighted L¹
transport and a true summable compact majorant give absolute convergence and
uniform convergence on compact subsets of the entire disc. The same literal
series is holomorphic and satisfies the quadratic automorphy equation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators UpperHalfPlane OnePoint Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Teichmuller.DiskPoincare

open LiZhongQC Hyperbolic Mobius WeightedQuadraticBergman

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))

/-- The entire actual disc group is the Cayley conjugate of the original image. -/
def discGroup : Subgroup complexMobiusGroup :=
  (Γ.map realSLMobius).map (MulAut.conj cayleyMobius).toMonoidHom

/-- Canonical conjugation retains every original projective transformation exactly once. -/
def cayleyGroupEquiv : Γ.map realSLMobius ≃* discGroup Γ :=
  (MulAut.conj cayleyMobius).subgroupMap (Γ.map realSLMobius)

@[simp] theorem cayleyGroupEquiv_coe (g : Γ.map realSLMobius) :
    (cayleyGroupEquiv Γ g).val = cayleyMobius * g.val * cayleyMobius⁻¹ := rfl

/-- The finite coordinate of the actual extended action, with zero at infinity. -/
def action (h : discGroup Γ) (z : ℂ) : ℂ :=
  ((h.val.val (z : ExtendedComplex)).elim 0 id : ℂ)

/-- Every original disc point has the genuine finite image under the actual conjugate. -/
theorem extended_action_equiv (g : Γ.map realSLMobius) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (cayleyGroupEquiv Γ g).val.val (z : ExtendedComplex) =
      (cayleyFormula (ProjectivePoincare.action Γ g (inverseCayleyFormula z)) :
        ExtendedComplex) := by
  obtain ⟨A, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ g
  let zD : 𝔻 := Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz)
  have he : (cayleyGroupEquiv Γ (ProjectivePoincare.imageHom Γ A)).val =
      discCayleyMobius A.val := cayleyGroupEquiv_coe Γ (ProjectivePoincare.imageHom Γ A)
  rw [he]
  have hpoint := discCayleyMobius_action A.val zD
  simp only [zD, Complex.UnitDisc.coe_mk] at hpoint
  rw [hpoint]
  apply congrArg (fun w : ℂ => (w : ExtendedComplex))
  have hzH : inverseCayleyFormula z ∈ upperHalf := by
    simpa only [upperHalf] using inverseCayley_mapsTo hz
  rw [ProjectivePoincare.action_image Γ A hzH]
  change cayleyFormula (((A.val • discToHalfPlane zD : ℍ) : ℂ)) =
    cayleyFormula (h36p_m A.val ((discToHalfPlane zD : ℍ) : ℂ))
  exact congrArg cayleyFormula (h36p_m_coe A.val (discToHalfPlane zD)).symm

/-- On every original disc point the actual finite coordinate is literal Cayley conjugation. -/
theorem action_equiv (g : Γ.map realSLMobius) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    action Γ (cayleyGroupEquiv Γ g) z =
      cayleyFormula (ProjectivePoincare.action Γ g (inverseCayleyFormula z)) := by
  simp only [action, extended_action_equiv Γ g hz, OnePoint.elim_some, id_eq]

/-- All elements of the actual conjugate group preserve the whole original disc. -/
theorem action_mem (h : discGroup Γ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    action Γ h z ∈ Metric.ball (0 : ℂ) 1 := by
  obtain ⟨g, rfl⟩ := (cayleyGroupEquiv Γ).surjective h
  rw [action_equiv Γ g hz]
  have hzH : inverseCayleyFormula z ∈ upperHalf := by
    simpa only [upperHalf] using inverseCayley_mapsTo hz
  apply cayley_mapsTo
  simpa only [upperHalf] using ProjectivePoincare.action_mem Γ g hzH

private theorem halfPlane_action_hasDerivAt (g : Γ.map realSLMobius) {z : ℂ}
    (hz : z ∈ upperHalf) :
    HasDerivAt (ProjectivePoincare.action Γ g) (deriv (ProjectivePoincare.action Γ g) z) z := by
  obtain ⟨A, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ g
  exact (ProjectivePoincare.action_hasDerivAt_image Γ A hz).differentiableAt.hasDerivAt

/-- The derivative belongs to the actual action and follows from the chain rule. -/
theorem action_hasDerivAt_equiv (g : Γ.map realSLMobius) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    HasDerivAt (action Γ (cayleyGroupEquiv Γ g))
      (cayleyDerivative (ProjectivePoincare.action Γ g (inverseCayleyFormula z)) *
        deriv (ProjectivePoincare.action Γ g) (inverseCayleyFormula z) *
          inverseCayleyDerivative z) z := by
  have hzH : inverseCayleyFormula z ∈ upperHalf := by
    simpa only [upperHalf] using inverseCayley_mapsTo hz
  have hgH : 0 < (ProjectivePoincare.action Γ g (inverseCayleyFormula z)).im := by
    simpa only [upperHalf, Set.mem_ofPred_eq] using ProjectivePoincare.action_mem Γ g hzH
  have hS := hasDerivAt_inverseCayleyFormula
    (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz))
  have hg := halfPlane_action_hasDerivAt Γ g hzH
  have hT := hasDerivAt_cayleyFormula
    (UpperHalfPlane.mk (ProjectivePoincare.action Γ g (inverseCayleyFormula z)) hgH)
  apply ((hT.comp (inverseCayleyFormula z) hg).comp z hS).congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact action_equiv Γ g hw

/-- Every actual disc transformation contributes its genuine quadratic pullback. -/
def term (f : ℂ → ℂ) (h : discGroup Γ) (z : ℂ) : ℂ :=
  f (action Γ h z) * deriv (action Γ h) z ^ 2

/-- Both squared derivative factors are retained in the exact summand identity. -/
theorem term_equiv (f : ℂ → ℂ) (g : Γ.map realSLMobius) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    term Γ f (cayleyGroupEquiv Γ g) z =
      ProjectivePoincare.term Γ (cayleyPullback f) g (inverseCayleyFormula z) *
        inverseCayleyDerivative z ^ 2 := by
  unfold term
  rw [action_equiv Γ g hz, (action_hasDerivAt_equiv Γ g hz).deriv]
  unfold ProjectivePoincare.term WeightedQuadraticBergman.cayleyPullback
  ring

/-- The literal Poincare series sums every actual disc transformation once. -/
def series (f : ℂ → ℂ) (z : ℂ) : ℂ := ∑' h : discGroup Γ, term Γ f h z

/-- The same literal disc sum is the inverse quadratic pullback of the entire half-plane sum. -/
theorem series_eq_inverseCayleyPullback (f : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    series Γ f z =
      inverseCayleyPullback (ProjectivePoincare.series Γ (cayleyPullback f)) z := by
  change (∑' h : discGroup Γ, term Γ f h z) =
    (∑' g : Γ.map realSLMobius,
      ProjectivePoincare.term Γ (cayleyPullback f) g (inverseCayleyFormula z)) *
        inverseCayleyDerivative z ^ 2
  calc
    _ = ∑' g : Γ.map realSLMobius, term Γ f (cayleyGroupEquiv Γ g) z :=
      ((cayleyGroupEquiv Γ).toEquiv.tsum_eq (fun h => term Γ f h z)).symm
    _ = ∑' g : Γ.map realSLMobius,
        ProjectivePoincare.term Γ (cayleyPullback f) g (inverseCayleyFormula z) *
          inverseCayleyDerivative z ^ 2 := tsum_congr (fun g => term_equiv Γ f g hz)
    _ = _ := tsum_mul_right

/-- Forward quadratic pullback recovers exactly the original half-plane series. -/
theorem cayleyPullback_series (f : ℂ → ℂ) {w : ℂ} (hw : w ∈ upperHalf) :
    cayleyPullback (series Γ f) w = ProjectivePoincare.series Γ (cayleyPullback f) w := by
  have hwH : 0 < w.im := by simpa only [upperHalf, Set.mem_ofPred_eq] using hw
  calc
    cayleyPullback (series Γ f) w = cayleyPullback
        (inverseCayleyPullback (ProjectivePoincare.series Γ (cayleyPullback f))) w :=
      congrArg (fun a : ℂ => a * cayleyDerivative w ^ 2)
        (series_eq_inverseCayleyPullback Γ f (cayley_mapsTo hwH))
    _ = _ := cayleyPullback_inverseCayleyPullback _ hwH

/-- A true summable majorant controls the whole actual group on every compact disc subset. -/
theorem compact_majorant (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hfA : phiArea f (Metric.ball (0 : ℂ) 1) < ⊤)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ v : discGroup Γ → ℝ, Summable v ∧
      ∀ h : discGroup Γ, ∀ z ∈ K, ‖term Γ f h z‖ ≤ v h := by
  have hU : DifferentiableOn ℂ (cayleyPullback f) upperHalf :=
    cayleyPullback_holomorphic hf
  have hUA : phiArea (cayleyPullback f) upperHalf < ⊤ := by
    rw [QuadraticCayleyL1.cayleyPullback_phiArea]
    exact hfA
  have hS : ContinuousOn inverseCayleyFormula (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact (hasDerivAt_inverseCayleyFormula
      (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz))).continuousAt.continuousWithinAt
  have himage : IsCompact (inverseCayleyFormula '' K) :=
    hK.image_of_continuousOn (hS.mono hKD)
  have himageH : inverseCayleyFormula '' K ⊆ upperHalf := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [upperHalf] using inverseCayley_mapsTo (hKD hz)
  obtain ⟨u, hu, hle⟩ := ProjectivePoincare.compact_majorant Γ hΓ hU hUA himage himageH
  have hd : ContinuousOn (fun z : ℂ => inverseCayleyDerivative z ^ 2)
      (Metric.ball (0 : ℂ) 1) := by
    have hconst : WeightedQuadraticBergman.inverseCayleyPullback (fun _ : ℂ => (1 : ℂ)) =
        (fun z : ℂ => inverseCayleyDerivative z ^ 2) := by
      funext z
      change (1 : ℂ) * inverseCayleyDerivative z ^ 2 = inverseCayleyDerivative z ^ 2
      exact one_mul _
    rw [← hconst]
    exact (inverseCayleyPullback_holomorphic (differentiableOn_const (1 : ℂ))).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hd.mono hKD)
  let C₀ : ℝ := max C 0
  refine ⟨fun h => C₀ * u ((cayleyGroupEquiv Γ).symm h),
    (hu.comp_injective (cayleyGroupEquiv Γ).symm.injective).mul_left C₀, ?_⟩
  intro h z hz
  have ht := term_equiv Γ f ((cayleyGroupEquiv Γ).symm h) (hKD hz)
  rw [(cayleyGroupEquiv Γ).apply_symm_apply h] at ht
  rw [ht, norm_mul]
  have hb : ‖inverseCayleyDerivative z ^ 2‖ ≤ C₀ :=
    (hC z hz).trans (le_max_left C 0)
  calc
    _ = ‖inverseCayleyDerivative z ^ 2‖ *
        ‖ProjectivePoincare.term Γ (cayleyPullback f)
          ((cayleyGroupEquiv Γ).symm h) (inverseCayleyFormula z)‖ := mul_comm _ _
    _ ≤ C₀ * u ((cayleyGroupEquiv Γ).symm h) :=
      mul_le_mul hb (hle _ _ ⟨z, hz, rfl⟩) (norm_nonneg _) (le_max_right C 0)

/-- Absolute convergence holds at every point of the entire original disc. -/
theorem summable_norm (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hfA : phiArea f (Metric.ball (0 : ℂ) 1) < ⊤)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    Summable (fun h : discGroup Γ => ‖term Γ f h z‖) := by
  obtain ⟨v, hv, hle⟩ := compact_majorant Γ hΓ hf hfA
    isCompact_singleton (singleton_subset_iff.mpr hz)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun h => hle h z (mem_singleton z)) hv

/-- Literal finite partial sums converge uniformly on every compact disc subset. -/
theorem tendstoUniformlyOn (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hfA : phiArea f (Metric.ball (0 : ℂ) 1) < ⊤)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ Metric.ball (0 : ℂ) 1) :
    TendstoUniformlyOn
      (fun s : Finset (discGroup Γ) => fun z => ∑ h ∈ s, term Γ f h z)
      (series Γ f) atTop K := by
  obtain ⟨v, hv, hle⟩ := compact_majorant Γ hΓ hf hfA hK hKD
  exact tendstoUniformlyOn_tsum hv hle

/-- Holomorphy is proved for the same full-disc series with the original L¹ seed. -/
theorem differentiableOn (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hfA : phiArea f (Metric.ball (0 : ℂ) 1) < ⊤) :
    DifferentiableOn ℂ (series Γ f) (Metric.ball (0 : ℂ) 1) := by
  have hU : DifferentiableOn ℂ (cayleyPullback f) upperHalf :=
    cayleyPullback_holomorphic hf
  have hUA : phiArea (cayleyPullback f) upperHalf < ⊤ := by
    rw [QuadraticCayleyL1.cayleyPullback_phiArea]
    exact hfA
  apply (inverseCayleyPullback_holomorphic
    (ProjectivePoincare.differentiableOn Γ hΓ hU hUA)).congr
  intro z hz
  exact series_eq_inverseCayleyPullback Γ f hz

/-- Every actual disc transformation satisfies the original quadratic automorphy equation. -/
theorem automorphic (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hfA : phiArea f (Metric.ball (0 : ℂ) 1) < ⊤)
    (h : discGroup Γ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    series Γ f (action Γ h z) * deriv (action Γ h) z ^ 2 = series Γ f z := by
  obtain ⟨g, rfl⟩ := (cayleyGroupEquiv Γ).surjective h
  have hzH : inverseCayleyFormula z ∈ upperHalf := by
    simpa only [upperHalf] using inverseCayley_mapsTo hz
  have hU : DifferentiableOn ℂ (cayleyPullback f) upperHalf :=
    cayleyPullback_holomorphic hf
  have hUA : phiArea (cayleyPullback f) upperHalf < ⊤ := by
    rw [QuadraticCayleyL1.cayleyPullback_phiArea]
    exact hfA
  change term Γ (series Γ f) (cayleyGroupEquiv Γ g) z = series Γ f z
  rw [term_equiv Γ (series Γ f) g hz]
  unfold ProjectivePoincare.term
  rw [cayleyPullback_series Γ f (ProjectivePoincare.action_mem Γ g hzH),
    ProjectivePoincare.automorphic Γ hΓ hU hUA g hzH]
  exact (series_eq_inverseCayleyPullback Γ f hz).symm

end LowDimensionalTopology.Geometry.Teichmuller.DiskPoincare
