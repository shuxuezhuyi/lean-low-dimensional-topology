module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonKernelL2Input
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# The actual harmonic inner principal value

The existing harmonic subspace supplies a literal quadratic coefficient equal
to the chosen representative almost everywhere. On the upper half-plane that
coefficient is smooth. A compact smooth cutoff uses the existing C¹ Hilbert
PV theorem; the L² remainder vanishes near the evaluation point and has a
constant truncated integral. The resulting limit is the existing actual
hilbertHSmooth, and exact a.e. invariance returns to the original representative.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology Metric
open scoped ComplexConjugate UpperHalfPlane Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open LiZhongQC GammaMeasurableBeltrami

private theorem principalValueExists_congr_ae {f g : ℂ → ℂ}
    (h : f =ᵐ[volume] g) (ξ : ℂ) (hf : PrincipalValueExists f ξ) :
    PrincipalValueExists g ξ := by
  have he (r : ℝ) :
      (∫ η in {η : ℂ | r < ‖η - ξ‖}, f η / (η - ξ) ^ 2) =
        ∫ η in {η : ℂ | r < ‖η - ξ‖}, g η / (η - ξ) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae h] with η hη
    rw [hη]
  refine ⟨fun r hr => (hf.1 r hr).congr ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae h] with η hη
    rw [hη]
  · have hH := congrFun (hilbertHSmooth_congr_ae h) ξ
    simpa only [he, hH] using hf.2

private theorem innerInput_congr_ae {μ ν : ℍ → ℂ}
    (h : μ =ᵐ[flatArea] ν) (z : ℍ) :
    innerInput μ z =ᵐ[volume] innerInput ν z := by
  apply ae_of_ae_restrict_of_ae_restrict_compl upperHalf
  · rw [← map_flat_coe, UpperHalfPlane.measurableEmbedding_coe.ae_map_iff]
    filter_upwards [h] with η hη
    simp only [innerInput, upperExtension, hη]
  · apply ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet.compl
    intro η hη
    simp only [innerInput, upperExtension, show ¬0 < η.im from hη, dite_false]

private theorem constant_truncation_of_zero_on_ball (f : ℂ → ℂ) (ξ : ℂ)
    {R : ℝ} (hR : 0 < R) (hf : ∀ η ∈ ball ξ R, f η = 0) :
    Tendsto (fun r : ℝ => -(1 / (Real.pi : ℂ)) *
      ∫ η in {η : ℂ | r < ‖η - ξ‖}, f η / (η - ξ) ^ 2)
      (𝓝[>] 0) (𝓝 (-(1 / (Real.pi : ℂ)) * ∫ η, f η / (η - ξ) ^ 2)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  congr 1
  have he := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (f := fun η => f η / (η - ξ) ^ 2) (μ := (volume : Measure ℂ))
    MeasurableSet.univ (subset_univ {η : ℂ | r < ‖η - ξ‖}) (fun η hη => by
      have hn : ‖η - ξ‖ ≤ r := not_lt.mp hη.2
      rw [hf η (by rw [mem_ball, dist_eq_norm]; exact hn.trans_lt hr.2), zero_div])
  simpa only [setIntegral_univ] using he

private theorem principalValueExists_of_memLp_contDiffOn_upper
    (f : ℂ → ℂ) (hLp : MemLp f 2 (volume : Measure ℂ))
    (hd : ContDiffOn ℝ 1 f upperHalf) (ξ : ℍ) : PrincipalValueExists f ξ := by
  let b : ContDiffBump (ξ : ℂ) := ⟨ξ.im / 4, ξ.im / 2, by positivity, by linarith [ξ.im_pos]⟩
  let ψ : ℂ → ℂ := fun η => (b η : ℂ) * f η
  have hsub : closedBall (ξ : ℂ) (ξ.im / 2) ⊆ upperHalf := by
    intro η hη
    have hn : ‖η - ξ‖ ≤ ξ.im / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hη
    have hi : ξ.im - η.im ≤ ‖η - ξ‖ := by
      calc
        ξ.im - η.im = -(η - ξ).im := by simp only [sub_im, UpperHalfPlane.coe_im]; ring
        _ ≤ |(η - ξ).im| := neg_le_abs _
        _ ≤ ‖η - ξ‖ := Complex.abs_im_le_norm _
    change 0 < η.im
    linarith [ξ.im_pos]
  have hb : ContDiff ℝ 1 (fun η : ℂ => (b η : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hψ : ContDiff ℝ 1 ψ := by
    rw [contDiff_iff_contDiffAt]
    intro η
    by_cases hη : η ∈ tsupport b
    · have hupper : η ∈ upperHalf := hsub (by simpa only [b.tsupport_eq] using hη)
      exact hb.contDiffAt.mul (hd.contDiffAt (isOpen_upperHalf.mem_nhds hupper))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (b : ℂ → ℝ)).isOpen_compl.mem_nhds hη] with w hw
      change (b w : ℂ) * f w = 0
      rw [image_eq_zero_of_notMem_tsupport hw, Complex.ofReal_zero, zero_mul]
  have hψc : HasCompactSupport ψ :=
    (b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) rfl).mul_right
  have hψLp : MemLp ψ 2 (volume : Measure ℂ) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  let d : ℂ → ℂ := f - ψ
  have hdLp : MemLp d 2 (volume : Measure ℂ) := hLp.sub hψLp
  have hzero : ∀ η ∈ ball (ξ : ℂ) (ξ.im / 4), d η = 0 := by
    intro η hη
    have hone := b.one_of_mem_closedBall (ball_subset_closedBall hη)
    simp only [d, Pi.sub_apply, ψ, hone, Complex.ofReal_one, one_mul, sub_self]
  have hψlim := tendsto_truncated_cauchyT_dz hψ hψc (ξ : ℂ)
  have hdlim := constant_truncation_of_zero_on_ball d ξ (by positivity : 0 < ξ.im / 4) hzero
  have hsum := hψlim.add hdlim
  have hInt (a : ℂ → ℂ) (ha : MemLp a 2 (volume : Measure ℂ)) (r : ℝ) (hr : 0 < r) :=
    integrableOn_truncated_kernel (p := 2) (by norm_num)
      (by simpa only [ofReal_two_eq] using ha) (ξ : ℂ) hr
  have hlim : Tendsto (fun r : ℝ => -(1 / (Real.pi : ℂ)) *
      ∫ η in {η : ℂ | r < ‖η - ξ‖}, f η / (η - ξ) ^ 2)
      (𝓝[>] 0) (𝓝 (cauchyT (dz ψ) ξ +
        -(1 / (Real.pi : ℂ)) * ∫ η, d η / (η - ξ) ^ 2)) := by
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [← mul_add, ← integral_add (hInt ψ hψLp r hr) (hInt d hdLp r hr)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun η => by dsimp only [d, Pi.sub_apply]; ring
  refine ⟨fun r hr => hInt f hLp r hr, ?_⟩
  have he : hilbertHSmooth f ξ = cauchyT (dz ψ) ξ +
      -(1 / (Real.pi : ℂ)) * ∫ η, d η / (η - ξ) ^ 2 := hlim.limUnder_eq
  rwa [he]

open Surfaces QuadraticBergman

/-- The SAME original quadratic harmonic class has its genuine inner PV at
every original upper point; the chosen L-infinity representative is retained. -/
theorem innerInput_ofQuadratic_principalValueExists
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z ξ : ℍ) :
    PrincipalValueExists
      (innerInput (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z) ξ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let a : Ambient := (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
  let f : ℂ → ℂ := innerInput (NativeHarmonicBeltrami.coefficient R p q) z
  have hae : innerInput (fun η => a η) z =ᵐ[volume] f :=
    innerInput_congr_ae (ae_hyperbolic_iff.mp
      (NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp q)) z
  have hLp : MemLp f 2 (volume : Measure ℂ) :=
    (memLp_congr_ae hae).mp (innerInput_memLp_two a z)
  have hQ : ContDiffOn ℝ 1 (uniformizedQuadratic R p q) upperHalf :=
    ((utm_liftQD_differentiableOn q.property hp).contDiffOn isOpen_upperHalf).restrict_scalars ℝ
  have him : ContDiff ℝ 1 (fun η : ℂ => (η.im : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff
  have hk : ContDiffOn ℝ 1 (fun η : ℂ => cauchySquare η (conj (z : ℂ))) upperHalf := by
    have hden : DifferentiableOn ℂ
        (fun η : ℂ => (η - conj (z : ℂ)) ^ 2) upperHalf :=
      (differentiableOn_id.sub (differentiableOn_const (conj (z : ℂ)))).pow 2
    have hne : ∀ η ∈ upperHalf, (η - conj (z : ℂ)) ^ 2 ≠ 0 := by
      intro η hη
      apply pow_ne_zero 2
      intro he
      have hi := congrArg Complex.im he
      simp only [sub_im, conj_im, zero_im] at hi
      have hz : 0 < (z : ℂ).im := by
        simpa only [UpperHalfPlane.coe_im] using z.im_pos
      linarith [hz, show 0 < η.im from hη]
    have hhol : DifferentiableOn ℂ
        (fun η : ℂ => cauchySquare η (conj (z : ℂ))) upperHalf := by
      change DifferentiableOn ℂ (fun η : ℂ => (1 : ℂ) / (η - conj (z : ℂ)) ^ 2) upperHalf
      exact (differentiableOn_const (1 : ℂ)).div hden hne
    exact (hhol.contDiffOn isOpen_upperHalf).restrict_scalars ℝ
  have hf : ContDiffOn ℝ 1 f upperHalf := by
    apply (((him.pow 2).contDiffOn.mul
      (Complex.conjCLE.contDiff.comp_contDiffOn hQ)).mul hk).congr
    intro η hη
    change innerInput (NativeHarmonicBeltrami.coefficient R p q) z η = _
    dsimp only [innerInput, upperExtension]
    rw [dite_eq_left (show 0 < η.im from hη), NativeHarmonicBeltrami.coefficient_eq_uniformized]
    rfl
  exact principalValueExists_congr_ae hae.symm ξ
    (principalValueExists_of_memLp_contDiffOn_upper f hLp hf ξ)

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree

/-- Every SAME actual native source direction has its true inner principal
value at every original upper point, without a PV-convergence hypothesis. -/
theorem nativeWeilPetersson_inner_principalValueExists
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (v : E) (z ξ : ℍ) :
    SourceKernel.PrincipalValueExists
      (SourceKernel.innerInput
        (nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth ν P F hF v) z) ξ := by
  let := C
  let b := TH ν P F hF hsmooth ((K (β ν.val)).symm v)
  rcases (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic
    (deformedNativeSurface R hgenus hΓ hp ν) P (deformedTargetCover R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) F hF b.val).mp b.property with ⟨q, hq⟩
  have h := SourceKernel.innerInput_ofQuadratic_principalValueExists
    (deformedNativeSurface R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) q z ξ
  rw [hq] at h
  exact h

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
