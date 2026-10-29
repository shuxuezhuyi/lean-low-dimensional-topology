module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeLiftedHorizontalArcShortest
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The phase of regular arcs with the same actual trace

At a common regular interior point, an embedded arc determines its tangent
line. Complex conjugation removes the sign of real difference quotients, so
the comparison needs no differentiable change of parameter. The positive
quadratic-differential tangent products then determine the same unit phase.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Topology ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

private def tangentLinePhase (z : ℂ) : ℂ := z / conj z

private theorem tangentLinePhase_real_smul (r : ℝ) (z : ℂ) (hr : r ≠ 0) :
    tangentLinePhase (r • z) = tangentLinePhase z := by
  unfold tangentLinePhase
  simp only [RCLike.real_smul_eq_coe_mul, map_mul, RCLike.conj_ofReal]
  exact mul_div_mul_left z (conj z) (RCLike.ofReal_ne_zero.mpr hr)

private theorem tangentLinePhase_continuousAt {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt tangentLinePhase z := by
  have hc : conj z ≠ 0 := by simpa using hz
  exact continuousAt_id.div Complex.continuous_conj.continuousAt hc

private theorem sameTrace_tangent_real_multiple
    {a b : UpperHalfPlane} (α β : Path a b) (s t : ℝ)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (htrace : Set.range α = Set.range β)
    (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hpoint : α.extend s = β.extend t) {v w : ℂ}
    (hv : HasDerivAt (fun u : ℝ => (α.extend u : ℂ)) v s)
    (hw : HasDerivAt (fun u : ℝ => (β.extend u : ℂ)) w t)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    ∃ r : ℝ, r ≠ 0 ∧ v = (r : ℂ) * w := by
  classical
  let sI : unitInterval := ⟨s, Ioo_subset_Icc_self hs⟩
  let cα : ℝ → ℂ := fun u => (α.extend u : ℂ)
  let cβ : ℝ → ℂ := fun u => (β.extend u : ℂ)
  have hex (u : ℝ) : ∃ x : unitInterval, α x = β.extend u := by
    have hm : β.extend u ∈ Set.range β := by
      rw [← β.extend_range]
      exact mem_range_self u
    rw [← htrace] at hm
    exact hm
  choose k hk using hex
  have hαs : α sI = β.extend t :=
    (α.extend_apply (Ioo_subset_Icc_self hs)).symm.trans hpoint
  have hemb : Topology.IsClosedEmbedding α := α.continuous.isClosedEmbedding hα
  have hkLimit : Tendsto k (𝓝 t) (𝓝 sI) := by
    apply hemb.tendsto_nhds_iff.mpr
    change Tendsto (fun u => α (k u)) (𝓝 t) (𝓝 (α sI))
    have hkFun : (fun u => α (k u)) = β.extend := funext hk
    rw [hkFun, hαs]
    exact β.continuous_extend.continuousAt.tendsto
  have hkReal : Tendsto (fun u => (k u : ℝ)) (𝓝 t) (𝓝 s) :=
    (continuous_subtype_val.tendsto sI).comp hkLimit
  have hinside : ∀ᶠ u in 𝓝[≠] t, u ∈ Ioo (0 : ℝ) 1 :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2)
  have hkNe : ∀ᶠ u in 𝓝[≠] t, (k u : ℝ) ≠ s := by
    filter_upwards [hinside, self_mem_nhdsWithin] with u hu hut
    intro hku
    have hkEq : k u = sI := Subtype.ext hku
    have hβEq : β.extend u = β.extend t := by
      rw [← hk u, hkEq, hαs]
    have hpath : β ⟨u, Ioo_subset_Icc_self hu⟩ =
        β ⟨t, Ioo_subset_Icc_self ht⟩ := by
      rw [← β.extend_apply (Ioo_subset_Icc_self hu),
        ← β.extend_apply (Ioo_subset_Icc_self ht)]
      exact hβEq
    exact hut (congrArg (fun x : unitInterval => (x : ℝ)) (hβ hpath))
  have hkPunctured : Tendsto (fun u => (k u : ℝ)) (𝓝[≠] t) (𝓝[≠] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hkReal.mono_left nhdsWithin_le_nhds, hkNe⟩
  have hchord (u : ℝ) : cα (k u : ℝ) - cα s = cβ u - cβ t := by
    have hαu : α.extend (k u : ℝ) = β.extend u :=
      (α.extend_apply (k u).property).trans (hk u)
    dsimp only [cα, cβ]
    rw [hαu, hpoint]
  have hlimα : Tendsto (fun u => tangentLinePhase (slope cα s (k u : ℝ)))
      (𝓝[≠] t) (𝓝 (tangentLinePhase v)) :=
    (tangentLinePhase_continuousAt hv0).tendsto.comp
      (hv.tendsto_slope.comp hkPunctured)
  have hlimβ : Tendsto (fun u => tangentLinePhase (slope cβ t u))
      (𝓝[≠] t) (𝓝 (tangentLinePhase w)) :=
    (tangentLinePhase_continuousAt hw0).tendsto.comp hw.tendsto_slope
  have hsame : (fun u => tangentLinePhase (slope cα s (k u : ℝ))) =ᶠ[𝓝[≠] t]
      (fun u => tangentLinePhase (slope cβ t u)) := by
    filter_upwards [hkNe, self_mem_nhdsWithin] with u hku hut
    calc
      tangentLinePhase (slope cα s (k u : ℝ)) =
          tangentLinePhase (cα (k u : ℝ) - cα s) :=
        tangentLinePhase_real_smul _ _ (inv_ne_zero (sub_ne_zero.mpr hku))
      _ = tangentLinePhase (cβ u - cβ t) := congrArg tangentLinePhase (hchord u)
      _ = tangentLinePhase (slope cβ t u) :=
        (tangentLinePhase_real_smul _ _ (inv_ne_zero (sub_ne_zero.mpr hut))).symm
  have hphase := tendsto_nhds_unique_of_eventuallyEq hlimα hlimβ hsame
  have hcv : conj v ≠ 0 := by simpa using hv0
  have hcw : conj w ≠ 0 := by simpa using hw0
  have hcross : v * conj w = w * conj v :=
    (div_eq_div_iff hcv hcw).mp hphase
  have hreal : conj (v / w) = v / w := by
    rw [map_div₀]
    apply (div_eq_div_iff hcw hw0).mpr
    calc
      conj v * w = w * conj v := mul_comm _ _
      _ = v * conj w := hcross.symm
  obtain ⟨r, hr⟩ := RCLike.conj_eq_iff_real.mp hreal
  have hr0 : r ≠ 0 := by
    intro hzero
    have hquot : v / w = 0 := by simpa only [hzero, RCLike.ofReal_zero] using hr
    exact (div_ne_zero hv0 hw0) hquot
  exact ⟨r, hr0, (div_eq_iff hw0).mp hr⟩

/-- Two regular fixed-phase arcs with the same actual lifted trace have the
same unit phase at every common interior point. -/
theorem thetaArc_phase_eq_of_same_actual_trace
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (_hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ _hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      ∀ {a b : UpperHalfPlane} (α β : Path a b) (θα θβ s t : ℝ),
        Function.Injective α → Function.Injective β →
        Set.range α = Set.range β →
        s ∈ Ioo (0 : ℝ) 1 → t ∈ Ioo (0 : ℝ) 1 →
        α.extend s = β.extend t →
        IsHorizontalArc (fun z => Complex.exp (-(θα : ℂ) * Complex.I) * ψ z)
          (fun u : ℝ => (α.extend u : ℂ)) 0 1 →
        IsHorizontalArc (fun z => Complex.exp (-(θβ : ℂ) * Complex.I) * ψ z)
          (fun u : ℝ => (β.extend u : ℂ)) 0 1 →
        Complex.exp ((θα : ℂ) * Complex.I) =
          Complex.exp ((θβ : ℂ) * Complex.I) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  intro _hp
  dsimp only
  intro a b α β θα θβ s t hα hβ htrace hs ht hpoint hαArc hβArc
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let cα : ℝ → ℂ := fun u => (α.extend u : ℂ)
  let cβ : ℝ → ℂ := fun u => (β.extend u : ℂ)
  let v : ℂ := deriv cα s
  let w : ℂ := deriv cβ t
  let uα : ℂ := Complex.exp (-(θα : ℂ) * Complex.I)
  let uβ : ℂ := Complex.exp (-(θβ : ℂ) * Complex.I)
  let A : ℂ := uα * ψ (cα s) * v ^ 2
  let B : ℂ := uβ * ψ (cα s) * w ^ 2
  obtain ⟨hαDiff, hv0, _hαCoeff, hαIm, hαRe⟩ := hαArc s hs
  obtain ⟨hβDiff, hw0, _hβCoeff, hβIm, hβRe⟩ := hβArc t ht
  obtain ⟨r, _hr0, hderiv⟩ := sameTrace_tangent_real_multiple α β s t
    hα hβ htrace hs ht hpoint hαDiff.hasDerivAt hβDiff.hasDerivAt hv0 hw0
  change v = (r : ℂ) * w at hderiv
  change A.im = 0 at hαIm
  change 0 < A.re at hαRe
  change (uβ * ψ (cβ t) * w ^ 2).im = 0 at hβIm
  change 0 < (uβ * ψ (cβ t) * w ^ 2).re at hβRe
  have hpointC : cα s = cβ t :=
    congrArg (fun z : UpperHalfPlane => (z : ℂ)) hpoint
  rw [← hpointC] at hβIm hβRe
  change B.im = 0 at hβIm
  change 0 < B.re at hβRe
  have hA : (A.re : ℂ) = A := Complex.ext rfl hαIm.symm
  have hB : (B.re : ℂ) = B := Complex.ext rfl hβIm.symm
  have hcross : (A.re : ℂ) * uβ = ((r ^ 2 * B.re : ℝ) : ℂ) * uα := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, hA, hB]
    dsimp only [A, B]
    rw [hderiv]
    ring
  have huα : ‖uα‖ = 1 := by
    simpa only [uα, Complex.ofReal_neg] using Complex.norm_exp_ofReal_mul_I (-θα)
  have huβ : ‖uβ‖ = 1 := by
    simpa only [uβ, Complex.ofReal_neg] using Complex.norm_exp_ofReal_mul_I (-θβ)
  have hscale : A.re = r ^ 2 * B.re := by
    have hn := congrArg norm hcross
    simpa only [norm_mul, Complex.norm_of_nonneg hαRe.le,
      Complex.norm_of_nonneg (mul_nonneg (sq_nonneg r) hβRe.le), huα, huβ,
      mul_one] using hn
  have hunit : uβ = uα := by
    rw [← hscale] at hcross
    exact mul_left_cancel₀ (RCLike.ofReal_ne_zero.mpr (ne_of_gt hαRe)) hcross
  have hinv := congrArg (fun z : ℂ => z⁻¹) hunit.symm
  simpa only [uα, uβ, neg_mul, Complex.exp_neg, inv_inv] using hinv

end LowDimensionalTopology.Geometry.Teichmuller
