/-
Portions of the imaginary-part mean-value argument adapt Wu Xiaobin's
Li-Zhong-QC-formalization (Copyright 2026), released under Apache-2.0.
See THIRD_PARTY_NOTICES.md for the pinned source and retained license.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticSegments
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticUpperHalfDistance
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.DenselyOrdered

/-! Actual horizontal subpaths are geometric segments in their native atlas. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

private theorem image_eq_segment_of_im_deriv_zero
    {f : ℝ → ℂ} {l r : ℝ} (hlr : l < r)
    (hc : ContinuousOn f (Icc l r)) (hi : InjOn f (Icc l r))
    (hd : ∀ u ∈ Ioo l r, DifferentiableAt ℝ f u)
    (him : ∀ u ∈ Ioo l r, (deriv f u).im = 0) :
    f '' Icc l r = segment ℝ (f l) (f r) := by
  have hImc : ContinuousOn (fun u => (f u).im) (Icc l r) :=
    Complex.continuous_im.comp_continuousOn hc
  have hImd (u : ℝ) (hu : u ∈ Ioo l r) : HasDerivAt (fun v => (f v).im) 0 u := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt u (hd u hu).hasDerivAt
    change HasDerivAt (fun v => (f v).im) ((deriv f u).im) u at h
    simpa only [him u hu] using h
  have hconst (u : ℝ) (hu : u ∈ Icc l r) : (f u).im = (f l).im := by
    by_cases heq : u = l
    · rw [heq]
    have hlu : l < u := lt_of_le_of_ne hu.1 (Ne.symm heq)
    obtain ⟨v, hv, hder⟩ := exists_deriv_eq_slope (fun v => (f v).im) hlu
      (hImc.mono (Icc_subset_Icc le_rfl hu.2))
      (fun v hv => (hImd v ⟨hv.1, hv.2.trans_le hu.2⟩).differentiableAt.differentiableWithinAt)
    rw [(hImd v ⟨hv.1, hv.2.trans_le hu.2⟩).deriv] at hder
    rcases div_eq_zero_iff.mp hder.symm with hnum | hden
    · exact sub_eq_zero.mp hnum
    · exact False.elim ((sub_pos.mpr hlu).ne' hden)
  have hRc : ContinuousOn (fun u => (f u).re) (Icc l r) :=
    Complex.continuous_re.comp_continuousOn hc
  have hRi : InjOn (fun u => (f u).re) (Icc l r) := by
    intro u hu v hv heq
    exact hi hu hv (Complex.ext heq ((hconst u hu).trans (hconst v hv).symm))
  have hRimage : (fun u => (f u).re) '' Icc l r = segment ℝ (f l).re (f r).re := by
    rcases hRc.strictMonoOn_of_injOn_Icc' hlr.le hRi with hm | ha
    · have hend : (f l).re ≤ (f r).re :=
        hm.monotoneOn (left_mem_Icc.mpr hlr.le) (right_mem_Icc.mpr hlr.le) hlr.le
      exact (hRc.image_Icc_of_monotoneOn hlr.le hm.monotoneOn).trans (segment_eq_Icc hend).symm
    · have hend : (f r).re ≤ (f l).re :=
        ha.antitoneOn (left_mem_Icc.mpr hlr.le) (right_mem_Icc.mpr hlr.le) hlr.le
      calc
        _ = Icc (f r).re (f l).re := ContinuousOn.image_Icc_of_antitoneOn
          (f := fun u : ℝ => (f u).re) hlr.le hRc ha.antitoneOn
        _ = segment ℝ (f r).re (f l).re := (segment_eq_Icc hend).symm
        _ = segment ℝ (f l).re (f r).re := by rw [segment_symm]
  let B : ℝ →ᵃ[ℝ] ℂ := Complex.ofRealCLM.toLinearMap.toAffineMap +
    AffineMap.const ℝ ℝ (((f l).im : ℂ) * Complex.I)
  have hB (v : ℝ) : B v = (v : ℂ) + ((f l).im : ℂ) * Complex.I := rfl
  have hBf (u : ℝ) (hu : u ∈ Icc l r) : B (f u).re = f u := by
    rw [hB]
    apply Complex.ext
    · simp
    · simpa using (hconst u hu).symm
  calc
    f '' Icc l r = B '' ((fun u => (f u).re) '' Icc l r) := by
      rw [image_image]
      apply Set.image_congr
      intro u hu
      exact (hBf u hu).symm
    _ = B '' segment ℝ (f l).re (f r).re := congrArg (Set.image B) hRimage
    _ = segment ℝ (B (f l).re) (B (f r).re) := image_segment ℝ B _ _
    _ = segment ℝ (f l) (f r) := by
      rw [hBf l (left_mem_Icc.mpr hlr.le), hBf r (right_mem_Icc.mpr hlr.le)]

/-- The actual injective horizontal side is locally straight in genuine natural
coordinates. Its original subpath parameter and both endpoints are retained. -/
theorem native_horizontal_subpath_isQuadraticSegment
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (δ : Path a b) (s t : unitInterval), s < t →
        InjOn δ (Icc s t) →
        IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ)) (s : ℝ) (t : ℝ) →
        IsQuadraticSegment upperHalfNativeSurface qH (δ.subpath s t).toContinuousMap := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b δ s t hst hi hh
  let d : ℝ := (t : ℝ) - s
  have hd : 0 < d := sub_pos.mpr hst
  let A : ℝ → ℝ := fun u => d * u + s
  let C := δ.subpath s t
  let F : ℝ → ℂ := fun u => (C.extend u : ℂ)
  let G : ℝ → ℂ := fun u => (δ.extend u : ℂ)
  have hcomb (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      (Icc.convexComb s t ⟨u, hu⟩ : ℝ) = A u := by
    rw [Icc.coe_convexComb]
    dsimp only [A, d]
    ring
  have hA01 (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : A u ∈ Icc (0 : ℝ) 1 := by
    rw [← hcomb u hu]
    exact (Icc.convexComb s t ⟨u, hu⟩).property
  have hext (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : C.extend u = δ.extend (A u) := by
    rw [Path.extend_apply C hu]
    change δ (Icc.convexComb s t ⟨u, hu⟩) = δ.extend (A u)
    rw [Path.extend_apply δ (hA01 u hu)]
    exact congrArg δ (Subtype.ext (hcomb u hu))
  have hCi : Function.Injective C := by
    intro u v huv
    change δ (Icc.convexComb s t u) = δ (Icc.convexComb s t v) at huv
    have htime := hi ⟨Icc.le_convexComb hst.le u, Icc.convexComb_le hst.le u⟩
      ⟨Icc.le_convexComb hst.le v, Icc.convexComb_le hst.le v⟩ huv
    have hreal := congrArg (fun z : unitInterval => (z : ℝ)) htime
    rw [hcomb u u.property, hcomb v v.property] at hreal
    apply Subtype.ext
    dsimp only [A] at hreal
    nlinarith
  have hphase : IsHorizontalArc ψ F 0 1 := by
    intro u hu
    have hAu : A u ∈ Ioo (s : ℝ) t := by
      dsimp only [A, d]
      constructor <;> nlinarith [hu.1, hu.2]
    obtain ⟨hGd, hG0, hψ0, him, hre⟩ := hh (A u) hAu
    have hAd : HasDerivAt A d u := by
      simpa only [A] using (hasDerivAt_const_mul (𝕜 := ℝ) (x := u) d).add_const (s : ℝ)
    have hev : F =ᶠ[𝓝 u] (G ∘ A) := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
      exact congrArg UpperHalfPlane.coe (hext v (Ioo_subset_Icc_self hv))
    have hFd : HasDerivAt F ((d : ℂ) * deriv G (A u)) u := by
      simpa only [Complex.real_smul] using
        (hGd.hasDerivAt.scomp u hAd).congr_of_eventuallyEq hev
    have hFu : F u = G (A u) := congrArg UpperHalfPlane.coe (hext u (Ioo_subset_Icc_self hu))
    have hprod : ψ (F u) * deriv F u ^ 2 =
        ((d ^ 2 : ℝ) : ℂ) * (ψ (G (A u)) * deriv G (A u) ^ 2) := by
      rw [hFu, hFd.deriv]
      push_cast
      ring
    have hp : (ψ (F u) * deriv F u ^ 2).im = 0 ∧ 0 < (ψ (F u) * deriv F u ^ 2).re := by
      rw [hprod]
      exact (ofReal_mul_horizontal_iff (sq_pos_of_pos hd) _).2 ⟨him, hre⟩
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    refine ⟨hFd.differentiableAt, ?_, ?_, hp.1, hp.2⟩
    · rw [hFd.deriv]
      exact mul_ne_zero hdC hG0
    · simpa only [hFu] using hψ0
  have hFc : Continuous F := UpperHalfPlane.continuous_coe.comp C.continuous_extend
  have hchart (z : UpperHalfPlane) : chartAt ℂ z = UpperHalfPlane.ofComplex.symm := by
    have hz := chart_mem_atlas ℂ z
    change chartAt ℂ z ∈ ({UpperHalfPlane.ofComplex.symm} :
      Set (OpenPartialHomeomorph UpperHalfPlane ℂ)) at hz
    exact Set.mem_singleton_iff.mp hz
  have hchartfun (z : UpperHalfPlane) : (chartAt ℂ z : UpperHalfPlane → ℂ) = UpperHalfPlane.coe := by
    rw [hchart z]
    rfl
  refine ⟨hCi, ?_⟩
  intro u₀ hu₀0 hu₀1
  let z₀ : ℂ := (C u₀ : ℂ)
  have hz₀ : z₀ ∈ upperHalf := (C u₀).im_pos
  have hreg : ψ z₀ ≠ 0 := by
    have h := (hphase u₀ ⟨hu₀0, hu₀1⟩).2.2.1
    simpa only [F, Path.extend_apply C u₀.property] using h
  obtain ⟨ζ, r, hr, hsub, hζ0, hinj, han⟩ :=
    psa_chart isOpen_upperHalf (utm_liftQD_differentiableOn q.property hp) hz₀ hreg
  obtain ⟨hopen, hInv⟩ := psa_inverse hr hinj (fun z hz => ⟨(han z hz).1, (han z hz).2.2⟩)
  let e : OpenPartialHomeomorph ℂ ℂ :=
    { toFun := ζ
      invFun := Function.invFunOn ζ (ball z₀ r)
      source := ball z₀ r
      target := ζ '' ball z₀ r
      map_source' := fun z hz => ⟨z, hz, rfl⟩
      map_target' := fun w hw => (hInv w hw).1
      left_inv' := by
        intro z hz
        exact hinj (ball_subset_closedBall (hInv (ζ z) ⟨z, hz, rfl⟩).1)
          (ball_subset_closedBall hz) (hInv (ζ z) ⟨z, hz, rfl⟩).2.1
      right_inv' := fun w hw => (hInv w hw).2.1
      continuousOn_toFun := fun z hz => (han z (ball_subset_closedBall hz)).1.continuousAt.continuousWithinAt
      continuousOn_invFun := fun w hw => (hInv w hw).2.2.continuousAt.continuousWithinAt
      open_source := isOpen_ball
      open_target := hopen }
  have htarget : (chartAt ℂ (C u₀)).target = upperHalf := by
    rw [hchart]
    change (UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph UpperHalfPlane.coe).target = _
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, UpperHalfPlane.range_coe]
    rfl
  have hN : Ioo (0 : ℝ) 1 ∩ F ⁻¹' ball z₀ r ∈ 𝓝 (u₀ : ℝ) := by
    refine inter_mem (isOpen_Ioo.mem_nhds ⟨hu₀0, hu₀1⟩) ?_
    apply hFc.continuousAt.preimage_mem_nhds
    have hFu₀ : F u₀ = z₀ := by
      change (C.extend (u₀ : ℝ) : ℂ) = (C u₀ : ℂ)
      rw [Path.extend_apply C u₀.property]
    rw [hFu₀]
    exact isOpen_ball.mem_nhds (mem_ball_self hr)
  obtain ⟨l, v, _hu₀, hIcc, hwin⟩ := exists_Icc_mem_subset_of_mem_nhds hN
  obtain ⟨hlu₀, hu₀v⟩ := Icc_mem_nhds_iff.mp hIcc
  have hlv : l < v := hlu₀.trans hu₀v
  have hl01 : l ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self (hwin (left_mem_Icc.mpr hlv.le)).1
  have hv01 : v ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self (hwin (right_mem_Icc.mpr hlv.le)).1
  let α : unitInterval := ⟨l, hl01⟩
  let β : unitInterval := ⟨v, hv01⟩
  let g : ℝ → ℂ := fun u => ζ (F u)
  have hmap (u : ℝ) (hu : u ∈ Icc l v) : F u ∈ ball z₀ r := (hwin hu).2
  have hunit (u : ℝ) (hu : u ∈ Icc l v) : u ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self (hwin hu).1
  have hgc : ContinuousOn g (Icc l v) :=
    (show ContinuousOn ζ (ball z₀ r) from fun z hz =>
      (han z (ball_subset_closedBall hz)).1.continuousAt.continuousWithinAt).comp
      hFc.continuousOn hmap
  have hgi : InjOn g (Icc l v) := by
    intro u hu w hw heq
    have hFw : F u = F w := hinj (ball_subset_closedBall (hmap u hu))
      (ball_subset_closedBall (hmap w hw)) heq
    have hCw : C ⟨u, hunit u hu⟩ = C ⟨w, hunit w hw⟩ := by
      simpa only [F, Path.extend_apply C (hunit u hu), Path.extend_apply C (hunit w hw)]
        using UpperHalfPlane.coe_injective hFw
    exact congrArg (fun z : unitInterval => (z : ℝ)) (hCi hCw)
  have hgd (u : ℝ) (hu : u ∈ Ioo l v) :
      HasDerivAt g (deriv F u * deriv ζ (F u)) u :=
    ((han (F u) (ball_subset_closedBall (hmap u (Ioo_subset_Icc_self hu)))).1.differentiableAt.hasDerivAt).scomp u
      (hphase u (hwin (Ioo_subset_Icc_self hu)).1).1.hasDerivAt
  have hgim (u : ℝ) (hu : u ∈ Ioo l v) : (deriv g u).im = 0 := by
    obtain ⟨_, hF0, hψ0, him, hre⟩ := hphase u (hwin (Ioo_subset_Icc_self hu)).1
    have hsquare : deriv g u ^ 2 = ψ (F u) * deriv F u ^ 2 := by
      rw [(hgd u hu).deriv, mul_pow, (han (F u) (ball_subset_closedBall (hmap u (Ioo_subset_Icc_self hu)))).2.1]
      ring
    exact (s25g_sq_real hsquare (mul_ne_zero hψ0 (pow_ne_zero 2 hF0))
      (Complex.arg_eq_zero_iff.mpr ⟨hre.le, him⟩)).1
  have hImage := image_eq_segment_of_im_deriv_zero hlv hgc hgi
    (fun u hu => (hgd u hu).differentiableAt) hgim
  have hpathImage : (fun u : unitInterval => e (chartAt ℂ (C u₀) (C u))) '' Icc α β =
      g '' Icc l v := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(u : ℝ), hu, ?_⟩
      rw [hchartfun]
      change ζ (C.extend (u : ℝ) : ℂ) = ζ (C u : ℂ)
      rw [Path.extend_apply C u.property]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨u, hunit u hu⟩, hu, ?_⟩
      rw [hchartfun]
      change ζ (C ⟨u, hunit u hu⟩ : ℂ) = ζ (C.extend u : ℂ)
      rw [Path.extend_apply C (hunit u hu)]
  refine ⟨?_, e, ?_, ?_, ?_, ?_, α, β, hlu₀, hu₀v, ?_, ?_⟩
  · rw [hchartfun]
    change upperHalf.indicator ψ z₀ ≠ 0
    rwa [Set.indicator_of_mem hz₀]
  · intro z hz
    change z ∈ (chartAt ℂ (C u₀)).target
    rw [htarget]
    exact hsub (ball_subset_closedBall hz)
  · intro z hz
    exact (han z (ball_subset_closedBall hz)).1
  · rw [hchartfun]
    exact hζ0
  · intro z hz
    change deriv ζ z ^ 2 = upperHalf.indicator ψ z
    rw [Set.indicator_of_mem (hsub (ball_subset_closedBall hz))]
    exact (han z (ball_subset_closedBall hz)).2.1
  · intro u hu
    constructor
    · rw [hchart]
      change C u ∈ (univ : Set UpperHalfPlane)
      trivial
    · rw [hchartfun]
      change (C u : ℂ) ∈ ball z₀ r
      have h := hmap (u : ℝ) hu
      simpa only [F, Path.extend_apply C u.property] using h
  · change (fun u : unitInterval => e (chartAt ℂ (C u₀) (C u))) '' Icc α β =
      segment ℝ (e (chartAt ℂ (C u₀) (C α))) (e (chartAt ℂ (C u₀) (C β)))
    rw [hpathImage, hImage]
    simp only [hchartfun]
    change segment ℝ (ζ (C.extend l : ℂ)) (ζ (C.extend v : ℂ)) =
      segment ℝ (ζ (C α : ℂ)) (ζ (C β : ℂ))
    rw [Path.extend_apply C hl01, Path.extend_apply C hv01]

end LowDimensionalTopology.Geometry.Teichmuller
