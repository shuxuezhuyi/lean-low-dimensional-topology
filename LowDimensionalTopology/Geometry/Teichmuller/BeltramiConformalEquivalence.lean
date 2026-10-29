module

public import LowDimensionalTopology.Geometry.Teichmuller.SmoothBeltrami

/-!
# Equality of smooth Beltrami tensors and conformal target changes

The two maps have the same reference surface
and may have different target carriers and complex structures. Equality of their
actual tensors is equivalent to the actual relative target homeomorphism being
analytic. This statement concerns literal coefficients of the given maps, not
free-homotopy classes of markings.

The pointwise argument uses Wu Xiaobin's LiZhongQC Wirtinger chain rules,
fixed upstream commit 1c0d5473c020b66ed5106331a38a61536760b9b2, original file
LiZhongQC/Ch01/S06_C1Quasiconformal.lean. It uses neither AE/QC regularity nor
uniformization, and does not depend on the later Bers/similarity material.
-/

@[expose] public section

noncomputable section

open Complex Set Filter Topology
open scoped ComplexConjugate ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
open LiZhongQC (complexDilatation dz dzbar)

/-- Pointwise cancellation in the Wirtinger chain rule. A positive-Jacobian
coordinate map cannot hide a nonzero antiholomorphic derivative in a relative
map when the two composite coefficients agree. -/
theorem complexDifferentiableAt_of_comp_dilatation_eq
    {F H : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) (hH : DifferentiableAt ℝ H (F z))
    (hFlt : ‖dzbar F z‖ < ‖dz F z‖)
    (hcomp : dz (H ∘ F) z ≠ 0)
    (hμ : complexDilatation (H ∘ F) z = complexDilatation F z) :
    DifferentiableAt ℂ H (F z) := by
  have hFdz : dz F z ≠ 0 :=
    norm_pos_iff.1 (lt_of_le_of_lt (norm_nonneg _) hFlt)
  have hcross : dzbar (H ∘ F) z * dz F z = dzbar F z * dz (H ∘ F) z := by
    exact (div_eq_div_iff hcomp hFdz).1 hμ
  have h1 := LiZhongQC.eq6_2_dz_comp hF hH
  have h2 := LiZhongQC.eq6_2_dzbar_comp hF hH
  obtain ⟨hc1, hc2⟩ := LiZhongQC.eq6_3 hF
  rw [← hc2] at h1
  rw [← hc1] at h2
  rw [h1, h2] at hcross
  have hzero : dzbar H (F z) *
      (conj (dz F z) * dz F z - conj (dzbar F z) * dzbar F z) = 0 := by
    linear_combination hcross
  have hfactor : conj (dz F z) * dz F z - conj (dzbar F z) * dzbar F z =
      (LiZhongQC.jacobian F z : ℂ) := by
    simp only [Complex.conj_mul', LiZhongQC.jacobian,
      Complex.ofReal_sub, Complex.ofReal_pow]
  have hJ : 0 < LiZhongQC.jacobian F z := by
    have hsub : 0 < ‖dz F z‖ - ‖dzbar F z‖ := sub_pos.2 hFlt
    have hadd : 0 < ‖dz F z‖ + ‖dzbar F z‖ :=
      add_pos_of_pos_of_nonneg (lt_of_le_of_lt (norm_nonneg _) hFlt) (norm_nonneg _)
    have hprod := mul_pos hsub hadd
    unfold LiZhongQC.jacobian
    nlinarith
  have hfactor_ne : conj (dz F z) * dz F z - conj (dzbar F z) * dzbar F z ≠ 0 := by
    rw [hfactor]
    exact Complex.ofReal_ne_zero.mpr hJ.ne'
  exact LiZhongQC.cauchyRiemann_iff.2
    ⟨hH, (mul_eq_zero.mp hzero).resolve_right hfactor_ne⟩

universe u v w

/-- The actual relative target map gives the expected composite in fixed local
charts near every point where the intermediate chart is valid. -/
theorem relative_chartMap_germ
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X ≃ₜ Y) (g : X ≃ₜ Z)
    (a : OpenPartialHomeomorph X ℂ) (b : OpenPartialHomeomorph Y ℂ)
    (c : OpenPartialHomeomorph Z ℂ) {z : ℂ}
    (hz : z ∈ riemannChartMapDomain a f b) :
    riemannChartMap a g c =ᶠ[𝓝 z]
      riemannChartMap b (f.symm.trans g) c ∘ riemannChartMap a f b := by
  filter_upwards [(riemannChartMapDomain_isOpen a f b f.continuous).mem_nhds hz] with t ht
  change c (g (a.symm t)) = c (g (f.symm (b.symm (b (f (a.symm t))))))
  rw [b.left_inv ht.2, f.symm_apply_apply]

namespace SmoothSurfaceEquiv

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {R : RiemannSurface X} {S : RiemannSurface Y} {T : RiemannSurface Z}

/-- Equality of the original-atlas tensors forces the relative map to satisfy
Cauchy–Riemann at every point in every actual target-chart pair. -/
theorem relative_chartMap_complexDifferentiableAt_of_beltrami_eq
    (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceEquiv R T)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation R.toRiemannAtlas T.toRiemannAtlas g.toHomeomorph)
    (hμ : f.beltrami hf = g.beltrami hg)
    (b : OpenPartialHomeomorph Y ℂ) (hb : b ∈ S.charts)
    (c : OpenPartialHomeomorph Z ℂ) (hc : c ∈ T.charts)
    {v : ℂ} (hv : v ∈ riemannChartMapDomain b (f.toHomeomorph.symm.trans g.toHomeomorph) c) :
    DifferentiableAt ℂ (riemannChartMap b (f.toHomeomorph.symm.trans g.toHomeomorph) c) v := by
  let k : SmoothSurfaceEquiv S T :=
    SmoothSurfaceEquiv.trans (SmoothSurfaceEquiv.symm f) g
  let h : Y ≃ₜ Z := f.toHomeomorph.symm.trans g.toHomeomorph
  let y : Y := b.symm v
  let x : X := f.toHomeomorph.symm y
  obtain ⟨a, ha, hxa⟩ := R.cover x
  let z : ℂ := a x
  let F : ℂ → ℂ := riemannChartMap a f.toHomeomorph b
  let G : ℂ → ℂ := riemannChartMap a g.toHomeomorph c
  let H : ℂ → ℂ := riemannChartMap b h c
  have hfx : f.toHomeomorph x = y := f.toHomeomorph.apply_symm_apply y
  have hyb : y ∈ b.source := b.map_target hv.1
  have hxb : f.toHomeomorph x ∈ b.source := hfx.symm ▸ hyb
  have hxc : g.toHomeomorph x ∈ c.source := hv.2
  have hzF : z ∈ riemannChartMapDomain a f.toHomeomorph b := by
    refine ⟨a.map_source hxa, ?_⟩
    change f.toHomeomorph (a.symm (a x)) ∈ b.source
    rwa [a.left_inv hxa]
  have hzG : z ∈ riemannChartMapDomain a g.toHomeomorph c := by
    refine ⟨a.map_source hxa, ?_⟩
    change g.toHomeomorph (a.symm (a x)) ∈ c.source
    rwa [a.left_inv hxa]
  have hFz : F z = v := by
    change b (f.toHomeomorph (a.symm (a x))) = v
    rw [a.left_inv hxa, hfx]
    exact b.right_inv hv.1
  have hFD : DifferentiableAt ℝ F z :=
    ((f.chartMap_contDiffOn_real a ha b hb).differentiableOn one_ne_zero).differentiableAt
      ((riemannChartMapDomain_isOpen a f.toHomeomorph b f.toHomeomorph.continuous).mem_nhds hzF)
  have hHC1 : ContDiffOn ℝ 1 H (riemannChartMapDomain b h c) :=
    k.chartMap_contDiffOn_real b hb c hc
  have hHD : DifferentiableAt ℝ H (F z) := by
    rw [hFz]
    exact (hHC1.differentiableOn one_ne_zero).differentiableAt
      ((riemannChartMapDomain_isOpen b h c h.continuous).mem_nhds hv)
  have hFlt : ‖dzbar F z‖ < ‖dz F z‖ := f.chartMap_wirtinger_lt hf a ha b hb hzF
  have hGlt : ‖dzbar G z‖ < ‖dz G z‖ := g.chartMap_wirtinger_lt hg a ha c hc hzG
  have hGdz : dz G z ≠ 0 :=
    norm_pos_iff.1 (lt_of_le_of_lt (norm_nonneg _) hGlt)
  have hnear : G =ᶠ[𝓝 z] H ∘ F :=
    relative_chartMap_germ f.toHomeomorph g.toHomeomorph a b c hzF
  have hcomp : dz (H ∘ F) z ≠ 0 := by
    simpa only [dz, hnear.fderiv_eq] using hGdz
  let A : BeltramiDifferential.Chart R.toRiemannAtlas := ⟨a, ha⟩
  let zz : a.target := ⟨z, a.map_source hxa⟩
  have hcoeff := congrArg (fun μ : BeltramiDifferential R.toRiemannAtlas => μ.coeff A zz) hμ
  rw [f.beltrami_coeff_eq_chartDilatation hf A zz b hb hzF.2,
    g.beltrami_coeff_eq_chartDilatation hg A zz c hc hzG.2] at hcoeff
  have hratio : complexDilatation G z = complexDilatation (H ∘ F) z := by
    simp only [complexDilatation, dz, dzbar, hnear.fderiv_eq]
  have hsame : complexDilatation (H ∘ F) z = complexDilatation F z :=
    hratio.symm.trans hcoeff.symm
  have hhol := complexDifferentiableAt_of_comp_dilatation_eq hFD hHD hFlt hcomp hsame
  simpa only [hFz] using hhol

/-- Identical Beltrami tensors give an actual analytic relative homeomorphism,
with no compactness, genus, QC or homotopy premise. -/
theorem relative_analytic_of_beltrami_eq
    (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceEquiv R T)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation R.toRiemannAtlas T.toRiemannAtlas g.toHomeomorph)
    (hμ : f.beltrami hf = g.beltrami hg) :
    RiemannAnalyticMap S.toRiemannAtlas T.toRiemannAtlas
      (f.toHomeomorph.symm.trans g.toHomeomorph) := by
  refine ⟨(f.toHomeomorph.symm.trans g.toHomeomorph).continuous, ?_⟩
  intro b hb c hc
  have hd : DifferentiableOn ℂ
      (riemannChartMap b (f.toHomeomorph.symm.trans g.toHomeomorph) c)
      (riemannChartMapDomain b (f.toHomeomorph.symm.trans g.toHomeomorph) c) := by
    intro v hv
    exact (f.relative_chartMap_complexDifferentiableAt_of_beltrami_eq g hf hg hμ b hb c hc hv).differentiableWithinAt
  exact hd.analyticOnNhd
    (riemannChartMapDomain_isOpen b (f.toHomeomorph.symm.trans g.toHomeomorph) c
      (f.toHomeomorph.symm.trans g.toHomeomorph).continuous)

/-- An analytic relative target homeomorphism preserves the actual Beltrami tensor. -/
theorem beltrami_eq_of_relative_analytic
    (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceEquiv R T)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation R.toRiemannAtlas T.toRiemannAtlas g.toHomeomorph)
    (han : RiemannAnalyticMap S.toRiemannAtlas T.toRiemannAtlas
      (f.toHomeomorph.symm.trans g.toHomeomorph)) :
    f.beltrami hf = g.beltrami hg := by
  apply BeltramiDifferential.ext
  intro a z
  let x : X := a.val.symm z.val
  obtain ⟨b, hb, hxb⟩ := S.cover (f.toHomeomorph x)
  obtain ⟨c, hc, hxc⟩ := T.cover (g.toHomeomorph x)
  let h : Y ≃ₜ Z := f.toHomeomorph.symm.trans g.toHomeomorph
  let F : ℂ → ℂ := riemannChartMap a.val f.toHomeomorph b
  let G : ℂ → ℂ := riemannChartMap a.val g.toHomeomorph c
  let H : ℂ → ℂ := riemannChartMap b h c
  have hzF : z.val ∈ riemannChartMapDomain a.val f.toHomeomorph b := ⟨z.property, hxb⟩
  have hzH : F z.val ∈ riemannChartMapDomain b h c := by
    refine ⟨b.map_source hxb, ?_⟩
    change g.toHomeomorph (f.toHomeomorph.symm (b.symm (b (f.toHomeomorph x)))) ∈ c.source
    rw [b.left_inv hxb, f.toHomeomorph.symm_apply_apply]
    exact hxc
  have hFD : DifferentiableAt ℝ F z.val :=
    ((f.chartMap_contDiffOn_real a.val a.property b hb).differentiableOn one_ne_zero).differentiableAt
      ((riemannChartMapDomain_isOpen a.val f.toHomeomorph b f.toHomeomorph.continuous).mem_nhds hzF)
  have hHD : DifferentiableAt ℂ H (F z.val) := (han.2 b hb c hc _ hzH).differentiableAt
  have hHne : deriv H (F z.val) ≠ 0 := by
    let K := riemannHomeomorphChart b h c
    have hKA : AnalyticOnNhd ℂ K K.source := by
      rw [show K.source = riemannChartMapDomain b h c from riemannHomeomorphChart_source b h c]
      exact han.2 b hb c hc
    have hzK : F z.val ∈ K.source := by
      rwa [show K.source = riemannChartMapDomain b h c from riemannHomeomorphChart_source b h c]
    exact openPartialHomeomorph_analytic_forward_deriv_ne_zero K hKA (F z.val) hzK
  have hpost := LiZhongQC.complexDilatation_comp_conformal_left hFD hHD hHne
  have hnear : G =ᶠ[𝓝 z.val] H ∘ F :=
    relative_chartMap_germ f.toHomeomorph g.toHomeomorph a.val b c hzF
  have hratio : complexDilatation G z.val = complexDilatation (H ∘ F) z.val := by
    simp only [complexDilatation, dz, dzbar, hnear.fderiv_eq]
  rw [f.beltrami_coeff_eq_chartDilatation hf a z b hb hxb,
    g.beltrami_coeff_eq_chartDilatation hg a z c hc hxc]
  exact hpost.symm.trans hratio.symm

/-- Equality of the literal tensors is exactly analyticity of the literal
relative target homeomorphism. Its inverse is analytic by the existing native
analytic-inverse theorem. -/
theorem beltrami_eq_iff_relative_analytic
    (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceEquiv R T)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation R.toRiemannAtlas T.toRiemannAtlas g.toHomeomorph) :
    f.beltrami hf = g.beltrami hg ↔
      RiemannAnalyticMap S.toRiemannAtlas T.toRiemannAtlas
        (f.toHomeomorph.symm.trans g.toHomeomorph) :=
  ⟨f.relative_analytic_of_beltrami_eq g hf hg,
    f.beltrami_eq_of_relative_analytic g hf hg⟩

/-- The same equivalence stated with an actual biholomorphic target change
carrying one given smooth marking exactly to the other. -/
theorem beltrami_eq_iff_exists_analytic_homeomorph
    (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceEquiv R T)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation R.toRiemannAtlas T.toRiemannAtlas g.toHomeomorph) :
    f.beltrami hf = g.beltrami hg ↔
      ∃ e : Y ≃ₜ Z, RiemannAnalyticMap S.toRiemannAtlas T.toRiemannAtlas e ∧
        RiemannAnalyticMap T.toRiemannAtlas S.toRiemannAtlas e.symm ∧
        ∀ x : X, e (f.toHomeomorph x) = g.toHomeomorph x := by
  constructor
  · intro hμ
    have hrel := (f.beltrami_eq_iff_relative_analytic g hf hg).1 hμ
    refine ⟨f.toHomeomorph.symm.trans g.toHomeomorph, hrel,
      riemannAnalyticMap_homeomorph_symm _ hrel, ?_⟩
    intro x
    change g.toHomeomorph (f.toHomeomorph.symm (f.toHomeomorph x)) = g.toHomeomorph x
    rw [f.toHomeomorph.symm_apply_apply]
  · rintro ⟨e, he, _heInv, hmark⟩
    have heq : e = f.toHomeomorph.symm.trans g.toHomeomorph := by
      ext y
      simpa only [f.toHomeomorph.apply_symm_apply, Homeomorph.trans_apply] using
        hmark (f.toHomeomorph.symm y)
    rw [heq] at he
    exact (f.beltrami_eq_iff_relative_analytic g hf hg).2 he

end SmoothSurfaceEquiv

end LowDimensionalTopology.Geometry.Teichmuller
