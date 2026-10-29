module

public import LowDimensionalTopology.Geometry.Teichmuller.SmoothBeltrami
public import LowDimensionalTopology.Geometry.Teichmuller.MappingClass

/-!
# Composition of actual smooth-surface Beltrami tensors

For f : R → S followed by g : S → T, the forward formula has phase
conj(f_z)/f_z. The reverse formula solves the same identity for the
coefficient of g at f(z).
Every chart below belongs to the original atlas. No QC or a.e. premise is used.
-/

@[expose] public section
noncomputable section

open Set Filter Topology
open scoped ComplexConjugate ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
open LiZhongQC (complexDilatation dz dzbar)

namespace SmoothSurfaceEquiv

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {R : RiemannSurface X} {S : RiemannSurface Y} {T : RiemannSurface Z}

/-- The actual tensor of g after f, in any three actual original charts. -/
theorem beltrami_trans_coeff
    (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceEquiv S T)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation S.toRiemannAtlas T.toRiemannAtlas g.toHomeomorph)
    (e : BeltramiDifferential.Chart R.toRiemannAtlas)
    (b : BeltramiDifferential.Chart S.toRiemannAtlas)
    (c : BeltramiDifferential.Chart T.toRiemannAtlas) (z : e.val.target)
    (hy : f.toHomeomorph (e.val.symm z.val) ∈ b.val.source)
    (hz : g.toHomeomorph (f.toHomeomorph (e.val.symm z.val)) ∈ c.val.source) :
    let F := riemannChartMap e.val f.toHomeomorph b.val
    let q : b.val.target := ⟨F z.val, b.val.map_source hy⟩
    ((SmoothSurfaceEquiv.trans f g).beltrami
      (hg.comp hf f.toHomeomorph.continuous)).coeff e z =
      ((f.beltrami hf).coeff e z + (g.beltrami hg).coeff b q *
        (conj (dz F z.val) / dz F z.val)) /
      (1 + conj ((f.beltrami hf).coeff e z) * (g.beltrami hg).coeff b q *
        (conj (dz F z.val) / dz F z.val)) := by
  dsimp only
  let F := riemannChartMap e.val f.toHomeomorph b.val
  let G := riemannChartMap b.val g.toHomeomorph c.val
  let H := riemannChartMap e.val (SmoothSurfaceEquiv.trans f g).toHomeomorph c.val
  let q : b.val.target := ⟨F z.val, b.val.map_source hy⟩
  have hzF : z.val ∈ riemannChartMapDomain e.val f.toHomeomorph b.val := ⟨z.property, hy⟩
  have hGq : g.toHomeomorph (b.val.symm q.val) ∈ c.val.source := by
    change g.toHomeomorph (b.val.symm (b.val (f.toHomeomorph (e.val.symm z.val)))) ∈ c.val.source
    rw [b.val.left_inv hy]
    exact hz
  have hzG : F z.val ∈ riemannChartMapDomain b.val g.toHomeomorph c.val :=
    ⟨q.property, hGq⟩
  have hFd : DifferentiableAt ℝ F z.val :=
    ((f.chartMap_contDiffOn_real e.val e.property b.val b.property).differentiableOn
      one_ne_zero).differentiableAt
      ((riemannChartMapDomain_isOpen e.val f.toHomeomorph b.val
        f.toHomeomorph.continuous).mem_nhds hzF)
  have hGd : DifferentiableAt ℝ G (F z.val) :=
    ((g.chartMap_contDiffOn_real b.val b.property c.val c.property).differentiableOn
      one_ne_zero).differentiableAt
      ((riemannChartMapDomain_isOpen b.val g.toHomeomorph c.val
        g.toHomeomorph.continuous).mem_nhds hzG)
  have hFz : dz F z.val ≠ 0 := norm_pos_iff.mp
    (lt_of_le_of_lt (norm_nonneg _)
      (f.chartMap_wirtinger_lt hf e.val e.property b.val b.property hzF))
  have hGz : dz G (F z.val) ≠ 0 := norm_pos_iff.mp
    (lt_of_le_of_lt (norm_nonneg _)
      (g.chartMap_wirtinger_lt hg b.val b.property c.val c.property hzG))
  have hμF : (f.beltrami hf).coeff e z = complexDilatation F z.val :=
    f.beltrami_coeff_eq_chartDilatation hf e z b.val b.property hy
  have hμG : (g.beltrami hg).coeff b q = complexDilatation G (F z.val) :=
    g.beltrami_coeff_eq_chartDilatation hg b q c.val c.property hGq
  have hμH : ((SmoothSurfaceEquiv.trans f g).beltrami
      (hg.comp hf f.toHomeomorph.continuous)).coeff e z = complexDilatation H z.val :=
    (SmoothSurfaceEquiv.trans f g).beltrami_coeff_eq_chartDilatation
      (hg.comp hf f.toHomeomorph.continuous) e z c.val c.property hz
  have hnF : ‖complexDilatation F z.val‖ < 1 := by
    rw [← hμF]
    exact f.beltrami_coeff_norm_lt_one hf e z
  have hnG : ‖complexDilatation G (F z.val)‖ < 1 := by
    rw [← hμG]
    exact g.beltrami_coeff_norm_lt_one hg b q
  have hEq : H =ᶠ[𝓝 z.val] G ∘ F := by
    filter_upwards [(riemannChartMapDomain_isOpen e.val f.toHomeomorph b.val
      f.toHomeomorph.continuous).mem_nhds hzF] with t ht
    change c.val (g.toHomeomorph (f.toHomeomorph (e.val.symm t))) =
      c.val (g.toHomeomorph (b.val.symm (b.val (f.toHomeomorph (e.val.symm t)))))
    rw [b.val.left_inv ht.2]
  have hratio : complexDilatation H z.val = complexDilatation (G ∘ F) z.val := by
    simp only [complexDilatation, dz, dzbar, hEq.fderiv_eq]
  rw [hμH, hμF, hμG, hratio]
  exact LiZhongQC.eq6_8_complexDilatation_comp hFd hGd hFz hGz hnF hnG

/-- Algebraic inversion of the forward law, with both denominators justified. -/
private theorem solve_beltrami_fraction {a b h p : ℂ} (hp : p ≠ 0)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hh : ‖h‖ < 1)
    (heq : h = (a + b * (conj p / p)) /
      (1 + conj a * b * (conj p / p))) :
    1 - conj a * h ≠ 0 ∧
      b = (p / conj p) * ((h - a) / (1 - conj a * h)) := by
  have hsmall : ‖conj a * h‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg h]
  have hden : 1 - conj a * h ≠ 0 := by
    intro hz
    have hone : conj a * h = 1 := by linear_combination -hz
    rw [hone, norm_one] at hsmall
    exact lt_irrefl _ hsmall
  have hsmall' : ‖conj a * b * (conj p / p)‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_div, Complex.norm_conj,
      div_self (norm_ne_zero_iff.2 hp), mul_one]
    nlinarith [norm_nonneg a, norm_nonneg b]
  have hden' : 1 + conj a * b * (conj p / p) ≠ 0 := by
    intro hz
    have hneg : conj a * b * (conj p / p) = -1 := by linear_combination hz
    rw [hneg, norm_neg, norm_one] at hsmall'
    exact lt_irrefl _ hsmall'
  have hcross := (eq_div_iff hden').1 heq
  have hnum : h - a = (b * (conj p / p)) * (1 - conj a * h) := by
    linear_combination hcross
  have hquot : (h - a) / (1 - conj a * h) = b * (conj p / p) :=
    (div_eq_iff hden).2 hnum
  have hconjp : conj p ≠ 0 := by
    intro hz
    apply hp
    have hc := congrArg (fun w : ℂ => conj w) hz
    simpa only [Complex.conj_conj, map_zero] using hc
  refine ⟨hden, ?_⟩
  rw [hquot]
  field_simp [hp, hconjp]

/-- Solve for the tensor of g at f(z). The denominator is nonzero because the
actual coefficients of f and g after f both have norm below one. -/
theorem beltrami_trans_solve_coeff
    (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceEquiv S T)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation S.toRiemannAtlas T.toRiemannAtlas g.toHomeomorph)
    (e : BeltramiDifferential.Chart R.toRiemannAtlas)
    (b : BeltramiDifferential.Chart S.toRiemannAtlas)
    (c : BeltramiDifferential.Chart T.toRiemannAtlas) (z : e.val.target)
    (hy : f.toHomeomorph (e.val.symm z.val) ∈ b.val.source)
    (hz : g.toHomeomorph (f.toHomeomorph (e.val.symm z.val)) ∈ c.val.source) :
    let F := riemannChartMap e.val f.toHomeomorph b.val
    let q : b.val.target := ⟨F z.val, b.val.map_source hy⟩
    let μf := (f.beltrami hf).coeff e z
    let μg := (g.beltrami hg).coeff b q
    let μcomp := ((SmoothSurfaceEquiv.trans f g).beltrami
      (hg.comp hf f.toHomeomorph.continuous)).coeff e z
    1 - conj μf * μcomp ≠ 0 ∧
      μg = (dz F z.val / conj (dz F z.val)) *
        ((μcomp - μf) / (1 - conj μf * μcomp)) := by
  dsimp only
  let F := riemannChartMap e.val f.toHomeomorph b.val
  let q : b.val.target := ⟨F z.val, b.val.map_source hy⟩
  have hzF : z.val ∈ riemannChartMapDomain e.val f.toHomeomorph b.val := ⟨z.property, hy⟩
  have hFz : dz F z.val ≠ 0 := norm_pos_iff.mp
    (lt_of_le_of_lt (norm_nonneg _)
      (f.chartMap_wirtinger_lt hf e.val e.property b.val b.property hzF))
  exact solve_beltrami_fraction hFz
    (f.beltrami_coeff_norm_lt_one hf e z)
    (g.beltrami_coeff_norm_lt_one hg b q)
    ((SmoothSurfaceEquiv.trans f g).beltrami_coeff_norm_lt_one
      (hg.comp hf f.toHomeomorph.continuous) e z)
    (beltrami_trans_coeff f g hf hg e b c z hy hz)

end SmoothSurfaceEquiv
end LowDimensionalTopology.Geometry.Teichmuller
