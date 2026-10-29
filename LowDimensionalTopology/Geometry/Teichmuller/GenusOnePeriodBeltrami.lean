module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneSmoothPeriodMarking
public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneAtlasBeltramiPairing
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# The original-atlas Beltrami coefficient of the actual period marking

Both covering charts come from the existing analytic local-sheet theorem.
The covering equation identifies the coordinate map with the actual affine
lift. Conformal pre- and post-composition account for the source tensor phase.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

private theorem affineLift_dilatation_eq (τ : ℍ) (t z : ℂ) :
    LiZhongQC.complexDilatation (affineLift τ t) z = affineBeltrami τ t := by
  let a := 1 + t / periodGap τ
  let b := -t / periodGap τ
  have hd : HasFDerivAt (affineLift τ t)
      (a • ContinuousLinearMap.id ℝ ℂ + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z :=
    ((hasFDerivAt_id z).const_mul a).add
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.const_mul b)
  have hdz : LiZhongQC.dz (affineLift τ t) z = a := by
    rw [LiZhongQC.dz, hd.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
      map_one, Complex.conj_I]
    linear_combination ((b - a) / 2) * Complex.I_sq
  have hdzbar : LiZhongQC.dzbar (affineLift τ t) z = b := by
    rw [LiZhongQC.dzbar, hd.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
      map_one, Complex.conj_I]
    linear_combination ((a - b) / 2) * Complex.I_sq
  rw [LiZhongQC.complexDilatation, hdz, hdzbar]
  rfl

/-- The Beltrami tensor of the actual marked torus map has precisely the
affine coefficient on the original plane cover, at every point. -/
theorem torusCoverBeltramiValue_periodMarking (τ σ : ℍ) (z : ℂ) :
    torusCoverBeltramiValue τ
      ((periodMarking τ σ).beltrami (periodMarking_spec τ σ).1) z =
        affineBeltrami τ ((σ : ℂ) - (τ : ℂ)) := by
  let A := (normalizedTorusModel τ).surface.toRiemannAtlas
  let B := (normalizedTorusModel σ).surface.toRiemannAtlas
  let p := (normalizedTorusModel τ).projection
  let q := (normalizedTorusModel σ).projection
  let f := periodMarking τ σ
  let hf := (periodMarking_spec τ σ).1
  let L := periodChange τ σ
  let c := A.cover (p z)
  let e : BeltramiDifferential.Chart A := ⟨c.choose, c.choose_spec.1⟩
  have he : p z ∈ e.val.source := c.choose_spec.2
  let d := B.cover (f.toHomeomorph (p z))
  let g : BeltramiDifferential.Chart B := ⟨d.choose, d.choose_spec.1⟩
  have hg : f.toHomeomorph (p z) ∈ g.val.source := d.choose_spec.2
  have hcover (w : ℂ) : f.toHomeomorph (p w) = q (L w) :=
    (periodMarking_spec τ σ).2 w
  have hgq : q (L z) ∈ g.val.source := by
    rw [← hcover z]
    exact hg
  let r : ℂ → ℂ := e.val ∘ p
  let s : ℂ → ℂ := g.val ∘ q
  let F : ℂ → ℂ := riemannChartMap e.val f.toHomeomorph g.val
  obtain ⟨P, hPfun, hzP, hPa, _hPsub⟩ :=
    analyticLocalHomeomorph_coordinateSheet (normalizedTorusModel τ).analytic_projection
      (normalizedTorusModel τ).covering.isLocalHomeomorph
      (OpenPartialHomeomorph.refl ℂ) rfl e.val e.property z (by trivial) he
  have hPr : (P : ℂ → ℂ) = r := by
    simpa [riemannChartMap, r, Function.comp_def] using hPfun
  have hr : DifferentiableAt ℂ r z := by
    rw [← hPr]
    exact (hPa z hzP).differentiableAt
  have hdr : deriv r z ≠ 0 := normalizedTorusCoverChart_deriv_ne_zero τ e z he
  obtain ⟨Q, hQfun, hzQ, hQa, _hQsub⟩ :=
    analyticLocalHomeomorph_coordinateSheet (normalizedTorusModel σ).analytic_projection
      (normalizedTorusModel σ).covering.isLocalHomeomorph
      (OpenPartialHomeomorph.refl ℂ) rfl g.val g.property (L z) (by trivial) hgq
  have hQs : (Q : ℂ → ℂ) = s := by
    simpa [riemannChartMap, s, Function.comp_def] using hQfun
  have hs : DifferentiableAt ℂ s (L z) := by
    rw [← hQs]
    exact (hQa (L z) hzQ).differentiableAt
  have hds : deriv s (L z) ≠ 0 := normalizedTorusCoverChart_deriv_ne_zero σ g (L z) hgq
  have hzF : r z ∈ riemannChartMapDomain e.val f.toHomeomorph g.val := by
    refine ⟨e.val.map_source he, ?_⟩
    change f.toHomeomorph (e.val.symm (e.val (p z))) ∈ g.val.source
    rwa [e.val.left_inv he]
  have hF : DifferentiableAt ℝ F (r z) :=
    ((f.chartMap_contDiffOn_real e.val e.property g.val g.property).differentiableOn
      one_ne_zero).differentiableAt
        ((riemannChartMapDomain_isOpen e.val f.toHomeomorph g.val
          f.toHomeomorph.continuous).mem_nhds hzF)
  let w : e.val.target := ⟨e.val (p z), e.val.map_source he⟩
  have hgw : f.toHomeomorph (e.val.symm w.val) ∈ g.val.source := by
    simpa only [w, e.val.left_inv he] using hg
  have hμ := f.beltrami_coeff_eq_chartDilatation hf e w g.val g.property hgw
  have hp : Continuous p := (normalizedTorusModel τ).analytic_projection.1
  have heq : F ∘ r =ᶠ[𝓝 z] s ∘ L := by
    filter_upwards [(e.val.open_source.preimage hp).mem_nhds he] with v hv
    change g.val (f.toHomeomorph (e.val.symm (e.val (p v)))) = g.val (q (L v))
    rw [e.val.left_inv hv, hcover v]
  have hcomp : LiZhongQC.complexDilatation (F ∘ r) z =
      LiZhongQC.complexDilatation (s ∘ L) z := by
    have hderiv := heq.fderiv_eq (𝕜 := ℝ)
    simp only [LiZhongQC.complexDilatation, LiZhongQC.dz, LiZhongQC.dzbar, hderiv]
  have hLaff : (L : ℂ → ℂ) = affineLift τ ((σ : ℂ) - (τ : ℂ)) :=
    funext (periodChange_eq_affineLift τ σ)
  change (f.beltrami hf).coeff e w * conj (deriv r z) / deriv r z = _
  rw [hμ]
  calc
    LiZhongQC.complexDilatation F (r z) * conj (deriv r z) / deriv r z =
        LiZhongQC.complexDilatation (F ∘ r) z := by
      simpa only [mul_div_assoc] using
        (LiZhongQC.complexDilatation_comp_conformal_right hr hdr hF).symm
    _ = LiZhongQC.complexDilatation (s ∘ L) z := hcomp
    _ = LiZhongQC.complexDilatation (L : ℂ → ℂ) z :=
      LiZhongQC.complexDilatation_comp_conformal_left L.differentiableAt hs hds
    _ = affineBeltrami τ ((σ : ℂ) - (τ : ℂ)) := by
      rw [hLaff]
      exact affineLift_dilatation_eq τ _ z

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
