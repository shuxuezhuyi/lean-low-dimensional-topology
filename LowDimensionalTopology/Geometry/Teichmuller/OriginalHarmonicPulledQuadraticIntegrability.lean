module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonHarmonicVariations
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Actual local convergence of the harmonic pulled-quadratic integral -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami HarmonicFirstVariation LiZhongQC

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : IsFuchsian Γ)

local notation "q" => nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ
local notation "K" => nativeWeilPeterssonDeformationKernel R hp hg hgenus hΓ

/-- The literal full-half-plane integral converges absolutely throughout an
actual parameter neighbourhood of each original harmonic coordinate axis. -/
theorem nativeWeilPeterssonPulledQuadratic_axis_eventually_integrable
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (j l : Fin (3 * g - 3)) :
    ∀ᶠ s : ℂ in 𝓝 0, ∀ z : ℍ,
      IntegrableOn (fun ζ : ℂ => K (Pi.single l s) (z : ℂ) (conj ζ) ^ 2 *
        conj (harmonicPlane R p (q j) ζ)) upperHalf := by
  classical
  let M (i : Fin (3 * g - 3)) :=
    ‖(NativeHarmonicBeltrami.ofQuadratic R p hp (q i)).val‖
  have hM (i : Fin (3 * g - 3)) : 0 ≤ M i := norm_nonneg _
  have hraw (i : Fin (3 * g - 3)) :
      IsBeltramiCoeff (harmonicPlane R p (q i)) upperHalf (M i) := by
    have hμ := planeRepresentative_isBeltramiCoeff
      (NativeHarmonicBeltrami.ofQuadratic R p hp (q i)).val
    have hae : planeRepresentative
        (NativeHarmonicBeltrami.ofQuadratic R p hp (q i)).val
          =ᵐ[volume.restrict upperHalf] harmonicPlane R p (q i) :=
      NativeHarmonicBeltrami.planeRepresentative_ofQuadratic_ae R p hp (q i)
    refine ⟨hμ.1.congr hae, ?_⟩
    filter_upwards [hae, hμ.2] with w hw hb
    rwa [← hw]
  obtain ⟨_, _, _, _, _, _, _, ⟨ε, hε, hC1⟩, _⟩ := hjets X R Γ p hp (q l)
  have hsmall : ∀ᶠ s : ℂ in 𝓝 0, ‖s‖ * M l < 1 :=
    (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).mem_nhds (by simp)
  have hspatial : ∀ᶠ s : ℂ in 𝓝 0, ‖s‖ < ε :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hε)
  filter_upwards [hsmall, hspatial] with s hs hsε
  intro z
  let f := canonicalFamily R p (q l) s
  let k := ‖s‖ * M l
  let Q := (1 + k) / (1 - k)
  have hcoeff : IsBeltramiCoeff
      (fun w => s * harmonicPlane R p (q l) w) upperHalf k := by
    refine ⟨(hraw l).1.const_mul s, ?_⟩
    filter_upwards [(hraw l).2] with w hw
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left hw (norm_nonneg s)
  have hmap := fMuSym_upperHalf (mul_nonneg (norm_nonneg s) (hM l)) hs hcoeff
  have himage : f '' upperHalf = upperHalf := hmap.1
  have hsym : ∀ w, f (conj w) = conj (f w) := hmap.2.2.1
  have hqc : IsKQC f upperHalf Q := hmap.2.2.2.1
  have hd (w : ℂ) (hw : w ∈ upperHalf) : DifferentiableAt ℝ f w :=
    ((hC1 s hsε).differentiableOn_one w hw).differentiableAt
      (isOpen_upperHalf.mem_nhds hw)
  have hdz_reflect (w : ℂ) (hw : w ∈ upperHalf) :
      dz f (conj w) = conj (dz f w) := by
    have hd' : DifferentiableAt ℝ f (conj (conj w)) := by
      simpa only [Complex.conj_conj] using hd w hw
    have hfun : (fun v => conj (f (conj v))) = f := by
      funext v
      rw [hsym, Complex.conj_conj]
    have h := (abR_x_dz_dzbar_conj hd').2.1
    simpa only [hfun, Complex.conj_conj] using h
  have hkernel (w : ℂ) (hw : w ∈ upperHalf) :
      K (Pi.single l s) (z : ℂ) (conj w) =
        dz f z * conj (dz f w) / (f z - conj (f w)) ^ 2 := by
    simp only [nativeWeilPeterssonDeformationKernel, coordinateFamily_axis]
    change dz f z * dz f (conj w) / (f z - f (conj w)) ^ 2 = _
    rw [hsym, hdz_reflect w hw]
  have hJ (w : ℂ) (hw : w ∈ upperHalf) : 0 ≤ jacobian f w := by
    rw [ar_jacobian_eq_abs_det hqc hw (hd w hw)]
    exact abs_nonneg _
  have hsq (w : ℂ) (hw : w ∈ upperHalf) : ‖dz f w‖ ^ 2 ≤ Q * jacobian f w := by
    have h := ac_t_dilatation_of_differentiableAt hqc hw (hd w hw)
    have hm := mul_le_mul_of_nonneg_right h
      (add_nonneg (norm_nonneg (dz f w)) (norm_nonneg (dzbar f w)))
    unfold jacobian
    nlinarith [mul_nonneg (norm_nonneg (dz f w)) (norm_nonneg (dzbar f w)),
      sq_nonneg ‖dzbar f w‖]
  have hz : f (z : ℂ) ∈ upperHalf := by
    rw [← himage]
    exact mem_image_of_mem f z.im_pos
  have hcz : conj (f (z : ℂ)) ∈ lowerHalf := by
    change (conj (f (z : ℂ))).im < 0
    simpa only [Complex.conj_im] using neg_lt_zero.mpr hz
  have hfourth : IntegrableOn
      (fun w : ℂ => ‖w - conj (f (z : ℂ))‖⁻¹ ^ 4) upperHalf := by
    have h := BersWeighted.fourthKernel_mul_integrable
      (κ := fun _ : ℂ => (1 : ℂ)) (M := 1) aestronglyMeasurable_const
      (Eventually.of_forall fun _ => by simp) hcz
    refine h.norm.congr (Eventually.of_forall fun w => ?_)
    change ‖(1 : ℂ) / (w - conj (f (z : ℂ))) ^ 4‖ =
      ‖w - conj (f (z : ℂ))‖⁻¹ ^ 4
    rw [one_div, norm_inv, norm_pow, inv_pow]
  have hpull : IntegrableOn (fun w : ℂ =>
      jacobian f w * ‖f w - conj (f (z : ℂ))‖⁻¹ ^ 4) upperHalf := by
    have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      (f := f) (f' := fderiv ℝ f) isOpen_upperHalf.measurableSet
      (fun w hw => (hd w hw).hasFDerivAt.hasFDerivWithinAt) hqc.2.2.1.2.1
      (fun w : ℂ => ‖w - conj (f (z : ℂ))‖⁻¹ ^ 4)).mp (by
        rw [himage]
        exact hfourth)
    refine h.congr_fun (fun w hw => ?_) isOpen_upperHalf.measurableSet
    dsimp only
    rw [← ar_jacobian_eq_abs_det hqc hw (hd w hw), smul_eq_mul]
  have hfm : AEStronglyMeasurable f (volume.restrict upperHalf) :=
    hqc.2.2.1.1.aestronglyMeasurable isOpen_upperHalf.measurableSet
  have hdm : AEStronglyMeasurable (dz f) (volume.restrict upperHalf) :=
    (measurable_dz f).aestronglyMeasurable.restrict
  have hm : AEStronglyMeasurable
      (fun w : ℂ => (dz f z * conj (dz f w) / (f z - conj (f w)) ^ 2) ^ 2 *
        conj (harmonicPlane R p (q j) w)) (volume.restrict upperHalf) := by
    have hnum : AEStronglyMeasurable (fun w : ℂ => dz f z * conj (dz f w))
        (volume.restrict upperHalf) :=
      aestronglyMeasurable_const.mul
        (Complex.continuous_conj.comp_aestronglyMeasurable hdm)
    have hden : AEStronglyMeasurable (fun w : ℂ => (f z - conj (f w)) ^ 2)
        (volume.restrict upperHalf) :=
      (aestronglyMeasurable_const.sub
        (Complex.continuous_conj.comp_aestronglyMeasurable hfm)).pow 2
    exact ((hnum.div₀ hden).pow 2).mul
      (Complex.continuous_conj.comp_aestronglyMeasurable (hraw j).1)
  have hint : IntegrableOn
      (fun w : ℂ => (dz f z * conj (dz f w) / (f z - conj (f w)) ^ 2) ^ 2 *
        conj (harmonicPlane R p (q j) w)) upperHalf := by
    apply (hpull.const_mul (‖dz f z‖ ^ 2 * Q * M j)).mono' hm
    filter_upwards [(hraw j).2, ae_restrict_mem isOpen_upperHalf.measurableSet] with w hw hwH
    have hden : ‖f z - conj (f w)‖ = ‖f w - conj (f z)‖ := by
      rw [← Complex.norm_conj (f z - conj (f w)), map_sub, Complex.conj_conj,
        norm_sub_rev]
    have he : ‖(dz f z * conj (dz f w) / (f z - conj (f w)) ^ 2) ^ 2 *
        conj (harmonicPlane R p (q j) w)‖ =
        ‖dz f z‖ ^ 2 * ‖dz f w‖ ^ 2 * ‖harmonicPlane R p (q j) w‖ *
          ‖f w - conj (f z)‖⁻¹ ^ 4 := by
      simp only [norm_mul, norm_pow, norm_div, Complex.norm_conj]
      rw [hden]
      simp only [div_eq_mul_inv, mul_pow, inv_pow, ← pow_mul]
      ring
    rw [he]
    have hQ : 0 ≤ Q := zero_le_one.trans hqc.2.1
    calc
      _ ≤ ‖dz f z‖ ^ 2 * (Q * jacobian f w) * M j *
          ‖f w - conj (f z)‖⁻¹ ^ 4 := by
        have h₁ := mul_le_mul_of_nonneg_left (hsq w hwH) (sq_nonneg ‖dz f z‖)
        have h₂ := mul_le_mul h₁ hw (norm_nonneg _)
          (mul_nonneg (sq_nonneg _) (mul_nonneg hQ (hJ w hwH)))
        exact mul_le_mul_of_nonneg_right h₂ (by positivity)
      _ = (‖dz f z‖ ^ 2 * Q * M j) *
          (jacobian f w * ‖f w - conj (f z)‖⁻¹ ^ 4) := by ring
  refine hint.congr_fun (fun w hw => ?_) isOpen_upperHalf.measurableSet
  exact (congrArg (fun c : ℂ => c ^ 2 * conj (harmonicPlane R p (q j) w))
    (hkernel w hw)).symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
