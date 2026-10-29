module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonHarmonicLocalCoefficients
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # The literal harmonic kernel integral is the actual pulled Riesz quadratic -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami HarmonicFirstVariation QuadraticBergman
open NormalizedCoefficientTransport LiZhongQC

/-- The actual coefficient transport and real Jacobian leave the conjugate
derivative square in the original normalized map. -/
theorem gammaDerivative_jacobian_conj
    {Γ : Subgroup Deck} (hΓ : IsFuchsian Γ) (ν : Ball Γ) (μ : Space Γ) :
    ∀ᵐ z : ℍ,
      (jacobian (normalizedMap ν) z : ℂ) *
          conj ((gammaDerivative hΓ ν μ).val (normalizedUpperEquiv ν z)) =
        conj (μ.val z) * conj (dz (normalizedMap ν) z) ^ 2 := by
  have htransport := (normalizedUpperEquiv_quasiMeasurePreserving ν).ae
    (ambientDerivative_coe_ae ν μ.val)
  filter_upwards [htransport, normalizedMap_dilatation_ae ν,
    coefficientDenominator_lower_ae ν, norm_derivativePhase_ae ν]
    with z ht hμ hden hphase
  have hv : (gammaDerivative hΓ ν μ).val (normalizedUpperEquiv ν z) =
      μ.val z / coefficientDenominator ν z * derivativePhase ν z := by
    simpa only [gammaDerivative_val, Equiv.symm_apply_apply, coefficientDenominator] using ht
  have ha : dz (normalizedMap ν) z ≠ 0 := by
    intro h
    simp [derivativePhase, h] at hphase
  have hb : dzbar (normalizedMap ν) z = ν.val.val z * dz (normalizedMap ν) z := by
    change dzbar (normalizedMap ν) z / dz (normalizedMap ν) z = ν.val.val z at hμ
    exact (div_eq_iff ha).mp hμ
  have hd : coefficientDenominator ν z ≠ 0 :=
    norm_pos_iff.mp ((one_sub_norm_sq_pos ν).trans_le hden)
  have hdconj : conj (coefficientDenominator ν z) = coefficientDenominator ν z := by
    simp only [coefficientDenominator, map_sub, map_one, map_mul, Complex.conj_conj]
    ring
  have hJ : (jacobian (normalizedMap ν) z : ℂ) =
      dz (normalizedMap ν) z * conj (dz (normalizedMap ν) z) *
        coefficientDenominator ν z := by
    calc
      _ = dz (normalizedMap ν) z * conj (dz (normalizedMap ν) z) -
          dzbar (normalizedMap ν) z * conj (dzbar (normalizedMap ν) z) := by
        simp only [jacobian, Complex.ofReal_sub, Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
      _ = _ := by
        rw [hb]
        simp only [map_mul, coefficientDenominator]
        ring
  rw [hv, hJ]
  simp only [map_mul, map_div₀, hdconj, derivativePhase, Complex.conj_conj]
  field_simp [ha, hd]

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : IsFuchsian Γ)

local notation "I" => Fin (3 * g - 3)
local notation "q" => nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ
local notation "L" => weightedLinearBersCoordinates R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hp
local notation "N" => nativeWeilPeterssonHarmonicParameter
  (Γ := Γ) (p := p) (g := g) R hp hg hgenus hΓ
local notation "Y" => deformedNativeSurface (Γ := Γ) (p := p) (g := g) R hgenus hΓ hp
local notation "pY" => deformedTargetCover (Γ := Γ) (p := p) (g := g) R hgenus hΓ hp
local notation "hpY" => deformedNativeSurface_uniformization
  (Γ := Γ) (p := p) (g := g) R hgenus hΓ hp
local notation "μ" => fun i : I => NativeHarmonicBeltrami.ofQuadratic R p hp (q i)
local notation "K" => nativeWeilPeterssonDeformationKernel R hp hg hgenus hΓ

/-- The actual small harmonic parameter is the same scalar coefficient axis,
with exactly the same normalized symmetric map. -/
theorem nativeWeilPeterssonHarmonicAxis_parameter (l : I) (s : ℂ)
    (ht : ‖(L).symm (Pi.single l s)‖ < 1 / 2) :
    let ν := N (Pi.single l s) ht
    (planeRepresentative ν.val.val =ᵐ[volume.restrict upperHalf]
      fun w => s * harmonicPlane R p (q l) w) ∧
      normalizedMap ν = canonicalFamily R p (q l) s := by
  classical
  dsimp only
  let ν : Ball Γ := N (Pi.single l s) ht
  have hsingle : Pi.single l s = s • Pi.single l (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using Pi.single_smul' l s (1 : ℂ)
  have hclass : ν.val = s • μ l := by
    change BersWeighted.ahlforsWeill ((L).symm (Pi.single l s)) = s • μ l
    rw [hsingle, map_smul, map_smul,
      ← nativeWeilPeterssonHarmonicFrame_section R hp hg hgenus hΓ l]
  have hsmul : (s • μ l).val = s • (μ l).val :=
    SetLike.val_smul (compatibleClosedSubmodule Γ) s (μ l)
  have hae : planeRepresentative ν.val.val =ᵐ[volume.restrict upperHalf]
      fun w => s * harmonicPlane R p (q l) w := by
    rw [hclass, hsmul]
    filter_upwards [planeRepresentative_smul_ae s (μ l).val,
      NativeHarmonicBeltrami.planeRepresentative_ofQuadratic_ae R p hp (q l)]
      with w hs hr
    have hs' : planeRepresentative (s • (μ l).val) w =
        s * planeRepresentative (μ l).val w := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hs
    have hr' : planeRepresentative (μ l).val w = harmonicPlane R p (q l) w := hr
    exact hs'.trans (congrArg (fun a : ℂ => s * a) hr')
  have hbound := planeRepresentative_isBeltramiCoeff ν.val.val
  have hraw : IsBeltramiCoeff (fun w => s * harmonicPlane R p (q l) w)
      upperHalf ‖ν.val.val‖ := by
    refine ⟨hbound.1.congr hae, ?_⟩
    filter_upwards [hae, hbound.2] with w hw hb
    rwa [← hw]
  refine ⟨hae, ?_⟩
  change s27u_fSym (planeRepresentative ν.val.val) =
    s27u_fSym (fun w => s * harmonicPlane R p (q l) w)
  exact s27u_fSym_congr_ae (norm_nonneg _) (Ball.norm_lt_one ν) hbound
    (norm_nonneg _) (Ball.norm_lt_one ν) hraw hae

/-- The unchanged kernel integral is exactly the lift of the genuine
deformed Riesz quadratic, pulled through the same normalized map. -/
theorem nativeWeilPeterssonPulledQuadratic_axis_eq_riesz
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0}) (j l : I) :
    ∀ᶠ s : ℂ in 𝓝 0,
      ∃ ht : ‖(L).symm (Pi.single l s)‖ < 1 / 2,
        let ν := N (Pi.single l s) ht
        ∀ (P : Fuchsian.HalfPlaneFuchsianGroup
            ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
          (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (z : ℍ),
          nativeWeilPeterssonPulledQuadratic R hp hg hgenus hΓ j (Pi.single l s) z =
            uniformizedQuadratic (Y ν) (pY ν)
                (NativePetersson.toQuadratic (Y ν) P (pY ν) (hpY ν) F hF
                  (NativePetersson.rieszQuadratic (Y ν) P (pY ν) (hpY ν) F hF
                    (gammaDerivative hΓ ν (μ j))))
                (canonicalFamily R p (q l) s z) *
              dz (canonicalFamily R p (q l) s) z ^ 2 := by
  classical
  obtain ⟨_, _, _, _, _, _, _, ⟨ε, hε, hC1⟩, _⟩ := hjets X R Γ p hp (q l)
  let A : (I → ℂ) →L[ℂ] BersWeighted.Automorphic Γ := (L).symm.toContinuousLinearMap
  have hsingle : Continuous (fun s : ℂ => (Pi.single l s : I → ℂ)) :=
    (ContinuousLinearMap.single ℂ (fun _ : I => ℂ) l).continuous
  have hzero : A (Pi.single l (0 : ℂ)) = 0 := by
    rw [Pi.single_zero]
    exact A.toLinearMap.map_zero
  have hball : ∀ᶠ s : ℂ in 𝓝 0, ‖(L).symm (Pi.single l s)‖ < 1 / 2 := by
    change ∀ᶠ s : ℂ in 𝓝 0, ‖A (Pi.single l s)‖ < 1 / 2
    exact (isOpen_lt ((A.continuous.comp hsingle).norm) continuous_const).mem_nhds
      (by change ‖A (Pi.single l 0)‖ < (1 / 2 : ℝ); rw [hzero, norm_zero]; norm_num)
  have hspatial : ∀ᶠ s : ℂ in 𝓝 0, ‖s‖ < ε :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hε)
  filter_upwards [hball, hspatial] with s ht hsε
  refine ⟨ht, ?_⟩
  dsimp only
  intro P F hF z
  let ν : Ball Γ := N (Pi.single l s) ht
  let κ := gammaDerivative hΓ ν (μ j)
  let f := canonicalFamily R p (q l) s
  have hn : normalizedMap ν = f := (nativeWeilPeterssonHarmonicAxis_parameter R hp hg hgenus hΓ l s ht).2
  obtain ⟨Q, hQ, _, _, _, hsymN, hupper, _⟩ := normalizedMap_spec ν
  have hqc : IsKQC f upperHalf Q := by
    simpa only [hn] using ac_t_isKQC_restrict hQ isOpen_upperHalf (subset_univ upperHalf)
  have himage : f '' upperHalf = upperHalf := by simpa only [hn] using hupper
  have hsym : ∀ w, f (conj w) = conj (f w) := by simpa only [hn] using hsymN
  have hd (w : ℂ) (hw : w ∈ upperHalf) : DifferentiableAt ℝ f w :=
    ((hC1 s hsε).differentiableOn_one w hw).differentiableAt
      (isOpen_upperHalf.mem_nhds hw)
  have hdz_reflect (w : ℂ) (hw : w ∈ upperHalf) : dz f (conj w) = conj (dz f w) := by
    have hd' : DifferentiableAt ℝ f (conj (conj w)) := by
      simpa only [Complex.conj_conj] using hd w hw
    have hfun : (fun v => conj (f (conj v))) = f := by
      funext v
      rw [hsym, Complex.conj_conj]
    simpa only [hfun, Complex.conj_conj] using (abR_x_dz_dzbar_conj hd').2.1
  have hkernel (w : ℂ) (hw : w ∈ upperHalf) :
      K (Pi.single l s) (z : ℂ) (conj w) =
        dz f z * conj (dz f w) / (f z - conj (f w)) ^ 2 := by
    simp only [nativeWeilPeterssonDeformationKernel, coordinateFamily_axis]
    change dz f z * dz f (conj w) / (f z - f (conj w)) ^ 2 = _
    rw [hsym, hdz_reflect w hw]
  have htrH : ∀ᵐ w : ℍ,
      (jacobian f w : ℂ) * conj (planeRepresentative κ.val (f w)) =
        conj (harmonicPlane R p (q j) w) * conj (dz f w) ^ 2 := by
    filter_upwards [gammaDerivative_jacobian_conj hΓ ν (μ j),
      NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp (q j)] with w hw hμ
    have he : f (w : ℂ) = (normalizedUpperEquiv ν w : ℂ) := by
      rw [normalizedUpperEquiv_coe, hn]
    rw [he, planeRepresentative_coe]
    rw [← harmonicPlane_eq_coefficient R p (q j) w] at hμ
    simpa only [hn, hμ] using hw
  have htr : (fun w : ℂ => (jacobian f w : ℂ) *
      conj (planeRepresentative κ.val (f w))) =ᵐ[volume.restrict upperHalf]
        fun w => conj (harmonicPlane R p (q j) w) * conj (dz f w) ^ 2 :=
    ae_plane_iff.mpr htrH
  have hz : f (z : ℂ) ∈ upperHalf := by
    rw [← himage]
    exact mem_image_of_mem f z.im_pos
  have hR : uniformizedQuadratic (Y ν) (pY ν)
      (NativePetersson.toQuadratic (Y ν) P (pY ν) (hpY ν) F hF
        (NativePetersson.rieszQuadratic (Y ν) P (pY ν) (hpY ν) F hF κ)) (f z) =
      (12 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf,
        conj (planeRepresentative κ.val w) / (conj w - f z) ^ 4 := by
    rw [NativePetersson.uniformized_rieszQuadratic_eq_bersDerivative
      (Y ν) P (pY ν) (hpY ν) F hF κ hz]
    unfold bersDerivative
    simp only [map_mul, map_neg, map_div₀, map_ofNat, Complex.conj_ofReal]
    rw [← integral_conj]
    simp only [map_div₀, map_pow, map_sub, Complex.conj_conj]
    ring
  have hcv : (∫ w : ℂ in upperHalf,
      conj (planeRepresentative κ.val w) / (conj w - f z) ^ 4) =
      ∫ w : ℂ in upperHalf, (jacobian f w : ℂ) *
        conj (planeRepresentative κ.val (f w)) / (conj (f w) - f z) ^ 4 := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume
      (f := f) (f' := fderiv ℝ f) isOpen_upperHalf.measurableSet
      (fun w hw => (hd w hw).hasFDerivAt.hasFDerivWithinAt) hqc.2.2.1.2.1
      (fun w : ℂ => conj (planeRepresentative κ.val w) / (conj w - f z) ^ 4)
    rw [himage] at h
    rw [h]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet] with w hw
    rw [← ar_jacobian_eq_abs_det hqc hw (hd w hw)]
    simp only [Complex.real_smul]
    ring
  have hcv' : (∫ w : ℂ in upperHalf,
      conj (planeRepresentative κ.val w) / (conj w - f z) ^ 4) =
      ∫ w : ℂ in upperHalf, conj (harmonicPlane R p (q j) w) *
        conj (dz f w) ^ 2 / (conj (f w) - f z) ^ 4 := by
    rw [hcv]
    apply integral_congr_ae
    filter_upwards [htr] with w hw
    rw [hw]
  calc
    nativeWeilPeterssonPulledQuadratic R hp hg hgenus hΓ j (Pi.single l s) z =
        (12 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf,
          (conj (harmonicPlane R p (q j) w) * conj (dz f w) ^ 2 /
            (conj (f w) - f z) ^ 4) * dz f z ^ 2 := by
      unfold nativeWeilPeterssonPulledQuadratic
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet] with w hw
      rw [hkernel w hw]
      have hpow : (f z - conj (f w)) ^ 4 = (conj (f w) - f z) ^ 4 := by ring
      simp only [div_pow, mul_pow, ← pow_mul]
      norm_num only [Nat.reduceMul]
      rw [hpow]
      ring
    _ = ((12 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf,
          conj (harmonicPlane R p (q j) w) * conj (dz f w) ^ 2 /
            (conj (f w) - f z) ^ 4) * dz f z ^ 2 := by
      rw [integral_mul_const]
      ring
    _ = _ := by rw [← hcv', ← hR]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
