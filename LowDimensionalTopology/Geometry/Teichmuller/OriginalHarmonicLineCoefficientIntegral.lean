module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicDirectionLines
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicSpatialControl
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicCoefficientIntegrals
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Tactic.Ring

/-!
# The actual WP coefficient integral on each original complex line

The genuine harmonic section on a fixed finite direction has the same
normalized symmetric map as its scalar quadratic combination. Its spatial
C1 regularity follows from the established biparameter family. The pulled
Riesz quadratic and the original WP coefficient therefore retain their
literal full-H and fundamental-region integrals along that whole line.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami HarmonicFirstVariation QuadraticBergman
open NormalizedCoefficientTransport LiZhongQC WeilPetersson

private theorem scalar_family_spatial_c1 {X : Type} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℂ, ‖s‖ < ε →
      ContDiffOn ℝ 1 (canonicalFamily R p Q s) upperHalf := by
  obtain ⟨ε, hε, hC1, _, _, _⟩ :=
    canonicalBiparameterFamily_spatial_c1_compact_control R p hp Q
  refine ⟨ε, hε, ?_⟩
  intro s hs
  have hsbar : ‖conj s‖ < ε := by simpa only [Complex.norm_conj] using hs
  have h := (hC1 s (conj s) hs hsbar).mono subset_union_left
  rw [canonicalBiparameterFamily_diagonal] at h
  exact h

private theorem normalized_integral_image {Γ : Subgroup Deck} (ν : Ball Γ)
    (F : Set ℍ) (hF : IsOpen F)
    (hd : DifferentiableOn ℝ (normalizedMap ν) upperHalf) (G : ℂ → ℂ) :
    let Ft := normalizedUpperHomeomorph ν '' F
    (IntegrableOn G (UpperHalfPlane.coe '' Ft) ↔
      IntegrableOn (fun z : ℍ => (jacobian (normalizedMap ν) z : ℂ) *
        G (normalizedMap ν z)) F flatArea) ∧
      (∫ w in UpperHalfPlane.coe '' Ft, G w) =
        ∫ z in F, (jacobian (normalizedMap ν) z : ℂ) * G (normalizedMap ν z) ∂flatArea := by
  dsimp only
  let f := normalizedMap ν
  let S := UpperHalfPlane.coe '' F
  let H : ℂ → ℂ := fun z => (jacobian f z : ℂ) * G (f z)
  have hS : MeasurableSet S := (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap F hF).measurableSet
  have hSH : S ⊆ upperHalf := by
    rintro _ ⟨z, _, rfl⟩
    exact z.im_pos
  have hdiff (w : ℂ) (hw : w ∈ upperHalf) : DifferentiableAt ℝ f w :=
    (hd w hw).differentiableAt (isOpen_upperHalf.mem_nhds hw)
  obtain ⟨Q, hQ, _⟩ := normalizedMap_spec ν
  have hinj : InjOn f S := hQ.2.2.1.2.1.mono (subset_univ S)
  have hJ (w : ℂ) (hw : w ∈ S) : |(fderiv ℝ f w).det| = jacobian f w :=
    (ar_jacobian_eq_abs_det hQ (mem_univ w) (hdiff w (hSH hw))).symm
  have himage : f '' S = UpperHalfPlane.coe '' (normalizedUpperHomeomorph ν '' F) := by
    rw [Set.image_image, Set.image_image]
    rfl
  have hsame : EqOn (fun w : ℂ => |(fderiv ℝ f w).det| • G (f w)) H S := by
    intro w hw
    dsimp only [H]
    rw [hJ w hw, Complex.real_smul]
  have hflat : IntegrableOn H S ↔ IntegrableOn (fun z : ℍ => H z) F flatArea := by
    simpa only [UpperHalfPlane.coe_injective.preimage_image, Function.comp_def, flatArea] using
      (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
        (f := H) (image_subset_range UpperHalfPlane.coe F))
  have hflatI : (∫ w in S, H w) = ∫ z in F, H z ∂flatArea := by
    have h := UpperHalfPlane.measurableEmbedding_coe.setIntegral_map
      (μ := flatArea) H S
    rw [map_flat_coe, Measure.restrict_restrict_of_subset hSH,
      UpperHalfPlane.coe_injective.preimage_image] at h
    exact h
  have hiff := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (f := f) (f' := fderiv ℝ f) hS
    (fun w hw => (hdiff w (hSH hw)).hasFDerivAt.hasFDerivWithinAt) hinj G
  rw [himage] at hiff
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume
    (f := f) (f' := fderiv ℝ f) hS
    (fun w hw => (hdiff w (hSH hw)).hasFDerivAt.hasFDerivWithinAt) hinj G
  rw [himage] at hcv
  refine ⟨hiff.trans ((integrableOn_congr_fun hsame hS).trans hflat), ?_⟩
  exact hcv.trans ((setIntegral_congr_fun hS hsame).trans hflatI)

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : IsFuchsian Γ)

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
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

/-- The unchanged kernel integral is exactly the lift of the genuine
deformed Riesz quadratic, pulled through the same normalized map. -/
theorem nativeWeilPeterssonPulledQuadratic_line_eq_riesz
    (j : I) (v : E) :
    let Q := ∑ i, conj (v i) • q i
    ∀ᶠ s : ℂ in 𝓝 0,
      ∃ ht : ‖(L).symm (s • v)‖ < 1 / 2,
        let ν := N (s • v) ht
        ∀ (P : Fuchsian.HalfPlaneFuchsianGroup
            ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
          (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (z : ℍ),
          nativeWeilPeterssonPulledQuadratic R hp hg hgenus hΓ j (s • v) z =
            uniformizedQuadratic (Y ν) (pY ν)
                (NativePetersson.toQuadratic (Y ν) P (pY ν) (hpY ν) F hF
                  (NativePetersson.rieszQuadratic (Y ν) P (pY ν) (hpY ν) F hF
                    (gammaDerivative hΓ ν (μ j))))
                (canonicalFamily R p Q s z) *
              dz (canonicalFamily R p Q s) z ^ 2 := by
  classical
  dsimp only
  let Q := ∑ i, conj (v i) • q i
  obtain ⟨ε, hε, hC1⟩ := scalar_family_spatial_c1 R hp Q
  let A : (I → ℂ) →L[ℂ] BersWeighted.Automorphic Γ := (L).symm.toContinuousLinearMap
  have hline : Continuous (fun s : ℂ => (s • v : E)) :=
    continuous_id.smul continuous_const
  have hzero : A ((0 : ℂ) • v) = 0 := by
    rw [zero_smul]
    exact A.toLinearMap.map_zero
  have hball : ∀ᶠ s : ℂ in 𝓝 0, ‖(L).symm (s • v)‖ < 1 / 2 := by
    change ∀ᶠ s : ℂ in 𝓝 0, ‖A (s • v)‖ < 1 / 2
    exact (isOpen_lt ((A.continuous.comp hline).norm) continuous_const).mem_nhds
      (by change ‖A ((0 : ℂ) • v)‖ < (1 / 2 : ℝ); rw [hzero, norm_zero]; norm_num)
  have hspatial : ∀ᶠ s : ℂ in 𝓝 0, ‖s‖ < ε :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hε)
  filter_upwards [hball, hspatial] with s ht hsε
  refine ⟨ht, ?_⟩

  intro P F hF z
  let ν : Ball Γ := N (s • v) ht
  let κ := gammaDerivative hΓ ν (μ j)
  let f := canonicalFamily R p Q s
  have hn : normalizedMap ν = f := (nativeWeilPeterssonHarmonicLine_parameter R hp hg hgenus hΓ v s ht).2
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
      K (s • v) (z : ℂ) (conj w) =
        dz f z * conj (dz f w) / (f z - conj (f w)) ^ 2 := by
    simp only [nativeWeilPeterssonDeformationKernel, coordinateFamily_complex_line]
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
    nativeWeilPeterssonPulledQuadratic R hp hg hgenus hΓ j (s • v) z =
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

variable (hfree : ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "ψ" => nativeWeilPeterssonPulledQuadratic R hp hg hgenus hΓ
local notation "h" => nativeWeilPeterssonLocalCoefficient
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

/-- Along every actual original complex line, the first WP coefficient
integral is absolutely convergent and equals the unchanged native metric. -/
theorem nativeWeilPeterssonLocalCoefficient_line_mixed_integral
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (j k : I) (v : E) :
    ∀ᶠ s : ℂ in 𝓝 0,
      IntegrableOn (fun z : ℍ => harmonicPlane R p (q j) z * ψ k (s • v) z)
        F flatArea ∧
      h j k (s • v) =
        ∫ z in F, harmonicPlane R p (q j) z * ψ k (s • v) z ∂flatArea := by
  classical
  let Q := ∑ i, conj (v i) • q i
  obtain ⟨ε, hε, hC1⟩ := scalar_family_spatial_c1 R hp Q
  have hspatial : ∀ᶠ s : ℂ in 𝓝 0, ‖s‖ < ε :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hε)
  filter_upwards [nativeWeilPeterssonPulledQuadratic_line_eq_riesz
    R hp hg hgenus hΓ k v, hspatial] with s hk hsε
  obtain ⟨ht, hψk⟩ := hk
  let ν : Ball Γ := N (s • v) ht
  let Pt := sourceHalfPlaneFuchsianGroup (deformedGroup_spec hΓ ν).1
  let Ft := normalizedUpperHomeomorph ν '' F
  have hFt : Fuchsian.IsHalfPlaneFundamentalRegion Pt Ft :=
    normalizedUpperHomeomorph_fundamentalRegion hΓ ν P Pt F hF
  let κj := gammaDerivative hΓ ν (μ j)
  let κk := gammaDerivative hΓ ν (μ k)
  let Qk := NativePetersson.rieszQuadratic (Y ν) Pt (pY ν) (hpY ν) Ft hFt κk
  let φk := uniformizedQuadratic (Y ν) (pY ν)
    (NativePetersson.toQuadratic (Y ν) Pt (pY ν) (hpY ν) Ft hFt Qk)
  let f := normalizedMap ν
  have hline := nativeWeilPeterssonHarmonicLine_parameter R hp hg hgenus hΓ v s ht
  have hf : f = canonicalFamily R p Q s := hline.2
  have hfd : DifferentiableOn ℝ f upperHalf := by
    rw [hf]
    exact (hC1 s hsε).differentiableOn_one
  have hΨk (z : ℍ) : ψ k (s • v) z = φk (f z) * dz f z ^ 2 := by
    simpa only [hf] using hψk Pt Ft hFt z
  have hμj : (μ j).val =ᵐ[volume] fun z : ℍ => harmonicPlane R p (q j) z := by
    filter_upwards [NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp (q j)] with z hz
    exact hz.trans (harmonicPlane_eq_coefficient R p (q j) z).symm
  have htrj : ∀ᵐ z : ℍ, (jacobian f z : ℂ) * κj.val (normalizedUpperEquiv ν z) =
      harmonicPlane R p (q j) z * dz f z ^ 2 := by
    filter_upwards [gammaDerivative_jacobian_conj hΓ ν (μ j), hμj] with z hz hμz
    have hc := congrArg conj hz
    simpa only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj, hμz] using hc
  have hcoef : h j k (s • v) =
      NativePetersson.pairing (Y ν) Pt (pY ν) (hpY ν) Ft hFt κj Qk :=
    (nativeWeilPeterssonLocalCoefficient_harmonicFamily R hp hg hgenus hΓ hfree hsmooth
      (s • v) ht Pt Ft hFt j k).2
  let G₁ : ℂ → ℂ := fun w => planeRepresentative κj.val w * φk w
  have hi₁ : IntegrableOn G₁ (UpperHalfPlane.coe '' Ft) := by
    apply (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
      (f := G₁) (image_subset_range UpperHalfPlane.coe Ft)).mpr
    rw [UpperHalfPlane.coe_injective.preimage_image]
    simp only [Function.comp_def, G₁, planeRepresentative_coe]
    change IntegrableOn (fun z : ℍ => κj.val z *
      NativePetersson.lift (Y ν) Pt (pY ν) (hpY ν) Ft hFt Qk z) Ft flatArea
    exact NativePetersson.pairing_integrable (Y ν) Pt (pY ν) (hpY ν) Ft hFt κj Qk
  have hc₁ := normalized_integral_image ν F hF.1 hfd G₁
  have he₁ : (fun z : ℍ => (jacobian f z : ℂ) * G₁ (f z)) =ᵐ[flatArea.restrict F]
      fun z => harmonicPlane R p (q j) z * ψ k (s • v) z := by
    filter_upwards [ae_restrict_of_ae (ae_hyperbolic_iff.mp htrj)] with z hz
    have hκ : planeRepresentative κj.val (f z) = κj.val (normalizedUpperEquiv ν z) :=
      planeRepresentative_coe κj.val (normalizedUpperEquiv ν z)
    dsimp only [G₁]
    rw [hκ, hΨk]
    calc
      _ = ((jacobian f z : ℂ) * κj.val (normalizedUpperEquiv ν z)) * φk (f z) := by ring
      _ = _ := by rw [hz]; ring
  refine ⟨(hc₁.1.mp hi₁).congr_fun_ae he₁, ?_⟩
  calc
    _ = NativePetersson.pairing (Y ν) Pt (pY ν) (hpY ν) Ft hFt κj Qk := hcoef
    _ = ∫ w in UpperHalfPlane.coe '' Ft, G₁ w :=
      NativePetersson.pairing_eq_planar (Y ν) Pt (pY ν) (hpY ν) Ft hFt κj Qk
    _ = ∫ z in F, (jacobian f z : ℂ) * G₁ (f z) ∂flatArea := hc₁.2
    _ = _ := integral_congr_ae he₁

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
