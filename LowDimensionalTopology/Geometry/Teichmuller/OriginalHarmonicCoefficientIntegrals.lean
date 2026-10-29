module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPulledQuadraticRiesz
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalNormalizedFundamentalRegion
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # The two actual harmonic WP coefficient integral representations -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami HarmonicFirstVariation QuadraticBergman
open NormalizedCoefficientTransport LiZhongQC WeilPetersson

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
    (hfree : ActsFreely Γ) (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3 * g - 3)
local notation "q" => nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ
local notation "N" => nativeWeilPeterssonHarmonicParameter
  (Γ := Γ) (p := p) (g := g) R hp hg hgenus hΓ
local notation "Y" => deformedNativeSurface (Γ := Γ) (p := p) (g := g) R hgenus hΓ hp
local notation "pY" => deformedTargetCover (Γ := Γ) (p := p) (g := g) R hgenus hΓ hp
local notation "hpY" => deformedNativeSurface_uniformization
  (Γ := Γ) (p := p) (g := g) R hgenus hΓ hp
local notation "μ" => fun i : I => NativeHarmonicBeltrami.ofQuadratic R p hp (q i)
local notation "ψ" => nativeWeilPeterssonPulledQuadratic R hp hg hgenus hΓ
local notation "h" => nativeWeilPeterssonLocalCoefficient
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

/-- Both literal WP coefficient integrals hold on every original genuine
region, with absolute convergence and the actual transported density. -/
theorem nativeWeilPeterssonLocalCoefficient_axis_integral_representations
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (j k l : I) :
    ∀ᶠ s : ℂ in 𝓝 0,
      IntegrableOn (fun z : ℍ => harmonicPlane R p (q j) z * ψ k (Pi.single l s) z)
        F flatArea ∧
      IntegrableOn (fun z : ℍ => ψ k (Pi.single l s) z * conj (ψ j (Pi.single l s) z) *
          (((1 - ‖s * harmonicPlane R p (q l) z‖ ^ 2) ^ 2 : ℝ) : ℂ) /
            (coordinateDensity R p q (Pi.single l s) z : ℂ)) F flatArea ∧
      h j k (Pi.single l s) =
        ∫ z in F, harmonicPlane R p (q j) z * ψ k (Pi.single l s) z ∂flatArea ∧
      h j k (Pi.single l s) =
        ∫ z in F, ψ k (Pi.single l s) z * conj (ψ j (Pi.single l s) z) *
          (((1 - ‖s * harmonicPlane R p (q l) z‖ ^ 2) ^ 2 : ℝ) : ℂ) /
            (coordinateDensity R p q (Pi.single l s) z : ℂ) ∂flatArea := by
  classical
  obtain ⟨_, _, _, _, _, _, _, ⟨ε, hε, hC1⟩, _⟩ := hjets X R Γ p hp (q l)
  have hspatial : ∀ᶠ s : ℂ in 𝓝 0, ‖s‖ < ε :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hε)
  filter_upwards [nativeWeilPeterssonPulledQuadratic_axis_eq_riesz
    R hp hg hgenus hΓ hjets j l,
    nativeWeilPeterssonPulledQuadratic_axis_eq_riesz R hp hg hgenus hΓ hjets k l,
    hspatial] with s hj hk hsε
  obtain ⟨ht, hψj⟩ := hj
  obtain ⟨ht', hψk⟩ := hk
  let ν : Ball Γ := N (Pi.single l s) ht
  let Pt := sourceHalfPlaneFuchsianGroup (deformedGroup_spec hΓ ν).1
  let Ft := normalizedUpperHomeomorph ν '' F
  have hFt : Fuchsian.IsHalfPlaneFundamentalRegion Pt Ft :=
    normalizedUpperHomeomorph_fundamentalRegion hΓ ν P Pt F hF
  let κj := gammaDerivative hΓ ν (μ j)
  let κk := gammaDerivative hΓ ν (μ k)
  let Qj := NativePetersson.rieszQuadratic (Y ν) Pt (pY ν) (hpY ν) Ft hFt κj
  let Qk := NativePetersson.rieszQuadratic (Y ν) Pt (pY ν) (hpY ν) Ft hFt κk
  let φj := uniformizedQuadratic (Y ν) (pY ν)
    (NativePetersson.toQuadratic (Y ν) Pt (pY ν) (hpY ν) Ft hFt Qj)
  let φk := uniformizedQuadratic (Y ν) (pY ν)
    (NativePetersson.toQuadratic (Y ν) Pt (pY ν) (hpY ν) Ft hFt Qk)
  let f := normalizedMap ν
  let δ : ℍ → ℝ := fun z => 1 - ‖s * harmonicPlane R p (q l) z‖ ^ 2
  let ρ := coordinateDensity R p q (Pi.single l s)
  have haxis := nativeWeilPeterssonHarmonicAxis_parameter R hp hg hgenus hΓ l s ht
  have hf : f = canonicalFamily R p (q l) s := haxis.2
  have hfd : DifferentiableOn ℝ f upperHalf := by
    rw [hf]
    exact (hC1 s hsε).differentiableOn_one
  have hΨj (z : ℍ) : ψ j (Pi.single l s) z = φj (f z) * dz f z ^ 2 := by
    simpa only [hf] using hψj Pt Ft hFt z
  have hΨk (z : ℍ) : ψ k (Pi.single l s) z = φk (f z) * dz f z ^ 2 := by
    simpa only [hf] using hψk Pt Ft hFt z
  have hρ (z : ℍ) : ρ z = jacobian f z / (f z).im ^ 2 := by
    simp only [ρ, coordinateDensity, coordinateFamily_axis, ← hf]
  have hν : ν.val.val =ᵐ[volume] fun z : ℍ => s * harmonicPlane R p (q l) z := by
    filter_upwards [ae_plane_iff.mp haxis.1] with z hz
    simpa only [planeRepresentative_coe] using hz
  have hμj : (μ j).val =ᵐ[volume] fun z : ℍ => harmonicPlane R p (q j) z := by
    filter_upwards [NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp (q j)] with z hz
    exact hz.trans (harmonicPlane_eq_coefficient R p (q j) z).symm
  have htrj : ∀ᵐ z : ℍ, (jacobian f z : ℂ) * κj.val (normalizedUpperEquiv ν z) =
      harmonicPlane R p (q j) z * dz f z ^ 2 := by
    filter_upwards [gammaDerivative_jacobian_conj hΓ ν (μ j), hμj] with z hz hμz
    have hc := congrArg conj hz
    simpa only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj, hμz] using hc
  have hcoef : h j k (Pi.single l s) =
      NativePetersson.pairing (Y ν) Pt (pY ν) (hpY ν) Ft hFt κj Qk :=
    (nativeWeilPeterssonLocalCoefficient_harmonicFamily R hp hg hgenus hΓ hfree hsmooth
      (Pi.single l s) ht Pt Ft hFt j k).2
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
      fun z => harmonicPlane R p (q j) z * ψ k (Pi.single l s) z := by
    filter_upwards [ae_restrict_of_ae (ae_hyperbolic_iff.mp htrj)] with z hz
    have hκ : planeRepresentative κj.val (f z) = κj.val (normalizedUpperEquiv ν z) :=
      planeRepresentative_coe κj.val (normalizedUpperEquiv ν z)
    dsimp only [G₁]
    rw [hκ, hΨk]
    calc
      _ = ((jacobian f z : ℂ) * κj.val (normalizedUpperEquiv ν z)) * φk (f z) := by ring
      _ = _ := by rw [hz]; ring
  have hiMixed : IntegrableOn
      (fun z : ℍ => harmonicPlane R p (q j) z * ψ k (Pi.single l s) z) F flatArea :=
    (hc₁.1.mp hi₁).congr_fun_ae he₁
  have heMixed : h j k (Pi.single l s) =
      ∫ z in F, harmonicPlane R p (q j) z * ψ k (Pi.single l s) z ∂flatArea := by
    calc
      _ = NativePetersson.pairing (Y ν) Pt (pY ν) (hpY ν) Ft hFt κj Qk := hcoef
      _ = ∫ w in UpperHalfPlane.coe '' Ft, G₁ w :=
        NativePetersson.pairing_eq_planar (Y ν) Pt (pY ν) (hpY ν) Ft hFt κj Qk
      _ = ∫ z in F, (jacobian f z : ℂ) * G₁ (f z) ∂flatArea := hc₁.2
      _ = _ := integral_congr_ae he₁
  let G₂ : ℂ → ℂ := fun w => ((w.im ^ 2 : ℝ) : ℂ) * φk w * conj (φj w)
  have hi₂ : IntegrableOn G₂ (UpperHalfPlane.coe '' Ft) := by
    apply (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
      (f := G₂) (image_subset_range UpperHalfPlane.coe Ft)).mpr
    rw [UpperHalfPlane.coe_injective.preimage_image]
    exact quadratic_integrand_integrableOn_fundamental (Y ν) Pt (pY ν) (hpY ν) hFt
      (NativePetersson.toQuadratic (Y ν) Pt (pY ν) (hpY ν) Ft hFt Qk)
      (NativePetersson.toQuadratic (Y ν) Pt (pY ν) (hpY ν) Ft hFt Qj)
  let J := InnerProductSpace.toDual ℂ
    (NativePetersson.Space (Y ν) Pt (pY ν) (hpY ν) Ft hFt)
  have hRiesz : J Qj = NativePetersson.pairingMap (Y ν) Pt (pY ν) (hpY ν) Ft hFt κj := by
    dsimp only [Qj, NativePetersson.rieszQuadratic]
    exact J.apply_symm_apply _
  have hcoef₂ : h j k (Pi.single l s) = ∫ w in UpperHalfPlane.coe '' Ft, G₂ w := by
    have hm := UpperHalfPlane.measurableEmbedding_coe.setIntegral_map
      («μ» := flatArea) G₂ (UpperHalfPlane.coe '' Ft)
    have hsub : UpperHalfPlane.coe '' Ft ⊆ upperHalf := by
      rintro _ ⟨z, _, rfl⟩
      exact z.im_pos
    rw [map_flat_coe, Measure.restrict_restrict_of_subset hsub,
      UpperHalfPlane.coe_injective.preimage_image] at hm
    calc
      _ = J Qj Qk := by
        rw [hRiesz, NativePetersson.pairingMap_apply]
        exact hcoef
      _ = ∫ z in Ft, G₂ z ∂flatArea :=
        NativePetersson.inner_eq_integral (Y ν) Pt (pY ν) (hpY ν) Ft hFt Qj Qk
      _ = _ := hm.symm
  have hJδ : ∀ᵐ z : ℍ,
      (jacobian f z : ℂ) = dz f z * conj (dz f z) * (δ z : ℂ) ∧
        dz f z ≠ 0 ∧ (δ z : ℂ) ≠ 0 := by
    filter_upwards [normalizedMap_dilatation_ae ν, norm_derivativePhase_ae ν,
      lpInfinity_norm_ae_le ν.val.val, hν] with z hd hphase hnorm hνz
    have ha : dz f z ≠ 0 := by
      intro hz
      simp [derivativePhase, f, hz] at hphase
    have hb : dzbar f z = (s * harmonicPlane R p (q l) z) * dz f z := by
      change dzbar f z / dz f z = ν.val.val z at hd
      rw [hνz] at hd
      exact (div_eq_iff ha).mp hd
    have hnlt : ‖s * harmonicPlane R p (q l) z‖ < 1 := by
      rw [← hνz]
      exact hnorm.trans_lt (Ball.norm_lt_one ν)
    have hδ : 0 < δ z := by
      dsimp only [δ]
      nlinarith [norm_nonneg (s * harmonicPlane R p (q l) z)]
    have hJ : jacobian f z = ‖dz f z‖ ^ 2 * δ z := by
      rw [jacobian, hb, norm_mul, mul_pow]
      dsimp only [δ]
      ring
    refine ⟨?_, ha, Complex.ofReal_ne_zero.mpr hδ.ne'⟩
    rw [hJ, Complex.ofReal_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hc₂ := normalized_integral_image ν F hF.1 hfd G₂
  have he₂ : (fun z : ℍ => (jacobian f z : ℂ) * G₂ (f z)) =ᵐ[flatArea.restrict F]
      fun z => ψ k (Pi.single l s) z * conj (ψ j (Pi.single l s) z) *
        ((δ z : ℂ) ^ 2) / (ρ z : ℂ) := by
    filter_upwards [ae_restrict_of_ae (ae_hyperbolic_iff.mp hJδ)] with z hz
    obtain ⟨hJ, ha, hδ⟩ := hz
    have hca : conj (dz f z) ≠ 0 := star_ne_zero.mpr ha
    have hheight : (f z).im > 0 := normalizedMap_mapsTo_upper ν z.im_pos
    have hh : ((f z).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hheight.ne'
    have hρc : (ρ z : ℂ) = (jacobian f z : ℂ) / ((f z).im : ℂ) ^ 2 := by
      rw [hρ, Complex.ofReal_div, Complex.ofReal_pow]
    dsimp only [G₂]
    rw [hΨk, hΨj, hρc, hJ]
    simp only [map_mul, map_pow, Complex.ofReal_pow]
    field_simp [ha, hca, hδ, hh]
  have hiDouble : IntegrableOn
      (fun z : ℍ => ψ k (Pi.single l s) z * conj (ψ j (Pi.single l s) z) *
        (δ z : ℂ) ^ 2 / (ρ z : ℂ)) F flatArea :=
    (hc₂.1.mp hi₂).congr_fun_ae he₂
  have heDouble : h j k (Pi.single l s) =
      ∫ z in F, ψ k (Pi.single l s) z * conj (ψ j (Pi.single l s) z) *
        (δ z : ℂ) ^ 2 / (ρ z : ℂ) ∂flatArea :=
    hcoef₂.trans (hc₂.2.trans (integral_congr_ae he₂))
  simpa only [δ, ρ, Complex.ofReal_pow] using
    And.intro hiMixed (And.intro hiDouble (And.intro heMixed heDouble))

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
