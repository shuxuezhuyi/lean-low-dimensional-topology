module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonIntegral
public import LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton

/-!
# Reproducing kernels and the actual quadratic-differential annihilator

The quadratic differentials belong to the original complex atlas. Their actual
uniformizing lifts are integrable over every fundamental domain, by unfolding a
compact orbit cover. The half-plane reproducing formula has coefficient `12/π`.
The infinitesimal kernel theorem uses the full bounded measurable deck-compatible
Banach space, without restricting its norm to the quasiconformal unit ball.

The analytic proofs adapt Wu Xiaobin's Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0),
`UniformizedUniqueness.lean` (lift/descent) and `S36_Hamilton.lean` (unfolding,
reproducing kernels and kernel orthogonality). See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter Topology MeasureTheory
open scoped ENNReal Manifold ContDiff ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergman

open Surfaces LiZhongQC
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)

/-- The actual coefficient of the original quadratic differential pulled back
by the given uniformizing map, extended by the source's chart formula on `ℂ`. -/
def uniformizedQuadratic (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) : ℂ → ℂ :=
  let := R.toRiemannAtlas.toChartedSpace
  utm_liftQD (q : X → ℂ → ℂ) p

/-- The lift satisfies the literal weight-four automorphic equation. -/
theorem uniformizedQuadratic_automorphic
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      uniformizedQuadratic R p q
          (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) /
        ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = uniformizedQuadratic R p q z := by
  let := R.toRiemannAtlas.toChartedSpace
  intro γ hγ z hz
  dsimp only [uniformizedQuadratic]
  change utm_liftQD (q : X → ℂ → ℂ) p (utm_b_mob γ z) /
    ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = utm_liftQD (q : X → ℂ → ℂ) p z
  have h := utm_b_liftQD_automorphic (q : X → ℂ → ℂ) hp hγ hz
  generalize ((γ 1 0 : ℂ) * z + γ 1 1) = d at h ⊢
  rw [← h]
  ring

/-- Compactness of the original surface supplies the weighted bound used in
the reproducing formula; no bound on the differential is an extra premise. -/
theorem uniformizedQuadratic_weightedBound
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ upperHalf,
      ‖uniformizedQuadratic R p q z‖ * z.im ^ 2 ≤ M := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.compactSpace
  obtain ⟨K, hK, hcover⟩ := utm_exists_compact_translate hp
  have hc : Continuous (fun τ : ℍ => ‖uniformizedQuadratic R p q τ‖ * τ.im ^ 2) :=
    (WeilPetersson.liftQuadratic_continuous R p hp q).norm.mul
      (UpperHalfPlane.continuous_im.pow 2)
  obtain ⟨M, hM⟩ := (hK.image hc).isBounded.exists_norm_le
  refine ⟨max 0 M, le_max_left _ _, fun z hz => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hcover ⟨z, hz⟩
  have hb : ‖uniformizedQuadratic R p q ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ)‖ *
      (γ • (⟨z, hz⟩ : ℍ) : ℍ).im ^ 2 ≤ M := by
    have hn := hM _ (mem_image_of_mem
      (fun τ : ℍ => ‖uniformizedQuadratic R p q τ‖ * τ.im ^ 2) hγK)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hn)
  have he := utm_x2_norm_mul_im_sq (q : X → ℂ → ℂ) hp hγ hz
  have hm : utm_b_mob γ z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) :=
    utm_b_mob_smul γ hz
  calc
    ‖uniformizedQuadratic R p q z‖ * z.im ^ 2 =
        ‖uniformizedQuadratic R p q (utm_b_mob γ z)‖ * (utm_b_mob γ z).im ^ 2 := he.symm
    _ ≤ M := by
      rw [hm, UpperHalfPlane.coe_im]
      exact hb
    _ ≤ max 0 M := le_max_right _ _

/-- Every actual original-atlas differential lifts to an integrable automorphic
form on every actual fundamental domain, including noncompact domains. -/
theorem uniformizedQuadratic_integrableAutomorphic
    (hΓ : IsFuchsian Γ)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    uniformizedQuadratic R p q ∈ integrableAutomorphicQD Γ F := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.compactSpace
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  let ψ := uniformizedQuadratic R p q
  have hd : DifferentiableOn ℂ ψ upperHalf := utm_liftQD_differentiableOn q.property hp
  refine ⟨hd, ?_, uniformizedQuadratic_automorphic R p hp q⟩
  obtain ⟨K, hK, hcover⟩ := utm_exists_compact_translate hp
  let Kc : Set ℂ := UpperHalfPlane.coe '' K
  have hKc : IsCompact Kc := hK.image UpperHalfPlane.continuous_coe
  have hKH : Kc ⊆ upperHalf := by
    rintro _ ⟨τ, _, rfl⟩
    exact τ.im_pos
  let g : ℂ → ℝ≥0∞ := Kc.indicator (fun z => ENNReal.ofReal ‖ψ z‖)
  have hg : Measurable g := by
    have he : g = Kc.piecewise (fun z => ENNReal.ofReal ‖ψ z‖) 0 := by
      rw [Set.piecewise_eq_indicator]
    rw [he]
    exact (ENNReal.continuous_ofReal.comp_continuousOn
      ((hd.continuousOn.mono hKH).norm)).measurable_piecewise continuousOn_const hKc.measurableSet
  have hfin : ∫⁻ z in upperHalf, g z < ⊤ := by
    have hi : IntegrableOn ψ Kc := (hd.continuousOn.mono hKH).integrableOn_compact hKc
    have hi' : phiArea ψ Kc < ⊤ := by
      simpa only [phiArea, HasFiniteIntegral, ofReal_norm] using hi.2
    calc
      ∫⁻ z in upperHalf, g z ≤ ∫⁻ z, g z := setLIntegral_le_lintegral upperHalf g
      _ = phiArea ψ Kc := lintegral_indicator hKc.measurableSet _
      _ < ⊤ := hi'
  let T : Γ → ℂ → ℝ≥0∞ := fun γ z => g (h36p_m γ.val z) *
    ENNReal.ofReal (‖(γ.val 1 0 : ℂ) * z + γ.val 1 1‖⁻¹ ^ 4)
  have hTm : ∀ γ : Γ, AEMeasurable (T γ) (volume.restrict F) := by
    intro γ
    have hρ : Measurable (fun z : ℂ =>
        ENNReal.ofReal (‖(γ.val 1 0 : ℂ) * z + γ.val 1 1‖⁻¹ ^ 4)) := by fun_prop
    exact ((hg.comp (h36p_m_measurable γ.val)).mul hρ).aemeasurable
  have hbound : phiArea ψ F ≤ ∑' γ : Γ, ∫⁻ z in F, T γ z := by
    rw [← lintegral_tsum hTm]
    refine setLIntegral_mono' hF.2.1 fun z hz => ?_
    obtain ⟨γ, hγ, hγK⟩ := hcover ⟨z, hF.1 hz⟩
    have hmem : h36p_m γ z ∈ Kc :=
      ⟨γ • (⟨z, hF.1 hz⟩ : ℍ), hγK, (h36p_m_coe γ _).symm⟩
    let δ : Γ := ⟨γ, hγ⟩
    have he : ENNReal.ofReal ‖ψ z‖ = T δ z := by
      change ENNReal.ofReal ‖ψ z‖ =
        Kc.indicator (fun w => ENNReal.ofReal ‖ψ w‖) (h36p_m γ z) *
          ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4)
      rw [indicator_of_mem hmem, ← ENNReal.ofReal_mul (norm_nonneg _)]
      congr 1
      have hn := congrArg norm (uniformizedQuadratic_automorphic R p hp q γ hγ z (hF.1 hz))
      change ‖ψ (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4‖ = ‖ψ z‖ at hn
      rw [norm_div, norm_pow] at hn
      simpa only [div_eq_mul_inv, inv_pow] using hn.symm
    exact he.le.trans (ENNReal.le_tsum (f := fun η : Γ => T η z) δ)
  exact lt_of_le_of_lt hbound (by
    change (∑' γ : Γ, ∫⁻ z in F, g (h36p_m γ.val z) *
      ENNReal.ofReal (‖(γ.val 1 0 : ℂ) * z + γ.val 1 1‖⁻¹ ^ 4)) < ⊤
    rw [h36p_unfold hΓ hF hg]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hfin)

private theorem kernel_integrable_of_weightedBound
    {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ upperHalf) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z ∈ upperHalf, ‖ψ z‖ * z.im ^ 2 ≤ M)
    {w : ℂ} (hw : w ∈ upperHalf) :
    IntegrableOn (fun ζ => h36p_c_K ψ ζ w) upperHalf := by
  refine ⟨(h36p_c_K_continuousOn_left hd.continuousOn hw).aestronglyMeasurable
    isOpen_upperHalf.measurableSet, ?_⟩
  unfold HasFiniteIntegral
  have hbound : ∀ᵐ ζ ∂(volume.restrict upperHalf),
      ‖h36p_c_K ψ ζ w‖ₑ ≤ ENNReal.ofReal M *
        ENNReal.ofReal (‖ζ - conj w‖⁻¹ ^ 4) := by
    refine ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet fun ζ hζ => ?_
    rw [← ofReal_norm, h36p_c_K_norm, ← ENNReal.ofReal_mul hM]
    apply ENNReal.ofReal_le_ofReal
    have he : ‖w - conj ζ‖ = ‖ζ - conj w‖ := by
      rw [← Complex.norm_conj (w - conj ζ), map_sub, Complex.conj_conj, norm_sub_rev]
    rw [he]
    exact mul_le_mul_of_nonneg_right (by simpa only [mul_comm] using hb ζ hζ) (by positivity)
  calc
    ∫⁻ ζ in upperHalf, ‖h36p_c_K ψ ζ w‖ₑ ≤
        ∫⁻ ζ in upperHalf, ENNReal.ofReal M * ENNReal.ofReal (‖ζ - conj w‖⁻¹ ^ 4) :=
      lintegral_mono_ae hbound
    _ = ENNReal.ofReal M * (volume (Metric.ball (0 : ℂ) 1) *
        ENNReal.ofReal ((4 * (conj w).im ^ 2)⁻¹)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        h36p_c_kernel_area (h36p_c_conj_mem hw)]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top measure_ball_lt_top ENNReal.ofReal_lt_top)

/-- Reproduction of every original-atlas differential, with actual absolute
convergence and the exact upper-half-plane coefficient `12/π`. -/
theorem uniformizedQuadratic_reproducing
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∀ w ∈ upperHalf,
      IntegrableOn (fun ζ => (ζ.im : ℂ) ^ 2 * uniformizedQuadratic R p q ζ /
        (conj ζ - w) ^ 4) upperHalf ∧
      uniformizedQuadratic R p q w = (12 / Real.pi : ℂ) *
        ∫ ζ in upperHalf, (ζ.im : ℂ) ^ 2 * uniformizedQuadratic R p q ζ /
          (conj ζ - w) ^ 4 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro w hw
  obtain ⟨M, hM, hb⟩ := uniformizedQuadratic_weightedBound R p hp q
  have hd : DifferentiableOn ℂ (uniformizedQuadratic R p q) upperHalf :=
    utm_liftQD_differentiableOn q.property hp
  have hi := kernel_integrable_of_weightedBound hd hM hb hw
  refine ⟨hi, ?_⟩
  change uniformizedQuadratic R p q w = (12 / Real.pi : ℂ) *
    ∫ ζ in upperHalf, h36p_c_K (uniformizedQuadratic R p q) ζ w
  rw [h36p_c_rp_upper hd hw hi]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

private theorem bersKernel_iff_integrableAnnihilator
    (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {κ : ℂ → ℂ} (hm : AEStronglyMeasurable κ (volume.restrict upperHalf))
    {M : ℝ} (hb : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κ z‖ ≤ M)
    (hκΓ : IsGammaCompatible Γ κ) (hκ0 : ∀ z : ℂ, z.im ≤ 0 → κ z = 0) :
    (∀ z ∈ lowerHalf, bersDerivative κ z = 0) ↔
      ∀ φ ∈ integrableAutomorphicQD Γ F, LiZhongQC.beltramiPairing F κ φ = 0 := by
  have hc : (-(6 / Real.pi : ℂ)) ≠ 0 := by simp
  constructor
  · intro hzero φ hφ
    obtain ⟨f, hf, hfA, hθ⟩ := h36p_theta_surj hΓ hF φ hφ
    have hpair := (h36p_poincare hΓ hF hf hfA).2 κ hm ⟨M, hb⟩ hκΓ
    have hz : ∀ z ∈ lowerHalf, ∫ ζ in upperHalf, κ ζ / (ζ - z) ^ 4 = 0 := by
      intro z hz
      have h := hzero z hz
      unfold bersDerivative at h
      exact (mul_eq_zero.1 h).resolve_left hc
    rw [h36p_orth_integrable hm hb hz hf hfA, mul_zero] at hpair
    have he : LiZhongQC.beltramiPairing F κ (h36p_theta Γ f) =
        LiZhongQC.beltramiPairing F κ φ := by
      unfold LiZhongQC.beltramiPairing
      exact setIntegral_congr_fun hF.2.1 fun z hz =>
        congrArg (fun v => κ z * v) (hθ z (hF.1 hz)).symm
    exact he.symm.trans hpair.symm
  · intro horth z hz
    have h := h36p_kernel_cond hΓ hF hm hb hκΓ hκ0 horth z hz z hz
    have he : ∫ ζ in upperHalf, κ ζ / (ζ - z) ^ 4 =
        ∫ ζ, κ ζ / ((ζ - z) ^ 3 * (ζ - z)) := by
      have hpow : (fun ζ => κ ζ / ((ζ - z) ^ 3 * (ζ - z))) =
          fun ζ => κ ζ / (ζ - z) ^ 4 := by funext ζ; ring
      rw [hpow]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => ?_
      rw [hκ0 ζ (not_lt.1 hζ), zero_div]
    unfold bersDerivative
    rw [he, h, mul_zero]

/-- The actual Bers first-variation kernel on the full measurable compatible
Banach space is precisely the annihilator of all original-atlas quadratic
differentials. The pairing is the literal integral over the actual domain `F`. -/
theorem bersKernel_iff_nativeQuadraticAnnihilator
    (hΓ : IsFuchsian Γ)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    (∀ z ∈ lowerHalf,
      bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z = 0) ↔
      ∀ q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
        ∫ z in F, GammaMeasurableBeltrami.planeRepresentative μ.val z *
          uniformizedQuadratic R p q z = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let κ := GammaMeasurableBeltrami.planeRepresentative μ.val
  have hκ := GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val
  have hiff := bersKernel_iff_integrableAnnihilator hΓ hF hκ.1 hκ.2
    (GammaMeasurableBeltrami.planeRepresentative_isGammaCompatible μ)
    (fun z hz => GammaMeasurableBeltrami.planeRepresentative_off μ.val (not_lt.2 hz))
  constructor
  · intro hzero q
    exact (hiff.mp hzero) (uniformizedQuadratic R p q)
      (uniformizedQuadratic_integrableAutomorphic R p hΓ hp hF q)
  · intro hnative
    apply hiff.mpr
    intro φ hφ
    obtain ⟨q, hq, he⟩ := utm_x_descent hp hφ.1 hφ.2.2
    have hn := hnative (⟨q, hq⟩ : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    calc
      LiZhongQC.beltramiPairing F κ φ =
          ∫ z in F, κ z * uniformizedQuadratic R p ⟨q, hq⟩ z := by
        unfold LiZhongQC.beltramiPairing
        exact setIntegral_congr_fun hF.2.1 fun z hz =>
          congrArg (fun v => κ z * v) (he z (hF.1 hz)).symm
      _ = 0 := hn

end LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergman
