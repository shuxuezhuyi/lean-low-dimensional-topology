module

public import LowDimensionalTopology.Geometry.Teichmuller.CoefficientRealMobiusIsometry
public import LowDimensionalTopology.Geometry.Teichmuller.BersRealMobiusIsometry
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationGlobalImage
public import Mathlib.Analysis.Analytic.Linear

/-!
# The literal real Möbius covariance of the full native Bers domains

The source pullback coefficient is compared with the existing native
L-infinity deck pullback in its actual almost-everywhere class. Its raw,
nonsymmetric normalized solution has the same Schwarzian as the original
raw solution precomposed by the real Möbius map. The original Schwarzian
chain rule then gives the literal fourth-power covariance. The entire
compatible coefficient balls, not only a neighborhood of zero, yield
exact equality of the full native Bers images under the weighted isometry.

The raw normalized-solution comparison and Schwarzian chain rule reuse
Wu Xiaobin's Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

/-- The source Möbius coefficient is exactly the actual native weighted a.e. class. -/
theorem sourceAmbient_realMobiusPullback (μ : LiZhongQC.BeltramiH) (M : Deck) :
    sourceAmbient (LiZhongQC.b33_e_pb μ M) = pullback M (sourceAmbient μ) := by
  have hdetR : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe M
    rwa [Matrix.det_fin_two] at h
  have hdet : (M 0 0 : ℂ) * M 1 1 - M 0 1 * M 1 0 = 1 := by
    exact_mod_cast hdetR
  have hne : (M 0 0 : ℂ) * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
    rw [hdet]
    exact one_ne_zero
  have hd := LiZhongQC.bg2_d_pullback μ hne LiZhongQC.isOpen_upperHalf
    (fun z hz => LiZhongQC.bg2_d_den_ne_zero hdetR (show 0 < z.im from hz).ne')
  apply Lp.ext
  filter_upwards [sourceAmbient_coe_ae (LiZhongQC.b33_e_pb μ M),
    ae_plane_iff.mp (ae_restrict_of_ae (LiZhongQC.b33_e_pb_L_dil μ M)),
    ae_plane_iff.mp hd, pullback_coe_ae M (sourceAmbient μ),
    (measurePreserving_deck M).quasiMeasurePreserving.ae (sourceAmbient_coe_ae μ)]
    with z hsource hpb hdil hpull hμ
  have hformula :
      LiZhongQC.complexDilatation (LiZhongQC.normalizedSolution μ.val ∘
        LiZhongQC.mobiusFn (M 0 0) (M 0 1) (M 1 0) (M 1 1)) z =
      LiZhongQC.complexDilatation (LiZhongQC.normalizedSolution μ.val) (M • z : ℍ) *
        phase M z := by
    simpa only [LiZhongQC.h23l_b_coe_smul, LiZhongQC.mobiusFn, phase, denominator] using
      LiZhongQC.bg2_d_dil_mobius (LiZhongQC.normalizedSolution μ.val)
        hdet (denominator_ne_zero M z)
  have hdil' : LiZhongQC.complexDilatation (LiZhongQC.normalizedSolution μ.val)
      (M • z : ℍ) = μ.val (M • z : ℍ) := by
    simpa only [LiZhongQC.h23l_b_coe_smul, LiZhongQC.mobiusFn] using hdil
  calc
    sourceAmbient (LiZhongQC.b33_e_pb μ M) z = (LiZhongQC.b33_e_pb μ M).val z := hsource
    _ = LiZhongQC.complexDilatation (LiZhongQC.normalizedSolution μ.val ∘
        LiZhongQC.mobiusFn (M 0 0) (M 0 1) (M 1 0) (M 1 1)) z := hpb.symm
    _ = LiZhongQC.complexDilatation (LiZhongQC.normalizedSolution μ.val) (M • z : ℍ) *
        phase M z := hformula
    _ = phase M z * sourceAmbient μ (M • z) := by rw [hdil', hμ]; exact mul_comm _ _
    _ = pullback M (sourceAmbient μ) z := hpull.symm

private theorem sourceAmbient_toSourceBall {Γ : Subgroup Deck} (μ : Ball Γ) :
    sourceAmbient (toSourceGamma μ).val = μ.val.val :=
  congrArg (fun η : Ball Γ => η.val.val) (fromSourceGamma_toSourceGamma μ)

/-- The original source coefficient and the native transported coefficient
have precisely the same upper-plane a.e. representative. -/
theorem coefficientRealMobiusBall_source_ae (Γ : Subgroup Deck) (M : Deck)
    (μ : Ball (LiZhongQC.conjGroup Γ M)) :
    (toSourceGamma (coefficientRealMobiusBallEquiv Γ M μ)).val.val
      =ᵐ[volume.restrict LiZhongQC.upperHalf] (LiZhongQC.b33_e_pb (toSourceGamma μ).val M).val := by
  let μM := coefficientRealMobiusBallEquiv Γ M μ
  have hclass : sourceAmbient (toSourceGamma μM).val =
      sourceAmbient (LiZhongQC.b33_e_pb (toSourceGamma μ).val M) := by
    rw [sourceAmbient_toSourceBall, sourceAmbient_realMobiusPullback, sourceAmbient_toSourceBall]
    change (coefficientRealMobiusIsometry Γ M μ.val).val = pullback M μ.val.val
    exact coefficientRealMobiusIsometry_val Γ M μ.val
  apply ae_plane_iff.mpr
  filter_upwards [sourceAmbient_coe_ae (toSourceGamma μM).val,
    sourceAmbient_coe_ae (LiZhongQC.b33_e_pb (toSourceGamma μ).val M)] with z hleft hright
  rw [hclass] at hleft
  exact hleft.symm.trans hright

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open GammaMeasurableBeltrami

/-- The a.e. comparison is on raw coefficients; its proof uses symmetric
uniqueness only to compare their real boundary values, then the actual welding theorem. -/
private theorem rawBers_eq_of_upperAE (μ η : LiZhongQC.BeltramiH)
    (h : μ.val =ᵐ[volume.restrict LiZhongQC.upperHalf] η.val) :
    LiZhongQC.bersFunction μ.val = LiZhongQC.bersFunction η.val := by
  obtain ⟨k, hk0, hk1, hμ⟩ := LiZhongQC.bg_beltramiH_upper μ
  obtain ⟨l, hl0, hl1, hη⟩ := LiZhongQC.bg_beltramiH_upper η
  have he := LiZhongQC.s27u_fSym_congr_ae hk0 hk1 hμ hl0 hl1 hη h
  apply LiZhongQC.bersFunction_eq_of_equiv
  apply LiZhongQC.bg_l_forward
  intro x
  simpa only [LiZhongQC.s33v_fSym_eq] using congrFun he (x : ℂ)

/-- The actual nonsymmetric raw solution obeys the literal quadratic
Möbius covariance; no symmetric native solution is substituted for it. -/
theorem rawBers_realMobiusPullback (μ : LiZhongQC.BeltramiH) (M : Deck) :
    realMobiusPullback M (LiZhongQC.bersFunction μ.val) =
      LiZhongQC.bersFunction (LiZhongQC.b33_e_pb μ M).val := by
  funext z
  by_cases hz : z ∈ LiZhongQC.lowerHalf
  · have hMz : LiZhongQC.utm_b_mob M z ∈ LiZhongQC.lowerHalf :=
      LiZhongQC.bg2_a_mem M hz
    rw [realMobiusPullback_apply M _ hz]
    rw [LiZhongQC.bersFunction, indicator_of_mem hMz,
      LiZhongQC.bersFunction, indicator_of_mem hz]
    exact (LiZhongQC.bg2_a_chain μ M hz).symm.trans
      (LiZhongQC.b33_e_pb_schwarzian μ M hz)
  · rw [realMobiusPullback_off _ _ hz, LiZhongQC.bersFunction,
      indicator_of_notMem hz]

/-- The exact matrix conjugate of an actual Fuchsian group remains Fuchsian. -/
theorem isFuchsian_realConjugate {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (M : Deck) :
    LiZhongQC.IsFuchsian (LiZhongQC.conjGroup Γ M) := by
  have hfull := LiZhongQC.b33_d_conjGroup_isFuchsian hΓ (Homeomorph.smul M)
  intro C hC
  apply (hfull C hC).subset
  rintro γ ⟨hγ, hmeet⟩
  refine ⟨?_, hmeet⟩
  obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hγ
  refine ⟨δ, hδ, fun τ => ?_⟩
  change M • (δ • τ) = (M * δ * M⁻¹) • (M • τ)
  rw [mul_smul, mul_smul, inv_smul_smul]

/-- The actual whole coefficient projection commutes with the two genuine
native Möbius isometries, on every compatible subunit coefficient. -/
theorem automorphicRealMobiusIsometry_projection {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (M : Deck)
    (μ : Ball (LiZhongQC.conjGroup Γ M)) :
    automorphicRealMobiusIsometry Γ M
        (automorphicProjection (isFuchsian_realConjugate hΓ M) μ.val) =
      automorphicProjection hΓ (coefficientRealMobiusBallEquiv Γ M μ).val := by
  apply Automorphic.toSource_injective
  apply Subtype.ext
  rw [automorphicRealMobiusIsometry_toSource,
    automorphicProjection_toSource_eq _ _ (Ball.norm_lt_one μ),
    automorphicProjection_toSource_eq _ _ (Ball.norm_lt_one _)]
  exact (rawBers_realMobiusPullback (toSourceGamma μ).val M).trans
    (rawBers_eq_of_upperAE (toSourceGamma (coefficientRealMobiusBallEquiv Γ M μ)).val
      (LiZhongQC.b33_e_pb (toSourceGamma μ).val M)
      (coefficientRealMobiusBall_source_ae Γ M μ)).symm

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami BersWeighted

/-- The real Möbius isometry identifies the ENTIRE compatible Bers images. -/
theorem automorphicRealMobiusIsometry_image {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (M : Deck) :
    automorphicRealMobiusIsometry Γ M ''
      coefficientBersImage (isFuchsian_realConjugate hΓ M) = coefficientBersImage hΓ := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨μ, rfl⟩ := (mem_coefficientBersImage_iff_coefficient _ ψ).mp hψ
    apply (mem_coefficientBersImage_iff_coefficient hΓ _).mpr
    exact ⟨coefficientRealMobiusBallEquiv Γ M μ,
      (automorphicRealMobiusIsometry_projection hΓ M μ).symm⟩
  · intro hφ
    obtain ⟨η, rfl⟩ := (mem_coefficientBersImage_iff_coefficient hΓ φ).mp hφ
    let μ := (coefficientRealMobiusBallEquiv Γ M).symm η
    refine ⟨automorphicProjection (isFuchsian_realConjugate hΓ M) μ.val, ?_, ?_⟩
    · exact (mem_coefficientBersImage_iff_coefficient _ _).mpr ⟨μ, rfl⟩
    · rw [automorphicRealMobiusIsometry_projection]
      change automorphicProjection hΓ
        ((coefficientRealMobiusBallEquiv Γ M) ((coefficientRealMobiusBallEquiv Γ M).symm η)).val = _
      rw [Equiv.apply_symm_apply]

/-- Both actual full-domain coordinate changes are analytic for the unchanged
weighted Banach norms. This follows from the proved complex linear isometry. -/
theorem automorphicRealMobiusIsometry_analytic_bothDirections {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (M : Deck) :
    AnalyticOnNhd ℂ (automorphicRealMobiusIsometry Γ M)
      (coefficientBersImage (isFuchsian_realConjugate hΓ M)) ∧
    AnalyticOnNhd ℂ (automorphicRealMobiusIsometry Γ M).symm
      (coefficientBersImage hΓ) := by
  exact ⟨(automorphicRealMobiusIsometry Γ M).toContinuousLinearEquiv.toContinuousLinearMap.analyticOnNhd _,
    (automorphicRealMobiusIsometry Γ M).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticOnNhd _⟩

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
