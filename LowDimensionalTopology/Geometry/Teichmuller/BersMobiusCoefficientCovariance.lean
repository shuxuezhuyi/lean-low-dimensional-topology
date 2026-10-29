module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersRealMobiusCovariance
public import LowDimensionalTopology.Geometry.Teichmuller.NativeAhlforsWeillSection

/-! Literal real Möbius covariance of the source Bers and Ahlfors–Weill maps. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
open GammaMeasurableBeltrami

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

private theorem positive_det (M : Deck) : 0 < M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
  have h := Matrix.SpecialLinearGroup.det_coe M
  rw [Matrix.det_fin_two] at h
  rw [h]
  exact zero_lt_one

/-- A genuine upper-plane postnormalization gives covariance of the raw Bers
map via its coefficient class; no Schwarzian of the symmetric QC map is used. -/
theorem rawBers_realMobiusPullback_of_symmetricPostcomp
    (μ η : LiZhongQC.BeltramiH) (A M : Deck)
    (hrel : ∀ z ∈ LiZhongQC.upperHalf,
      LiZhongQC.fMuSym η.val z =
        LiZhongQC.mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1)
          (LiZhongQC.fMuSym μ.val
            (LiZhongQC.mobiusFn (M 0 0) (M 0 1) (M 1 0) (M 1 1) z))) :
    LiZhongQC.bersFunction η.val = realMobiusPullback M (LiZhongQC.bersFunction μ.val) := by
  let G := LiZhongQC.fMuSym μ.val ∘
    LiZhongQC.mobiusFn (M 0 0) (M 0 1) (M 1 0) (M 1 1)
  obtain ⟨K, hK, _, _, _, _, hU, _⟩ := LiZhongQC.b33_t_fs_spec μ
  obtain ⟨_, _, _, _, _, _, _, hdη⟩ := LiZhongQC.b33_t_fs_spec η
  have hM := LiZhongQC.isConformalOnto_mobius_upperHalf (positive_det M)
  have hG := LiZhongQC.thm7_1_comp
    (LiZhongQC.isKQC_one_of_conformal LiZhongQC.isOpen_upperHalf hM) hK (subset_univ _)
  have hGU : G '' LiZhongQC.upperHalf ⊆ LiZhongQC.upperHalf := by
    simpa only [G, image_comp, hM.2.2, hU] using
      (show LiZhongQC.upperHalf ⊆ LiZhongQC.upperHalf from fun _ hz => hz)
  have hpost := (LiZhongQC.bg_comp_conformal hG LiZhongQC.isOpen_upperHalf
    (LiZhongQC.isConformalOnto_mobius_upperHalf (positive_det A)) hGU).2
  have hae : η.val =ᵐ[volume.restrict LiZhongQC.upperHalf]
      (LiZhongQC.b33_e_pb μ M).val := by
    filter_upwards [hdη, hpost,
      ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with z hη hp hz
    have he := LiZhongQC.abR_t_complexDilatation_congr LiZhongQC.isOpen_upperHalf hrel hz
    change LiZhongQC.complexDilatation (LiZhongQC.fMuSym η.val) z =
      LiZhongQC.complexDilatation
        (LiZhongQC.mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) ∘ G) z at he
    change η.val z = LiZhongQC.upperHalf.indicator (LiZhongQC.complexDilatation G) z
    rw [indicator_of_mem hz]
    exact hη.symm.trans (he.trans hp)
  exact (rawBers_eq_of_upperAE η (LiZhongQC.b33_e_pb μ M) hae).trans
    (rawBers_realMobiusPullback μ M).symm

/-- The exact quadratic pullback induces the actual Beltrami tensor law on
the literal coefficient of the complex-linear Ahlfors–Weill section. -/
theorem ahlforsWeillCoefficient_realMobiusPullback
    {G H : Subgroup Deck} (M : Deck) (φ : Automorphic G) (ψ : Automorphic H)
    (hψ : (ψ.toSource : ℂ → ℂ) = realMobiusPullback M (φ.toSource : ℂ → ℂ)) (z : ℍ) :
    ahlforsWeillCoefficient ψ z = phase M z * ahlforsWeillCoefficient φ (M • z) := by
  have hz : conj (z : ℂ) ∈ LiZhongQC.lowerHalf := by
    change (conj (z : ℂ)).im < 0
    rw [Complex.conj_im]
    exact neg_lt_zero.mpr z.im_pos
  have hd := denominator_ne_zero M z
  have hcd : conj (denominator M z) ≠ 0 := by
    intro h
    apply hd
    simpa only [Complex.conj_conj, map_zero] using congrArg conj h
  have hden : realMobiusDenom M (conj (z : ℂ)) = conj (denominator M z) := by
    simp only [realMobiusDenom, denominator, map_add, map_mul, Complex.conj_ofReal]
  have hmob : LiZhongQC.utm_b_mob M (conj (z : ℂ)) = conj ((M • z : ℍ) : ℂ) :=
    (LiZhongQC.s33dim_conj_mob M z).symm.trans
      (congrArg conj (LiZhongQC.utm_b_mob_coe M z))
  have him : (M • z : ℍ).im = z.im / Complex.normSq (denominator M z) := by
    simp [MulAction.compHom_smul_def, UpperHalfPlane.im_smul_eq_div_normSq,
      Matrix.SpecialLinearGroup.det_mapGL, UpperHalfPlane.denom, denominator]
  have himc : ((M • z : ℍ).im : ℂ) =
      (z.im : ℂ) / (denominator M z * conj (denominator M z)) := by
    rw [Complex.mul_conj]
    exact_mod_cast him
  rw [ahlforsWeillCoefficient, ahlforsWeillCoefficient, hψ,
    realMobiusPullback_apply M _ hz, hden, hmob, phase, himc]
  simp only [map_pow]
  field_simp [hd, hcd]

/-- Covariance holds in the original ambient L-infinity space, not only for
chosen pointwise representatives. -/
theorem ahlforsWeill_realMobiusPullback
    {G H : Subgroup Deck} (M : Deck) (φ : Automorphic G) (ψ : Automorphic H)
    (hψ : (ψ.toSource : ℂ → ℂ) = realMobiusPullback M (φ.toSource : ℂ → ℂ)) :
    (ahlforsWeill ψ).val = pullback M (ahlforsWeill φ).val := by
  apply Lp.ext
  filter_upwards [ahlforsWeill_coe_ae ψ,
    pullback_coe_ae M (ahlforsWeill φ).val,
    (measurePreserving_deck M).quasiMeasurePreserving.ae (ahlforsWeill_coe_ae φ)]
      with z hψz hp hφz
  rw [hψz, hp, hφz]
  exact ahlforsWeillCoefficient_realMobiusPullback M φ ψ hψ z

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
