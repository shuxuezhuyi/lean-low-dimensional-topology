module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslation
public import Mathlib.Topology.Continuous

/-!
# The actual Bers translation has a genuine local inverse at the original point

The actual Ahlfors-Weill epsilon theorem puts a weighted neighborhood of the
original Bers point inside the genuine universal Bers image. The actual
normalized coefficient translation is injective on that image. Consequently
the independently defined normalized pullback section is a left inverse there.

The proved fixed-base norm estimate gives continuity of the actual native
coordinate translation at the original point. Its values eventually enter
the genuine half-unit section ball, so the left-inverse equality holds on an
actual full neighborhood. No derivative, inverse, or continuity premise is
introduced.

The source image and normalized translation arguments use Wu Xiaobin's
LiZhongQC development, Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The actual universal Bers-function image inside the faithful native automorphic space. -/
def nativeUniversalBersImage (Γ : Subgroup Deck) : Set (BersWeighted.Automorphic Γ) :=
  {φ | ∃ μ : LiZhongQC.BeltramiH, LiZhongQC.bersFunction μ.val = (φ.toSource : ℂ → ℂ)}

/-- The actual epsilon theorem puts a full original weighted ball in the genuine Bers image. -/
theorem exists_nativeUniversalBersImage_ball (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : BersWeighted.Automorphic Γ,
      ‖φ - baseBersValue hΓ ν‖ < r → φ ∈ nativeUniversalBersImage Γ := by
  let νH := (toSourceGamma ν).val
  let p : LiZhongQC.UniversalTeichmuller := Quotient.mk LiZhongQC.teichSetoid νH
  obtain ⟨c, hc, hcore⟩ := LiZhongQC.aw_core p
  refine ⟨1 / c, one_div_pos.mpr hc, ?_⟩
  intro φ hφ
  let n := ‖φ - baseBersValue hΓ ν‖
  have hn : 0 ≤ n := norm_nonneg _
  have hφL : (φ.toSource : ℂ → ℂ) ∈ LiZhongQC.bersSpaceL :=
    ⟨φ.toSource.property.1,
      (BersWeighted.Automorphic.bersNormL_toSource_le φ).trans_lt ENNReal.ofReal_lt_top⟩
  have hN := BersWeighted.Automorphic.bersNormL_toSource_le (φ - baseBersValue hΓ ν)
  have hsub : ((φ - baseBersValue hΓ ν).toSource : ℂ → ℂ) =
      (φ.toSource : ℂ → ℂ) - ((baseBersValue hΓ ν).toSource : ℂ → ℂ) := by
    change BersWeighted.decode (φ.val - (baseBersValue hΓ ν).val) =
      BersWeighted.decode φ.val - BersWeighted.decode (baseBersValue hΓ ν).val
    exact map_sub BersWeighted.decodeLinearMap _ _
  rw [hsub, baseBersValue_toSource] at hN
  have hN' : LiZhongQC.bersNormL ((φ.toSource : ℂ → ℂ) - LiZhongQC.bersMapU p) ≤
      ENNReal.ofReal n := by
    change LiZhongQC.bersNormL ((φ.toSource : ℂ → ℂ) -
      LiZhongQC.bersMapU (Quotient.mk LiZhongQC.teichSetoid νH)) ≤ ENNReal.ofReal n
    rw [LiZhongQC.aw_t_bersMapU_mk]
    exact hN
  obtain ⟨μ, hS, _⟩ := hcore (φ.toSource : ℂ → ℂ) hφL n hn hN' hφ
  refine ⟨μ, ?_⟩
  funext z
  by_cases hz : z ∈ LiZhongQC.lowerHalf
  · rw [LiZhongQC.bersFunction, indicator_of_mem hz]
    exact hS z hz
  · rw [LiZhongQC.bersFunction, indicator_of_notMem hz]
    exact (φ.toSource.property.2.1 z hz).symm

/-- The actual normalized coordinate map is injective on its genuine source Bers image. -/
theorem bersTranslation_injOn_nativeUniversalBersImage
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    InjOn (bersTranslation hΓ ν) (nativeUniversalBersImage Γ) := by
  rintro φ ⟨μ, hμ⟩ ψ ⟨κ, hκ⟩ heq
  apply BersWeighted.Automorphic.toSource_injective
  apply Subtype.ext
  have he := congrArg
    (fun q : BersWeighted.Automorphic (deformedGroup hΓ ν) => (q.toSource : ℂ → ℂ)) heq
  rw [bersTranslation_toSource, bersTranslation_toSource, ← hμ, ← hκ,
    LiZhongQC.b33_t_chi_spec, LiZhongQC.b33_t_chi_spec] at he
  have hpoint : LiZhongQC.teichSetoid μ κ :=
    (LiZhongQC.b33_t_tb_equiv (toSourceGamma ν).val μ κ).2
      ((LiZhongQC.b33_t_bf_eq_iff
        (LiZhongQC.b33_t_tb (toSourceGamma ν).val μ)
        (LiZhongQC.b33_t_tb (toSourceGamma ν).val κ)).1 he)
  exact (hμ.symm.trans ((LiZhongQC.b33_t_bf_eq_iff μ κ).2 hpoint)).trans hκ

/-- Every actual section value in its half-unit domain is a genuine source Bers value. -/
theorem inverseBersGerm_mem_nativeUniversalBersImage
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) (hφ : ‖φ‖ < 1 / 2) :
    inverseBersGerm hΓ ν φ ∈ nativeUniversalBersImage Γ := by
  refine ⟨LiZhongQC.b33_t_pb (toSourceGamma ν).val
    (toSourceGamma (ahlforsWeillBall φ hφ)).val, ?_⟩
  exact (inverseBersGerm_source_pullback hΓ ν φ hφ).symm

/-- The independently defined normalized pullback is the actual left inverse on the image. -/
theorem inverseBersGerm_bersTranslation_of_image
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) (φ : BersWeighted.Automorphic Γ)
    (hφ : φ ∈ nativeUniversalBersImage Γ)
    (hsmall : ‖bersTranslation hΓ ν φ‖ < 1 / 2) :
    inverseBersGerm hΓ ν (bersTranslation hΓ ν φ) = φ := by
  exact (bersTranslation_injOn_nativeUniversalBersImage hΓ ν)
    (inverseBersGerm_mem_nativeUniversalBersImage hΓ ν _ hsmall) hφ
    (bersTranslation_inverseBersGerm hΓ ν _ hsmall)

/-- The actual fixed-base quantitative norm bound proves actual continuity at the original point. -/
theorem continuousAt_bersTranslation_base (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    ContinuousAt (bersTranslation hΓ ν) (baseBersValue hΓ ν) := by
  obtain ⟨c, hc, hb⟩ := bersTranslation_local_norm_bound hΓ ν
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hC : 0 < 12 * c := mul_pos (by norm_num) hc
  refine ⟨min ((1 / 2) / c) (ε / (12 * c)),
    lt_min (div_pos (by norm_num) hc) (div_pos hε hC), ?_⟩
  intro φ hdist
  have hn : ‖φ - baseBersValue hΓ ν‖ < min ((1 / 2) / c) (ε / (12 * c)) := by
    simpa only [dist_eq_norm] using hdist
  have hsmall : c * ‖φ - baseBersValue hΓ ν‖ < 1 / 2 := by
    have ht := (lt_div_iff₀ hc).mp (hn.trans_le (min_le_left _ _))
    nlinarith
  have hεn : 12 * c * ‖φ - baseBersValue hΓ ν‖ < ε := by
    have ht := (lt_div_iff₀ hC).mp (hn.trans_le (min_le_right _ _))
    nlinarith
  rw [bersTranslation_base, dist_zero_right]
  exact (hb φ hsmall).trans_lt hεn

/-- Continuity places actual translated values in every prescribed positive weighted ball. -/
theorem eventually_bersTranslation_norm_lt (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ φ in 𝓝 (baseBersValue hΓ ν), ‖bersTranslation hΓ ν φ‖ < ε := by
  have hball : Metric.ball (0 : BersWeighted.Automorphic (deformedGroup hΓ ν)) ε ∈
      𝓝 (bersTranslation hΓ ν (baseBersValue hΓ ν)) := by
    rw [bersTranslation_base]
    exact Metric.ball_mem_nhds _ hε
  have he := (continuousAt_bersTranslation_base hΓ ν).preimage_mem_nhds hball
  filter_upwards [he] with φ hφ
  exact mem_ball_zero_iff.mp hφ

/-- The actual left-inverse equation holds on a full neighborhood of the original Bers point. -/
theorem inverseBersGerm_bersTranslation_eventually
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    ∀ᶠ φ in 𝓝 (baseBersValue hΓ ν), inverseBersGerm hΓ ν (bersTranslation hΓ ν φ) = φ := by
  obtain ⟨r, hr, himage⟩ := exists_nativeUniversalBersImage_ball hΓ ν
  filter_upwards [Metric.ball_mem_nhds (baseBersValue hΓ ν) hr,
    eventually_bersTranslation_norm_lt hΓ ν (show 0 < (1 / 2 : ℝ) by norm_num)] with φ hφ hsmall
  apply inverseBersGerm_bersTranslation_of_image hΓ ν φ _ hsmall
  exact himage φ (by simpa only [Metric.mem_ball, dist_eq_norm] using hφ)

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
