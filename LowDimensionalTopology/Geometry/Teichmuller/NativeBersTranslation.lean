module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeInverseBersGermContinuity
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationLocalBound

/-!
# The actual Bers-coordinate translation in its faithful native codomain

The genuine source translation has automorphic image by the actual normalized
conjugacy laws, and its source values have the universal Bers bound. These
proved facts place that literal map in the unchanged weighted normed space.
The actual normalized pullback of the Ahlfors-Weill section is its right
inverse on the original weighted half-unit ball. The quantitative source
estimate gives the corresponding actual native fixed-base norm estimate.
Neither differentiability nor invertibility of its derivative is assumed.

The source normalized translation uses Wu Xiaobin's LiZhongQC development,
Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The actual source translation is automorphic for the actual normalized deformed group. -/
theorem sourceBersTranslation_mem (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic Γ) :
    LiZhongQC.b33_t_chi (toSourceGamma ν).val (φ.toSource : ℂ → ℂ) ∈
      LiZhongQC.automorphicQD (deformedGroup hΓ ν) := by
  classical
  by_cases hφ : ∃ μ : LiZhongQC.BeltramiH,
      LiZhongQC.bersFunction μ.val = (φ.toSource : ℂ → ℂ)
  · obtain ⟨μ, hμ⟩ := hφ
    rw [← hμ, LiZhongQC.b33_t_chi_spec]
    apply (LiZhongQC.b33_t_tb_auto_iff (toSourceGamma ν).val
      (deformedGroup_spec hΓ ν).2 μ).mp
    rw [hμ]
    exact φ.toSource.property
  · rw [LiZhongQC.b33_t_chi, dite_eq_right hφ]
    exact (LiZhongQC.automorphicQD _).zero_mem

/-- Every actual source translation value has the universal sharp Bers bound. -/
theorem sourceBersTranslation_bersBound (ν : Ball Γ)
    (φ : BersWeighted.Automorphic Γ) :
    LiZhongQC.bersNormL
      (LiZhongQC.b33_t_chi (toSourceGamma ν).val (φ.toSource : ℂ → ℂ)) ≤
        ENNReal.ofReal (3 / 2 : ℝ) := by
  classical
  by_cases hφ : ∃ μ : LiZhongQC.BeltramiH,
      LiZhongQC.bersFunction μ.val = (φ.toSource : ℂ → ℂ)
  · obtain ⟨μ, hμ⟩ := hφ
    rw [← hμ, LiZhongQC.b33_t_chi_spec]
    exact (LiZhongQC.bg2_bers_mem (LiZhongQC.b33_t_tb (toSourceGamma ν).val μ)).2.le
  · rw [LiZhongQC.b33_t_chi, dite_eq_right hφ]
    apply iSup₂_le
    intro z hz
    simp only [Pi.zero_apply, norm_zero, zero_mul, ENNReal.ofReal_zero]
    exact bot_le

/-- The literal weighted pointwise bound, used for the faithful native realization. -/
theorem sourceBersTranslation_weightedBound (ν : Ball Γ)
    (φ : BersWeighted.Automorphic Γ) :
    ∀ z ∈ LiZhongQC.lowerHalf,
      ‖LiZhongQC.b33_t_chi (toSourceGamma ν).val (φ.toSource : ℂ → ℂ) z‖ * z.im ^ 2 ≤
        (3 / 2 : ℝ) := by
  intro z hz
  apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : 0 ≤ (3 / 2 : ℝ))).mp
  exact (le_iSup₂_of_le z hz le_rfl).trans (sourceBersTranslation_bersBound ν φ)

/-- The actual source-coordinate translation in the unchanged native weighted codomain. -/
def bersTranslation (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic Γ) : BersWeighted.Automorphic (deformedGroup hΓ ν) :=
  BersWeighted.Automorphic.ofSource
    ⟨LiZhongQC.b33_t_chi (toSourceGamma ν).val (φ.toSource : ℂ → ℂ),
      sourceBersTranslation_mem hΓ ν φ⟩
    ⟨3 / 2, sourceBersTranslation_weightedBound ν φ⟩

/-- The realization retains the entire genuine source translation function. -/
theorem bersTranslation_toSource (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic Γ) :
    ((bersTranslation hΓ ν φ).toSource : ℂ → ℂ) =
      LiZhongQC.b33_t_chi (toSourceGamma ν).val (φ.toSource : ℂ → ℂ) := by
  exact congrArg (fun q : LiZhongQC.automorphicQD (deformedGroup hΓ ν) => (q : ℂ → ℂ))
    (BersWeighted.Automorphic.toSource_ofSource _ _)

/-- The actual native translation sends the original nonzero Bers point to zero. -/
theorem bersTranslation_base (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    bersTranslation hΓ ν (baseBersValue hΓ ν) = 0 := by
  apply BersWeighted.Automorphic.toSource_injective
  apply Subtype.ext
  rw [bersTranslation_toSource, baseBersValue_toSource, LiZhongQC.b33_t_chi_spec,
    LiZhongQC.b33_t_tb_self, LiZhongQC.b33_t_bf_zero]
  exact (map_zero BersWeighted.decodeLinearMap).symm

/-- The actual coordinate translation recovers every vector in the weighted half-unit section ball. -/
theorem bersTranslation_inverseBersGerm (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) (hφ : ‖φ‖ < 1 / 2) :
    bersTranslation hΓ ν (inverseBersGerm hΓ ν φ) = φ := by
  apply BersWeighted.Automorphic.toSource_injective
  apply Subtype.ext
  rw [bersTranslation_toSource, inverseBersGerm_source_pullback hΓ ν φ hφ,
    LiZhongQC.b33_t_chi_spec]
  have he := (LiZhongQC.b33_t_bf_eq_iff
    (LiZhongQC.b33_t_tb (toSourceGamma ν).val
      (LiZhongQC.b33_t_pb (toSourceGamma ν).val
        (toSourceGamma (ahlforsWeillBall φ hφ)).val))
    (toSourceGamma (ahlforsWeillBall φ hφ)).val).2
      (LiZhongQC.b33_t_tb_pb_equiv (toSourceGamma ν).val
        (toSourceGamma (ahlforsWeillBall φ hφ)).val)
  exact he.trans (ahlforsWeillBall_source (deformedGroup_spec hΓ ν).1 φ hφ)

/-- The actual inverse germ at zero is the original nonzero Bers point. -/
theorem inverseBersGerm_zero (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    inverseBersGerm hΓ ν 0 = baseBersValue hΓ ν := by
  have he : gammaPullback hΓ ν (0 : Space (deformedGroup hΓ ν)) = ν.val := by
    apply Subtype.ext
    exact pullback_base ν
  change BersWeighted.automorphicProjection hΓ
    (gammaPullback hΓ ν (BersWeighted.ahlforsWeill 0)) = _
  rw [map_zero, he]
  rfl

/-- The genuine source quantitative estimate is a norm estimate in the actual native codomain. -/
theorem bersTranslation_local_norm_bound (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ : BersWeighted.Automorphic Γ,
      c * ‖φ - baseBersValue hΓ ν‖ < 1 / 2 →
      ‖bersTranslation hΓ ν φ‖ ≤ 12 * c * ‖φ - baseBersValue hΓ ν‖ := by
  obtain ⟨c, hc, hb⟩ := sourceBersTranslation_local_bound hΓ ν
  refine ⟨c, hc, fun φ hφ => ?_⟩
  apply BersWeighted.Automorphic.norm_le_of_bersNormL_le _
    (mul_nonneg (mul_nonneg (by norm_num) hc.le) (norm_nonneg _))
  rw [bersTranslation_toSource]
  exact hb φ hφ

/-- On actual original coefficients, the native coordinate map is the actual translated composite. -/
theorem bersTranslation_automorphicProjection (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    bersTranslation hΓ ν (BersWeighted.automorphicProjection hΓ μ.val) =
      translatedBersProjection hΓ ν μ.val := by
  apply BersWeighted.Automorphic.toSource_injective
  apply Subtype.ext
  rw [bersTranslation_toSource, translatedBersProjection_source,
    BersWeighted.automorphicProjection_toSource_eq hΓ μ.val (Ball.norm_lt_one μ),
    bersProjection_eq]

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
