module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceChangeProjection

/-!
# The same original marked point under a prescribed real Mobius change

The actual coefficient isometry and the conjugated covering projection give
the same native marked point on the entire coefficient ball. Real scalar
coefficient curves therefore have the same original marked-quotient germ.
The normalization uses the actual zero coefficient and the prescribed matrix.

The normalized-solution and reference-change APIs reuse Wu Xiaobin's
Li-Zhong-QC-formalization, Apache-2.0, pinned commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane ENNReal Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

/-- The original zero compatible coefficient in its actual open unit ball. -/
def zeroCoefficient (Γ : Subgroup Deck) : Ball Γ :=
  ⟨0, by simpa only [Metric.mem_ball, dist_self] using (zero_lt_one : (0 : ℝ) < 1)⟩

/-- The actual normalized symmetric solution of the zero coefficient is the identity. -/
theorem normalizedMap_zeroCoefficient (Γ : Subgroup Deck) :
    normalizedMap (zeroCoefficient Γ) = id := by
  have hplane : planeRepresentative (0 : Ambient)
      =ᵐ[volume.restrict LiZhongQC.upperHalf] (0 : ℂ → ℂ) := by
    apply ae_plane_iff.mpr
    filter_upwards [Lp.coeFn_zero ℂ (⊤ : ℝ≥0∞) (volume : Measure ℍ)] with z hz
    simpa only [planeRepresentative_coe, Pi.zero_apply] using hz
  have hzero : LiZhongQC.IsBeltramiCoeff (0 : ℂ → ℂ) LiZhongQC.upperHalf 0 :=
    ⟨aestronglyMeasurable_const, Eventually.of_forall fun _ => by simp⟩
  have hcoeff : LiZhongQC.IsBeltramiCoeff (planeRepresentative (0 : Ambient))
      LiZhongQC.upperHalf 0 := by
    simpa only [norm_zero] using planeRepresentative_isBeltramiCoeff (0 : Ambient)
  have hmirror : LiZhongQC.s27u_symExt (0 : ℂ → ℂ) = 0 := by
    funext z
    simp only [LiZhongQC.s27u_symExt, Pi.zero_apply, map_zero, ite_self]
  have hraw : LiZhongQC.s27u_fSym (0 : ℂ → ℂ) = id := by
    rw [LiZhongQC.s27u_fSym, hmirror, LiZhongQC.bB_l_normalizedSolution_zero]
  have h := LiZhongQC.s27u_fSym_congr_ae (le_refl (0 : ℝ)) zero_lt_one hcoeff
    (le_refl (0 : ℝ)) zero_lt_one hzero hplane
  change LiZhongQC.fMuSym (planeRepresentative (0 : Ambient)) = id
  rw [← LiZhongQC.s33v_fSym_eq]
  exact h.trans hraw

private theorem translation_zeroCoefficient (Γ : Subgroup Deck) (μ : Ball Γ) :
    translation (zeroCoefficient Γ) μ.val.val = μ.val.val := by
  have hinv : normalizedInverse (zeroCoefficient Γ) = id := by
    funext z
    have h := (normalizedInverse_spec (zeroCoefficient Γ)).choose_spec.2.1 z
    rw [normalizedMap_zeroCoefficient] at h
    exact h
  have h := translation_eq_actual_composite_ae (zeroCoefficient Γ) μ
  change translation (zeroCoefficient Γ) μ.val.val =ᵐ[volume]
    (fun z : ℍ => LiZhongQC.upperHalf.indicator
      (fun w : ℂ => LiZhongQC.complexDilatation
        (normalizedMap μ ∘ normalizedInverse (zeroCoefficient Γ)) w) (z : ℂ)) at h
  rw [hinv, Function.comp_id] at h
  apply Lp.ext
  filter_upwards [h, normalizedMap_dilatation_ae μ] with z hz hμ
  rw [indicator_of_mem (show (z : ℂ) ∈ LiZhongQC.upperHalf from z.im_pos)] at hz
  exact hz.trans hμ

private theorem source_reference_identity {Y : Type} [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] (a : LiZhongQC.TeichSpace Y) :
    SourceReferenceChange.quotientMap (Homeomorph.refl Y) LiZhongQC.isQCRS_refl a = a := by
  refine Quot.inductionOn a ?_
  intro m
  refine Quot.sound ⟨Homeomorph.refl m.X.carrier, LiZhongQC.isBiholomorphic_id, ?_⟩
  change ContinuousMap.Homotopic
    (⟨m.marking, m.marking.continuous⟩ : C(Y, m.X.carrier))
    (⟨m.marking, m.marking.continuous⟩ : C(Y, m.X.carrier))
  exact ContinuousMap.Homotopic.refl _

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

/-- On the entire ball, the prescribed conjugated covering and actual inverse
coefficient isometry represent the same original marked point. -/
theorem coefficientProjectionBall_realMobius_conjugate (Q : Deck) (μ : Ball Γ) :
    letI := R.toRiemannAtlas.toChartedSpace
    let ΓQ := LiZhongQC.conjGroup Γ Q
    let pQ := LiZhongQC.adjustProjection p Q
    let hpQ : LiZhongQC.IsUniformization ΓQ pQ := LiZhongQC.adjustProjection_isUniformization hp Q
    coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ (LiZhongQC.s27g_actsFreely hp) hp μ =
      coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
        (BersWeighted.isFuchsian_realConjugate hΓ Q) (LiZhongQC.s27g_actsFreely hpQ) hpQ
        ((coefficientRealMobiusBallEquiv Γ Q).symm μ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let ΓQ := LiZhongQC.conjGroup Γ Q
  let pQ := LiZhongQC.adjustProjection p Q
  have hpQ : LiZhongQC.IsUniformization ΓQ pQ := LiZhongQC.adjustProjection_isUniformization hp Q
  let hΓQ := BersWeighted.isFuchsian_realConjugate hΓ Q
  let e := Homeomorph.refl X
  let w : ℍ ≃ₜ ℍ := Homeomorph.smul Q
  have hw : LiZhongQC.IsLift p pQ e w := by
    intro z
    change p (Q⁻¹ • (Q • z)) = p z
    rw [inv_smul_smul]
  have hM : ∀ z : ℍ, normalizedUpperEquiv (zeroCoefficient Γ) z = Q⁻¹ • w z := by
    intro z
    change normalizedUpperEquiv (zeroCoefficient Γ) z = Q⁻¹ • (Q • z)
    rw [inv_smul_smul]
    apply UpperHalfPlane.ext
    change normalizedMap (zeroCoefficient Γ) (z : ℂ) = (z : ℂ)
    rw [normalizedMap_zeroCoefficient]
    rfl
  have hball : givenReferenceChangedBall hp hpQ hΓ e w hw
      (zeroCoefficient Γ) Q⁻¹ hM μ = (coefficientRealMobiusBallEquiv Γ Q).symm μ := by
    apply Subtype.ext
    apply Subtype.ext
    calc
      _ = pullback Q⁻¹ (translation (zeroCoefficient Γ) μ.val.val) :=
        givenReferenceChangedBall_val hp hpQ hΓ e w hw (zeroCoefficient Γ) Q⁻¹ hM μ
      _ = pullback Q⁻¹ μ.val.val := by rw [translation_zeroCoefficient]
      _ = _ := (coefficientRealMobiusIsometry_symm_val Γ Q μ.val).symm
  apply toSource_injective R
  have h := source_referenceChange_coefficientProjection R R hg hgenus hgenus hΓ hΓQ
    hp hpQ e LiZhongQC.isQCRS_refl w hw (zeroCoefficient Γ) Q⁻¹ hM μ
  dsimp only at h
  rw [hball] at h
  exact (source_reference_identity _).symm.trans h

/-- Every original compatible direction has the same real coefficient-curve
germ after the prescribed real Mobius change of its covering coordinates. -/
theorem coefficientProjection_realScalar_realMobius_germ (Q : Deck) (μ : Space Γ) :
    letI := R.toRiemannAtlas.toChartedSpace
    let ΓQ := LiZhongQC.conjGroup Γ Q
    let pQ := LiZhongQC.adjustProjection p Q
    let hpQ : LiZhongQC.IsUniformization ΓQ pQ := LiZhongQC.adjustProjection_isUniformization hp Q
    let μQ := (coefficientRealMobiusIsometry Γ Q).symm μ
    (fun t : ℝ => coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ (LiZhongQC.s27g_actsFreely hp) hp ((t : ℂ) • μ)) =ᶠ[𝓝 0]
      (fun t : ℝ => coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g)
        (BersWeighted.isFuchsian_realConjugate hΓ Q) (LiZhongQC.s27g_actsFreely hpQ) hpQ
        ((t : ℂ) • μQ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let ΓQ := LiZhongQC.conjGroup Γ Q
  let pQ := LiZhongQC.adjustProjection p Q
  have hpQ : LiZhongQC.IsUniformization ΓQ pQ := LiZhongQC.adjustProjection_isUniformization hp Q
  let μQ := (coefficientRealMobiusIsometry Γ Q).symm μ
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖(t : ℂ) • μ‖ < 1 :=
    (isOpen_lt ((Complex.continuous_ofReal.smul continuous_const).norm) continuous_const).mem_nhds
      (by
        change ‖((0 : ℂ) • μ : Space Γ)‖ < 1
        rw [zero_smul, norm_zero]
        exact zero_lt_one)
  filter_upwards [hnear] with t ht
  have hnorm : ‖(t : ℂ) • μQ‖ = ‖(t : ℂ) • μ‖ := by
    change ‖(t : ℂ) • (coefficientRealMobiusIsometry Γ Q).symm μ‖ = ‖(t : ℂ) • μ‖
    rw [← (coefficientRealMobiusIsometry Γ Q).symm.map_smul]
    exact (coefficientRealMobiusIsometry Γ Q).symm.norm_map _
  have htQ : ‖(t : ℂ) • μQ‖ < 1 := hnorm.trans_lt ht
  let ν : Ball Γ := ⟨(t : ℂ) • μ, by simpa only [Metric.mem_ball, dist_zero_right] using ht⟩
  have hν : (coefficientRealMobiusBallEquiv Γ Q).symm ν =
      (⟨(t : ℂ) • μQ, by simpa only [Metric.mem_ball, dist_zero_right] using htQ⟩ : Ball ΓQ) := by
    apply Subtype.ext
    change (coefficientRealMobiusIsometry Γ Q).symm ((t : ℂ) • μ) = (t : ℂ) • μQ
    exact (coefficientRealMobiusIsometry Γ Q).symm.map_smul _ _
  have h := coefficientProjectionBall_realMobius_conjugate R hg hgenus hΓ hp Q ν
  rw [hν] at h
  dsimp only [μQ] at htQ h
  simpa only [coefficientProjection, dite_eq_left ht, dite_eq_left htQ, ν] using h

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
