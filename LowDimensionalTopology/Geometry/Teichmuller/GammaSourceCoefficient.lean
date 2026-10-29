module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaCoefficientEncoding

/-!
# Actual measurable coefficients in the source Bers projection

The genuine L-infinity classes retain their chosen planar representatives in the
source Gamma ball. Scalar multiplication agrees almost everywhere, which suffices
for the actual Bers projection. The normalized-solution and Bers comparison APIs
are Wu Xiaobin's LiZhongQC development, Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

/-- The zero extension retains the actual class-norm bound on the whole plane. -/
theorem planeRepresentative_isBeltramiCoeff_univ (μ : Ambient) :
    LiZhongQC.IsBeltramiCoeff (planeRepresentative μ) Set.univ ‖μ‖ := by
  classical
  have hB := planeRepresentative_isBeltramiCoeff μ
  have hind : LiZhongQC.upperHalf.indicator (planeRepresentative μ) =
      planeRepresentative μ := by
    funext z
    by_cases hz : z ∈ LiZhongQC.upperHalf
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz, planeRepresentative_off μ hz]
  rw [LiZhongQC.IsBeltramiCoeff, Measure.restrict_univ]
  refine ⟨?_, ?_⟩
  · rw [← hind]
    exact (aestronglyMeasurable_indicator_iff
      LiZhongQC.isOpen_upperHalf.measurableSet).2 hB.1
  · have hb := (ae_restrict_iff' LiZhongQC.isOpen_upperHalf.measurableSet).1 hB.2
    filter_upwards [hb] with z hz
    by_cases hzU : z ∈ LiZhongQC.upperHalf
    · exact hz hzU
    · rw [planeRepresentative_off μ hzU, norm_zero]
      exact norm_nonneg μ

/-- L-infinity scalar multiplication is retained by planar representatives a.e. -/
theorem planeRepresentative_smul_ae (c : ℂ) (μ : Ambient) :
    planeRepresentative (c • μ) =ᵐ[volume.restrict LiZhongQC.upperHalf]
      c • planeRepresentative μ := by
  apply ae_plane_iff.2
  filter_upwards [Lp.coeFn_smul c μ] with z hz
  simpa only [planeRepresentative_coe, Pi.smul_apply] using hz

/-- Encode the actual chosen planar representative into the source Gamma ball. -/
def toSourceGamma {Γ : Subgroup Deck} (μ : Ball Γ) : LiZhongQC.BeltramiGamma Γ :=
  ⟨⟨planeRepresentative μ.val.val,
    ⟨⟨‖μ.val.val‖, norm_nonneg _, Ball.norm_lt_one μ,
      planeRepresentative_isBeltramiCoeff_univ μ.val.val⟩,
      fun _ hz => planeRepresentative_off μ.val.val (not_lt.2 hz)⟩⟩,
    planeRepresentative_isGammaCompatible μ.val⟩

/-- Source Bers functions depend only on the actual upper-half-plane a.e. class. -/
theorem sourceBers_congr_ae {Γ : Subgroup Deck} (μ ν : LiZhongQC.BeltramiGamma Γ)
    (h : μ.val.val =ᵐ[volume.restrict LiZhongQC.upperHalf] ν.val.val) :
    LiZhongQC.bersFunction μ.val.val = LiZhongQC.bersFunction ν.val.val := by
  obtain ⟨k, hk₀, hk₁, hμ⟩ := LiZhongQC.bg_beltramiH_upper μ.val
  obtain ⟨l, hl₀, hl₁, hν⟩ := LiZhongQC.bg_beltramiH_upper ν.val
  have he := LiZhongQC.s27u_fSym_congr_ae hk₀ hk₁ hμ hl₀ hl₁ hν h
  apply LiZhongQC.bersFunctionGamma_eq_of_equiv
  intro x
  simpa only [LiZhongQC.s33v_fSym_eq] using congrFun he (x : ℂ)

/-- A subunit scalar multiple uses the literal scalar-times-planar coefficient. -/
def sourceGammaOfScalar {Γ : Subgroup Deck} (μ : Space Γ) (c : ℂ)
    (hc : ‖c‖ * ‖μ‖ < 1) : LiZhongQC.BeltramiGamma Γ := by
  have hB := planeRepresentative_isBeltramiCoeff_univ μ.val
  refine ⟨⟨fun z => c * planeRepresentative μ.val z, ⟨?_, ?_⟩⟩, ?_⟩
  · refine ⟨‖c‖ * ‖μ‖, mul_nonneg (norm_nonneg c) (norm_nonneg μ), hc,
      hB.1.const_mul c, ?_⟩
    filter_upwards [hB.2] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hz (norm_nonneg c)
  · intro z hz
    change c * planeRepresentative μ.val z = 0
    rw [planeRepresentative_off μ.val (not_lt.2 hz), mul_zero]
  · intro γ hγ
    filter_upwards [planeRepresentative_isGammaCompatible μ γ hγ] with z hz
    simpa only [mul_assoc] using congrArg (fun a : ℂ => c * a) hz

/-- The scalar encoding retains its actual raw function by definition. -/
theorem sourceGammaOfScalar_coe {Γ : Subgroup Deck} (μ : Space Γ) (c : ℂ)
    (hc : ‖c‖ * ‖μ‖ < 1) :
    (sourceGammaOfScalar μ c hc).val.val = fun z => c * planeRepresentative μ.val z := rfl

/-- The actual Bers projection of a native measurable Gamma-ball element. -/
def bersProjection {Γ : Subgroup Deck} (μ : Ball Γ) : ℂ → ℂ :=
  LiZhongQC.bersMapGamma Γ (Quotient.mk _ (toSourceGamma μ))

/-- The quotient projection is the Bers function of the exact chosen representative. -/
theorem bersProjection_eq {Γ : Subgroup Deck} (μ : Ball Γ) :
    bersProjection μ = LiZhongQC.bersFunction (planeRepresentative μ.val.val) := by
  change LiZhongQC.bersMapGamma Γ (Quotient.mk _ (toSourceGamma μ)) =
    LiZhongQC.bersFunction (toSourceGamma μ).val.val
  exact LiZhongQC.bg_bersMapGamma_eq (Γ := Γ) (μ := toSourceGamma μ)
    (p := Quotient.mk _ (toSourceGamma μ)) rfl

/-- The genuine native scalar family has the literal scalar-coefficient Bers image. -/
theorem bersProjection_smul {Γ : Subgroup Deck} (μ : Space Γ) (c : ℂ)
    (hc : ‖c‖ * ‖μ‖ < 1) :
    bersProjection (⟨c • μ, by
      simpa only [Metric.mem_ball, dist_zero_right, norm_smul] using hc⟩ : Ball Γ) =
      LiZhongQC.bersFunction (fun z => c * planeRepresentative μ.val z) := by
  rw [bersProjection_eq]
  exact sourceBers_congr_ae
    (toSourceGamma ⟨c • μ, by
      simpa only [Metric.mem_ball, dist_zero_right, norm_smul] using hc⟩)
    (sourceGammaOfScalar μ c hc) (planeRepresentative_smul_ae c μ.val)

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
