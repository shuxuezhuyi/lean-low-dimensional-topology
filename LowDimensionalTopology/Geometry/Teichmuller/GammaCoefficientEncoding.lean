module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

/-!
# Encoding actual measurable deck-compatible coefficients

The passage from planar coefficients to hyperbolic L-infinity classes preserves
almost-everywhere equality and its sharp bound. Conversely every compatible class
is recovered from its actual planar representative. These are genuine Banach
classes; no raw-function supremum seminorm is used as a norm.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

/-- A bounded measurable planar coefficient defines an actual hyperbolic L-infinity class. -/
theorem coefficientMemLp {μ : ℂ → ℂ} {k : ℝ}
    (hμ : LiZhongQC.IsBeltramiCoeff μ LiZhongQC.upperHalf k) :
    MemLp (fun z : ℍ => μ (z : ℂ)) (⊤ : ℝ≥0∞) volume :=
  memLp_top_of_bound (aestronglyMeasurable_plane_iff.1 hμ.1) k
    (ae_plane_iff.1 hμ.2)

/-- Encode an actual compatible coefficient into the proved closed Banach subspace. -/
def ofCoefficient {Γ : Subgroup Deck} {μ : ℂ → ℂ} {k : ℝ}
    (hμ : LiZhongQC.IsBeltramiCoeff μ LiZhongQC.upperHalf k)
    (hΓ : LiZhongQC.IsGammaCompatible Γ μ) : Space Γ := by
  let ν : Ambient := (coefficientMemLp hμ).toLp (fun z : ℍ => μ (z : ℂ))
  refine ⟨ν, (mem_compatibleSubmodule_iff ν).2 ?_⟩
  intro γ hγ
  have hrep : ν =ᵐ[volume] fun z : ℍ => μ (z : ℂ) :=
    (coefficientMemLp hμ).coeFn_toLp
  have hdeck := (measurePreserving_deck γ).quasiMeasurePreserving.ae_eq_comp hrep
  have hcompat := ae_plane_iff.1 (hΓ γ hγ)
  filter_upwards [hrep, hdeck, hcompat] with z hz hγz hc
  change ν (γ • z) = μ ((γ • z : ℍ) : ℂ) at hγz
  rw [hz, hγz, LiZhongQC.h23l_b_coe_smul]
  simpa only [phase, denominator, mul_comm] using hc

/-- Encoding retains the actual coefficient almost everywhere in hyperbolic area. -/
theorem ofCoefficient_coe_ae {Γ : Subgroup Deck} {μ : ℂ → ℂ} {k : ℝ}
    (hμ : LiZhongQC.IsBeltramiCoeff μ LiZhongQC.upperHalf k)
    (hΓ : LiZhongQC.IsGammaCompatible Γ μ) :
    ((ofCoefficient hμ hΓ).val : ℍ → ℂ) =ᵐ[volume] fun z : ℍ => μ (z : ℂ) := by
  change ((coefficientMemLp hμ).toLp (fun z : ℍ => μ (z : ℂ)) : ℍ → ℂ) =ᵐ[volume]
    fun z : ℍ => μ (z : ℂ)
  exact (coefficientMemLp hμ).coeFn_toLp

/-- Every actual almost-everywhere bound controls the intrinsic Banach norm. -/
theorem norm_ofCoefficient_le {Γ : Subgroup Deck} {μ : ℂ → ℂ} {k : ℝ}
    (hk : 0 ≤ k) (hμ : LiZhongQC.IsBeltramiCoeff μ LiZhongQC.upperHalf k)
    (hΓ : LiZhongQC.IsGammaCompatible Γ μ) : ‖ofCoefficient hμ hΓ‖ ≤ k := by
  change ‖(ofCoefficient hμ hΓ).val‖ ≤ k
  apply lpInfinity_norm_le_of_ae_bound (ofCoefficient hμ hΓ).val hk
  filter_upwards [ofCoefficient_coe_ae hμ hΓ, ae_plane_iff.1 hμ.2] with z hz hb
  rw [hz]
  exact hb

/-- Equality of compatible Banach classes is exactly planar a.e. equality. -/
theorem ofCoefficient_eq_iff {Γ : Subgroup Deck} {μ ν : ℂ → ℂ} {k l : ℝ}
    (hμ : LiZhongQC.IsBeltramiCoeff μ LiZhongQC.upperHalf k)
    (hΓμ : LiZhongQC.IsGammaCompatible Γ μ)
    (hν : LiZhongQC.IsBeltramiCoeff ν LiZhongQC.upperHalf l)
    (hΓν : LiZhongQC.IsGammaCompatible Γ ν) :
    ofCoefficient hμ hΓμ = ofCoefficient hν hΓν ↔
      μ =ᵐ[volume.restrict LiZhongQC.upperHalf] ν := by
  constructor
  · intro heq
    apply ae_plane_iff.2
    have h := ofCoefficient_coe_ae hμ hΓμ
    rw [heq] at h
    exact h.symm.trans (ofCoefficient_coe_ae hν hΓν)
  · intro h
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [ofCoefficient_coe_ae hμ hΓμ, ae_plane_iff.1 h,
      ofCoefficient_coe_ae hν hΓν] with z hzμ hμν hzν
    exact hzμ.trans (hμν.trans hzν.symm)

/-- Re-encoding the actual planar representative recovers the compatible class. -/
theorem ofCoefficient_planeRepresentative {Γ : Subgroup Deck} (μ : Space Γ) :
    ofCoefficient (planeRepresentative_isBeltramiCoeff μ.val)
      (planeRepresentative_isGammaCompatible μ) = μ := by
  apply Subtype.ext
  apply Lp.ext
  exact (ofCoefficient_coe_ae (planeRepresentative_isBeltramiCoeff μ.val)
    (planeRepresentative_isGammaCompatible μ)).trans
      (Eventually.of_forall (planeRepresentative_coe μ.val))

/-- The intrinsic norm is the least nonnegative actual a.e. planar bound. -/
theorem norm_le_iff_plane_bound {Γ : Subgroup Deck} (μ : Space Γ) {k : ℝ} (hk : 0 ≤ k) :
    ‖μ‖ ≤ k ↔ ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      ‖planeRepresentative μ.val z‖ ≤ k := by
  constructor
  · intro h
    filter_upwards [(planeRepresentative_isBeltramiCoeff μ.val).2] with z hz
    exact hz.trans h
  · intro h
    change ‖μ.val‖ ≤ k
    apply lpInfinity_norm_le_of_ae_bound μ.val hk
    have hh := ae_plane_iff.1 h
    simpa only [planeRepresentative_coe] using hh

/-- A genuinely subunit coefficient encodes into the actual open unit ball. -/
def ofCoefficientBall {Γ : Subgroup Deck} {μ : ℂ → ℂ} {k : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : LiZhongQC.IsBeltramiCoeff μ LiZhongQC.upperHalf k)
    (hΓ : LiZhongQC.IsGammaCompatible Γ μ) : Ball Γ :=
  ⟨ofCoefficient hμ hΓ, by
    rw [Metric.mem_ball, dist_zero_right]
    exact (norm_ofCoefficient_le hk₀ hμ hΓ).trans_lt hk⟩

/-- Every ball element is recovered from its own chosen measurable representative. -/
theorem ofCoefficientBall_planeRepresentative {Γ : Subgroup Deck} (μ : Ball Γ) :
    ofCoefficientBall (norm_nonneg μ.val) (Ball.norm_lt_one μ)
      (planeRepresentative_isBeltramiCoeff μ.val.val)
      (planeRepresentative_isGammaCompatible μ.val) = μ := by
  apply Subtype.ext
  exact ofCoefficient_planeRepresentative μ.val

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
