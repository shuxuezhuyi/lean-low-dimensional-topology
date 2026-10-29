module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeGammaCoefficientTransport
public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicDerivative

/-!
# The actual translated Bers composite has the transported genuine derivative

The actual normalized coefficient translation is followed by the actual
Bers projection for the genuine deformed group. Its true derivative at the
original nonzero coefficient is the literal deformed Bers integral composed
with the proved coefficient transport. Its source value agrees exactly with
the original Bers-coordinate translation applied to the original Bers value.
This is a derivative of that actual composite; differentiability and
invertibility of the Bers-coordinate translation itself remain separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The translated native class is the unchanged actual normalized source composition class. -/
theorem gammaTranslation_val_eq_sourceAmbient (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    (gammaTranslation hΓ ν μ.val).val = sourceAmbient (translatedSource hΓ ν μ).val := by
  apply Lp.ext
  filter_upwards [translation_eq_actual_composite_ae ν μ,
    sourceAmbient_coe_ae (translatedSource hΓ ν μ).val] with z ht hs
  exact ht.trans hs.symm

/-- Actual translation preserves the original open coefficient ball in the deformed group. -/
theorem norm_gammaTranslation_lt_one (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    ‖gammaTranslation hΓ ν μ.val‖ < 1 := by
  change ‖(gammaTranslation hΓ ν μ.val).val‖ < 1
  rw [gammaTranslation_val_eq_sourceAmbient]
  exact norm_sourceAmbient_lt_one _

/-- The actual translated coefficient, with its proved subunit norm. -/
def translatedBall (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    Ball (deformedGroup hΓ ν) :=
  ⟨gammaTranslation hΓ ν μ.val, by
    simpa only [Metric.mem_ball, dist_zero_right] using norm_gammaTranslation_lt_one hΓ ν μ⟩

theorem translatedBall_eq_fromSource (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    translatedBall hΓ ν μ = fromSourceGamma (translatedSource hΓ ν μ) := by
  apply Subtype.ext
  apply Subtype.ext
  exact gammaTranslation_val_eq_sourceAmbient hΓ ν μ

/-- The actual deformed-group Bers projection of the actual normalized translated coefficient. -/
def translatedBersProjection (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) (μ : Space Γ) :
    BersWeighted.Automorphic (deformedGroup hΓ ν) :=
  BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1 (gammaTranslation hΓ ν μ)

/-- The exact source function is the genuine original Bers-coordinate translation value. -/
theorem translatedBersProjection_source (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    ((translatedBersProjection hΓ ν μ.val).toSource : ℂ → ℂ) =
      LiZhongQC.b33_t_chi (toSourceGamma ν).val (bersProjection μ) := by
  have he : ((translatedBersProjection hΓ ν μ.val).toSource : ℂ → ℂ) =
      bersProjection (translatedBall hΓ ν μ) := by
    change BersWeighted.decode (BersWeighted.projection (gammaTranslation hΓ ν μ.val)) = _
    rw [BersWeighted.projection, dite_eq_left (norm_gammaTranslation_lt_one hΓ ν μ)]
    exact BersWeighted.decode_projectionValue (translatedBall hΓ ν μ)
  have hs := sourceBers_congr_ae
    (toSourceGamma (fromSourceGamma (translatedSource hΓ ν μ))) (translatedSource hΓ ν μ)
    (toSourceGamma_fromSourceGamma_ae (translatedSource hΓ ν μ))
  calc
    _ = bersProjection (translatedBall hΓ ν μ) := he
    _ = LiZhongQC.bersFunction (translatedSource hΓ ν μ).val.val := by
      rw [translatedBall_eq_fromSource, bersProjection_eq]
      exact hs
    _ = _ := by
      rw [bersProjection_eq]
      exact (LiZhongQC.b33_t_chi_spec (toSourceGamma ν).val (toSourceGamma μ).val).symm

/-- The actual translated Bers composite sends the original nonzero base to zero. -/
theorem translatedBersProjection_base (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    translatedBersProjection hΓ ν ν.val = 0 := by
  have hz : gammaTranslation hΓ ν ν.val = 0 := by
    apply Subtype.ext
    exact translation_base ν
  apply Subtype.ext
  change BersWeighted.projection (gammaTranslation hΓ ν ν.val) = 0
  rw [hz, BersWeighted.projection_zero]

/-- The genuine nonzero derivative of the actual composite is exactly the transported integral. -/
theorem hasFDerivAt_translatedBersProjection (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    HasFDerivAt (translatedBersProjection hΓ ν)
      ((BersWeighted.automorphicIntegralOperator (deformedGroup_spec hΓ ν).1).comp
        (gammaDerivative hΓ ν)) ν.val := by
  have hz : gammaTranslation hΓ ν ν.val = 0 := by
    apply Subtype.ext
    exact translation_base ν
  have hd := BersWeighted.hasFDerivAt_automorphicProjection (deformedGroup_spec hΓ ν).1
  rw [← hz] at hd
  exact hd.comp ν.val (hasFDerivAt_gammaTranslation hΓ ν)

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
