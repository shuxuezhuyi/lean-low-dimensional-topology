module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaSourceCoefficient

/-!
# Source quasiconformal coefficients as actual native compatible classes

The literal upper-half-plane restriction of a valid source coefficient gives
an element of the existing hyperbolic L-infinity ball. Source compatibility
proves the native deck law; the maps retain the actual almost-everywhere
class in both directions. This interface is used for the actual translated
and pulled-back normalized coefficients, without postulating native values.

The planar coefficient and compatibility interface uses Wu Xiaobin's
LiZhongQC source, Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

/-- The unchanged upper restriction is bounded for the actual hyperbolic null class. -/
theorem sourceAmbient_memLp (μ : LiZhongQC.BeltramiH) :
    MemLp (fun z : ℍ => μ.val z) (⊤ : ℝ≥0∞) volume := by
  obtain ⟨k, _, _, hμ⟩ := LiZhongQC.bg_beltramiH_upper μ
  exact memLp_top_of_bound (aestronglyMeasurable_plane_iff.mp hμ.1) k
    (ae_plane_iff.mp hμ.2)

/-- The actual coefficient class of the source's literal representative. -/
def sourceAmbient (μ : LiZhongQC.BeltramiH) : Ambient :=
  (sourceAmbient_memLp μ).toLp (fun z : ℍ => μ.val z)

theorem sourceAmbient_coe_ae (μ : LiZhongQC.BeltramiH) :
    sourceAmbient μ =ᵐ[volume] fun z : ℍ => μ.val z :=
  (sourceAmbient_memLp μ).coeFn_toLp

theorem norm_sourceAmbient_lt_one (μ : LiZhongQC.BeltramiH) :
    ‖sourceAmbient μ‖ < 1 := by
  obtain ⟨k, hk0, hk1, hμ⟩ := LiZhongQC.bg_beltramiH_upper μ
  apply lt_of_le_of_lt _ hk1
  apply lpInfinity_norm_le_of_ae_bound _ hk0
  filter_upwards [sourceAmbient_coe_ae μ, ae_plane_iff.mp hμ.2] with z hz hb
  rw [hz]
  exact hb

/-- The source's genuine planar deck equation implies the native compatible subspace. -/
theorem sourceAmbient_mem_compatible {Γ : Subgroup Deck}
    (μ : LiZhongQC.BeltramiGamma Γ) :
    sourceAmbient μ.val ∈ compatibleSubmodule Γ := by
  apply (mem_compatibleSubmodule_iff _).mpr
  intro γ hγ
  have hs := ae_plane_iff.mp (μ.property γ hγ)
  filter_upwards [sourceAmbient_coe_ae μ.val,
    (measurePreserving_deck γ).quasiMeasurePreserving.ae (sourceAmbient_coe_ae μ.val),
    hs] with z hz hγz he
  rw [hz, hγz]
  have hm : μ.val.val (((γ • (z : ℍ) : ℍ) : ℂ)) =
      μ.val.val (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) := by
    rw [LiZhongQC.h23l_b_coe_smul]
  rw [← hm] at he
  simpa only [phase, denominator, mul_comm] using he

/-- Every actual compatible source coefficient gives its native compatible class. -/
def fromSourceGamma {Γ : Subgroup Deck} (μ : LiZhongQC.BeltramiGamma Γ) : Ball Γ :=
  ⟨⟨sourceAmbient μ.val, sourceAmbient_mem_compatible μ⟩, by
    rw [Metric.mem_ball, dist_zero_right, ← ClosedSubmodule.norm_coe]
    exact norm_sourceAmbient_lt_one μ.val⟩

theorem fromSourceGamma_coe_ae {Γ : Subgroup Deck} (μ : LiZhongQC.BeltramiGamma Γ) :
    (fromSourceGamma μ).val.val =ᵐ[volume] fun z : ℍ => μ.val.val z :=
  sourceAmbient_coe_ae μ.val

/-- The actual native ball element survives the source passage unchanged. -/
theorem fromSourceGamma_toSourceGamma {Γ : Subgroup Deck} (μ : Ball Γ) :
    fromSourceGamma (toSourceGamma μ) = μ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [fromSourceGamma_coe_ae (toSourceGamma μ)] with z hz
  simpa only [toSourceGamma, planeRepresentative_coe] using hz

/-- A source representative is retained up to precisely its original planar a.e. relation. -/
theorem toSourceGamma_fromSourceGamma_ae {Γ : Subgroup Deck}
    (μ : LiZhongQC.BeltramiGamma Γ) :
    (toSourceGamma (fromSourceGamma μ)).val.val =ᵐ[volume.restrict LiZhongQC.upperHalf]
      μ.val.val := by
  apply ae_plane_iff.mpr
  filter_upwards [fromSourceGamma_coe_ae μ] with z hz
  simpa only [toSourceGamma, planeRepresentative_coe] using hz

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
