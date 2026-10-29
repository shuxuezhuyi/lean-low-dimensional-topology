module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicCoefficientSpace
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBergmanProjection

/-!
# The Bergman projection on the original weighted coefficient space

Conjugating the genuine harmonic projection by the actual coefficient
isometry gives a bounded complex-linear projection in the original norm.
On every original raw coefficient class its representative is the weighted
literal Bergman integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicCoefficient

open Surfaces GammaMeasurableBeltrami

variable {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

local notation "s" => beltramiEquiv Γ
local notation "H" => NativePetersson.harmonicProjection R P p hp F hF

/-- The two actual conjugations give a bounded complex-linear projection. -/
def bergmanProjection : Space Γ →L[ℂ] Space Γ where
  toFun u := (s).symm (H (s u))
  map_add' u v := by rw [map_add, map_add, map_add]
  map_smul' c u := by
    simp only [RingHom.id_apply]
    rw [LinearIsometryEquiv.map_smulₛₗ, map_smul,
      LinearIsometryEquiv.map_smulₛₗ, starRingEnd_self_apply]
  cont := (s).symm.continuous.comp ((H).continuous.comp (s).continuous)

@[simp] theorem bergmanProjection_apply (u : Space Γ) :
    bergmanProjection R P p hp F hF u = (s).symm (H (s u)) := rfl

/-- This bound uses exactly the original coefficient and Beltrami norms. -/
theorem norm_bergmanProjection_le (u : Space Γ) :
    ‖bergmanProjection R P p hp F hF u‖ ≤ ‖H‖ * ‖u‖ := by
  calc
    _ = ‖H (s u)‖ := (s).symm.norm_map _
    _ ≤ ‖H‖ * ‖s u‖ := (H).le_opNorm _
    _ = _ := by rw [(s).norm_map]

/-- The actual original harmonic idempotence transports to the coefficient space. -/
theorem bergmanProjection_idempotent (u : Space Γ) :
    bergmanProjection R P p hp F hF (bergmanProjection R P p hp F hF u) =
      bergmanProjection R P p hp F hF u := by
  change (s).symm (H (s ((s).symm (H (s u))))) = (s).symm (H (s u))
  rw [(s).apply_symm_apply, NativePetersson.harmonicProjection_idempotent]

/-- On every original raw coefficient, the projected weighted class is the
actual square-height multiple of the same literal Bergman kernel integral.
The native raw predicates are the original Euclidean-area predicates on H. -/
theorem bergmanProjection_ofRaw_coe_ae (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable (fun z : ℍ => f z) flatMeasure)
    (ha : ∀ A ∈ Γ, ∀ z : ℍ, f (A • z : ℍ) / denominator A z ^ 4 = f z)
    (hb : ∃ M : ℝ, ∀ᵐ z : ℍ ∂flatMeasure, ‖f z‖ * z.im ^ 2 ≤ M) :
    (bergmanProjection R P p hp F hF (ofRaw (fun z : ℍ => f z) hf ha hb)).val
      =ᵐ[volume] fun z : ℍ =>
        (z.im : ℂ) ^ 2 * MeasurableQuadratic.bergman f (z : ℂ) := by
  have hf' : AEStronglyMeasurable f (volume.restrict LiZhongQC.upperHalf) :=
    aestronglyMeasurable_plane_iff.mpr
      (hf.mono_ac (withDensity_absolutelyContinuous flatMeasure hyperbolicDensity))
  have ha' : ∀ A ∈ Γ, ∀ z ∈ LiZhongQC.upperHalf,
      f (LiZhongQC.h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = f z := by
    intro A hA z hz
    change f (LiZhongQC.h36p_m A (⟨z, hz⟩ : ℍ)) /
      denominator A ⟨z, hz⟩ ^ 4 = f (⟨z, hz⟩ : ℍ)
    rw [LiZhongQC.h36p_m_coe]
    exact ha A hA ⟨z, hz⟩
  have hb' : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      ‖f z‖ * z.im ^ 2 ≤ M := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, ae_plane_iff.mpr (ae_hyperbolic_iff.mpr hM)⟩
  let μ := MeasurableQuadratic.bergmanInput f hf' ha' hb'
  let q := NativePetersson.toQuadratic R P p hp F hF
    (NativePetersson.rieszQuadratic R P p hp F hF μ)
  have hμ : s (ofRaw (fun z : ℍ => f z) hf ha hb) = μ :=
    toBeltrami_ofBeltrami _
  change (star (H (s (ofRaw (fun z : ℍ => f z) hf ha hb))).val : Ambient) =ᵐ[volume] _
  rw [hμ, NativePetersson.harmonicProjection_apply]
  change (star (NativeHarmonicBeltrami.ofQuadratic R p hp q).val : Ambient)
    =ᵐ[volume] _
  filter_upwards [Lp.coeFn_star (NativeHarmonicBeltrami.ofQuadratic R p hp q).val,
    NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp q] with z hstar hq
  rw [hstar]
  change conj ((NativeHarmonicBeltrami.ofQuadratic R p hp q).val z) = _
  rw [hq, NativeHarmonicBeltrami.coefficient_eq_uniformized]
  simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj]
  exact congrArg (fun v : ℂ => (z.im : ℂ) ^ 2 * v)
    (MeasurableQuadratic.bergman_eq_uniformized f hf' ha' hb' R P p hp F hF z.im_pos).symm

end LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicCoefficient
