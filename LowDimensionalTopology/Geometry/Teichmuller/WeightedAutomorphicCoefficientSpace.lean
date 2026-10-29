module

public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadraticTransport
public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadraticTransportInverse
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Weighted automorphic coefficients as a closed complex subspace

The actual weighted coefficients are conjugates of compatible Beltrami
classes in the same L-infinity space. The norm is inherited from that
space, and every original measurable automorphic input retains its exact
weighted essential norm. Reverse pointwise representative selection is separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicCoefficient

open GammaMeasurableBeltrami

private def conjugation : Ambient ≃ₗᵢ⋆[ℂ] Ambient where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' u v := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (u + v), Lp.coeFn_add u v,
      Lp.coeFn_add (star u) (star v), Lp.coeFn_star u, Lp.coeFn_star v]
      with z h₀ h₁ h₂ h₃ h₄
    rw [h₀, h₂]
    change star ((u + v) z) = (star u : Ambient) z + (star v : Ambient) z
    rw [h₃, h₄, h₁]
    exact star_add _ _
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (c • u), Lp.coeFn_smul c u,
      Lp.coeFn_smul (star c) (star u), Lp.coeFn_star u] with z h₀ h₁ h₂ h₃
    change (star (c • u) : Ambient) z = (star c • star u : Ambient) z
    rw [h₀, h₂]
    change star ((c • u) z) = star c • (star u : Ambient) z
    rw [h₃, h₁]
    exact star_smul c (u z)
  norm_map' u := by
    change ‖(star u : Ambient)‖ = ‖u‖
    apply le_antisymm
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [Lp.coeFn_star u] with z hz
      rw [hz]
      change ‖conj (u z)‖ ≤ ‖u z‖
      exact (Complex.norm_conj _).le
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [Lp.coeFn_star u] with z hz
      rw [hz]
      change ‖u z‖ ≤ ‖conj (u z)‖
      exact (Complex.norm_conj _).ge

/-- The actual weighted coefficient condition in the original L-infinity carrier. -/
def coefficientSubmodule (Γ : Subgroup Deck) : Submodule ℂ Ambient :=
  (compatibleSubmodule Γ).comap
    ({
      toFun := star
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [Lp.coeFn_star (u + v), Lp.coeFn_add u v,
          Lp.coeFn_add (star u) (star v), Lp.coeFn_star u, Lp.coeFn_star v]
          with z h₀ h₁ h₂ h₃ h₄
        rw [h₀, h₂]
        change star ((u + v) z) = (star u : Ambient) z + (star v : Ambient) z
        rw [h₃, h₄, h₁]
        exact star_add _ _
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [Lp.coeFn_star (c • u), Lp.coeFn_smul c u,
          Lp.coeFn_smul (star c) (star u), Lp.coeFn_star u] with z h₀ h₁ h₂ h₃
        change (star (c • u) : Ambient) z = (star c • star u : Ambient) z
        rw [h₀, h₂]
        change star ((c • u) z) = star c • (star u : Ambient) z
        rw [h₃, h₁]
        exact star_smul c (u z) } : Ambient →ₗ⋆[ℂ] Ambient)

theorem mem_coefficientSubmodule_iff {Γ : Subgroup Deck} (g : Ambient) :
    g ∈ coefficientSubmodule Γ ↔ star g ∈ compatibleSubmodule Γ := Iff.rfl

theorem isClosed_coefficientSubmodule (Γ : Subgroup Deck) :
    IsClosed (coefficientSubmodule Γ : Set Ambient) := by
  change IsClosed (conjugation ⁻¹' (compatibleSubmodule Γ : Set Ambient))
  exact (isClosed_compatibleSubmodule Γ).preimage conjugation.continuous

/-- The weighted automorphic subspace carries the original inherited norm. -/
def coefficientClosedSubmodule (Γ : Subgroup Deck) : ClosedSubmodule ℂ Ambient :=
  ⟨coefficientSubmodule Γ, isClosed_coefficientSubmodule Γ⟩

abbrev Space (Γ : Subgroup Deck) := ↥(coefficientClosedSubmodule Γ)

theorem completeSpace (Γ : Subgroup Deck) : CompleteSpace (Space Γ) := inferInstance

/-- Conjugating an actual compatible class gives a weighted coefficient class. -/
def ofBeltrami {Γ : Subgroup Deck} (μ : GammaMeasurableBeltrami.Space Γ) : Space Γ :=
  ⟨star μ.val, by
    change star (star μ.val) ∈ compatibleSubmodule Γ
    have hμ : μ.val ∈ compatibleSubmodule Γ := μ.property
    simpa only [star_star] using hμ⟩

/-- The reverse map retains the entire compatible class. -/
def toBeltrami {Γ : Subgroup Deck} (g : Space Γ) : GammaMeasurableBeltrami.Space Γ :=
  ⟨star g.val, g.property⟩

theorem norm_ofBeltrami {Γ : Subgroup Deck} (μ : GammaMeasurableBeltrami.Space Γ) :
    ‖ofBeltrami μ‖ = ‖μ‖ := conjugation.norm_map μ.val

theorem toBeltrami_ofBeltrami {Γ : Subgroup Deck} (μ : GammaMeasurableBeltrami.Space Γ) :
    toBeltrami (ofBeltrami μ) = μ := Subtype.ext (star_star μ.val)

theorem ofBeltrami_toBeltrami {Γ : Subgroup Deck} (g : Space Γ) :
    ofBeltrami (toBeltrami g) = g := Subtype.ext (star_star g.val)

theorem toBeltrami_add {Γ : Subgroup Deck} (g h : Space Γ) :
    toBeltrami (g + h) = toBeltrami g + toBeltrami h :=
  Subtype.ext (conjugation.map_add g.val h.val)

theorem toBeltrami_smul {Γ : Subgroup Deck} (c : ℂ) (g : Space Γ) :
    toBeltrami (c • g) = star c • toBeltrami g :=
  Subtype.ext (conjugation.map_smulₛₗ c g.val)

theorem norm_toBeltrami {Γ : Subgroup Deck} (g : Space Γ) :
    ‖toBeltrami g‖ = ‖g‖ := conjugation.norm_map g.val

/-- Actual coefficient conjugation is an antilinear isometry onto the full Beltrami space. -/
def beltramiEquiv (Γ : Subgroup Deck) :
    Space Γ ≃ₗᵢ⋆[ℂ] GammaMeasurableBeltrami.Space Γ where
  toFun := toBeltrami
  invFun := ofBeltrami
  left_inv := ofBeltrami_toBeltrami
  right_inv := toBeltrami_ofBeltrami
  map_add' := toBeltrami_add
  map_smul' := toBeltrami_smul
  norm_map' := norm_toBeltrami

variable {Γ : Subgroup Deck} (f : ℍ → ℂ)
    (hf : AEStronglyMeasurable f flatMeasure)
    (ha : ∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) / denominator γ z ^ 4 = f z)
    (hb : ∃ M : ℝ, ∀ᵐ z ∂flatMeasure, ‖f z‖ * z.im ^ 2 ≤ M)

/-- Every original measurable weighted-bounded automorphic coefficient is retained. -/
def ofRaw : Space Γ := ofBeltrami (MeasurableQuadratic.toBeltrami f hf ha hb)

theorem ofRaw_coe_ae :
    (ofRaw f hf ha hb).val =ᵐ[volume] MeasurableQuadratic.weightedValue f := by
  filter_upwards [Lp.coeFn_star (MeasurableQuadratic.toBeltrami f hf ha hb).val,
    MeasurableQuadratic.toBeltrami_coe_ae f hf ha hb] with z hs hμ
  change (star (MeasurableQuadratic.toBeltrami f hf ha hb).val : Ambient) z = _
  rw [hs]
  change star ((MeasurableQuadratic.toBeltrami f hf ha hb).val z) = _
  rw [hμ]
  exact star_star (MeasurableQuadratic.weightedValue f z)

theorem ofRaw_coe_ae_flat :
    (ofRaw f hf ha hb).val =ᵐ[flatMeasure] MeasurableQuadratic.weightedValue f :=
  ae_hyperbolic_iff.mp (ofRaw_coe_ae f hf ha hb)

/-- The class norm is exactly the original weighted essential norm. -/
theorem norm_ofRaw : ‖ofRaw f hf ha hb‖ = MeasurableQuadratic.weightedEssNorm f :=
  (norm_ofBeltrami _).trans (MeasurableQuadratic.norm_toBeltrami f hf ha hb)

/-- Every coefficient class has an original pointwise automorphic representative. -/
theorem exists_raw_representative {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (g : Space Γ) :
    ∃ f : ℍ → ℂ,
      ∃ hf : AEStronglyMeasurable f flatMeasure,
      ∃ ha : ∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) / denominator γ z ^ 4 = f z,
      ∃ hb : ∃ M : ℝ, ∀ᵐ z ∂flatMeasure, ‖f z‖ * z.im ^ 2 ≤ M,
      ofRaw f hf ha hb = g ∧ MeasurableQuadratic.weightedEssNorm f = ‖g‖ := by
  obtain ⟨f, hf, ha, hb, hμ, hn⟩ :=
    MeasurableQuadratic.exists_quadratic_preimage hΓ (toBeltrami g)
  refine ⟨f, hf, ha, hb, ?_, hn.trans (norm_toBeltrami g)⟩
  exact (congrArg ofBeltrami hμ).trans (ofBeltrami_toBeltrami g)

end LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicCoefficient
