module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedBersTarget
public import LowDimensionalTopology.External.LiZhongQC.Ch10.S33_BersEmbedding
public import Mathlib.Tactic.FieldSimp

/-!
# The actual bounded automorphic quadratic-differential normed space

Decode the faithful weighted supremum representation by dividing by the
nonzero square-height weight on the lower half-plane and extending by zero
elsewhere. The inverse image of the actual source holomorphy and automorphy
submodule is then the literal bounded automorphic space with the inherited
weighted supremum norm. The canonical zero extension is explicit.

The automorphy convention is due to Wu Xiaobin's Li-Zhong-QC-formalization,
commit `1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

theorem norm_weight (z : Lower) : ‖weight z‖ = z.val.im ^ 2 := by
  rw [weight, Complex.norm_real, Real.norm_eq_abs, abs_sq]

/-- The actual function on the lower half-plane, with its canonical zero extension. -/
def decode (f : Target) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ LiZhongQC.lowerHalf then f ⟨z, hz⟩ / weight ⟨z, hz⟩ else 0

@[simp] theorem decode_coe (f : Target) (z : Lower) :
    decode f z = f z / weight z := by
  classical
  exact dite_eq_left z.property

@[simp] theorem decode_off (f : Target) {z : ℂ} (hz : z ∉ LiZhongQC.lowerHalf) :
    decode f z = 0 := by
  classical
  exact dite_eq_right hz

/-- Decode is a genuine complex-linear map; its zero extension is retained. -/
def decodeLinearMap : Target →ₗ[ℂ] (ℂ → ℂ) where
  toFun := decode
  map_add' f g := by
    funext z
    classical
    by_cases hz : z ∈ LiZhongQC.lowerHalf
    · simp only [decode, dite_eq_left hz, lp.coeFn_add, Pi.add_apply]
      exact add_div _ _ _
    · simp only [Pi.add_apply, decode_off _ hz, zero_add]
  map_smul' c f := by
    funext z
    classical
    by_cases hz : z ∈ LiZhongQC.lowerHalf
    · simp only [decode, dite_eq_left hz, lp.coeFn_smul, Pi.smul_apply,
        RingHom.id_apply, smul_eq_mul]
      exact mul_div_assoc _ _ _
    · simp only [Pi.smul_apply, smul_eq_mul, decode_off _ hz, mul_zero]

/-- Dividing by the strictly positive height weight loses no pointwise values. -/
theorem decode_injective : Function.Injective decode := by
  intro f g h
  apply lp.ext
  funext z
  have he := congrFun h (z : ℂ)
  rw [decode_coe, decode_coe] at he
  exact (div_left_inj' (weight_ne_zero z)).mp he

/-- The decoded function retains the literal weighted size at each actual point. -/
theorem norm_decode_mul_weight (f : Target) (z : Lower) :
    ‖decode f z‖ * z.val.im ^ 2 = ‖f z‖ := by
  rw [decode_coe, norm_div, norm_weight]
  exact div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_lt z.property))

/-- Every decoded bounded family satisfies the actual Bers weighted bound. -/
theorem decode_weightedBound (f : Target) :
    ∀ z ∈ LiZhongQC.lowerHalf, ‖decode f z‖ * z.im ^ 2 ≤ ‖f‖ := by
  intro z hz
  exact (norm_decode_mul_weight f ⟨z, hz⟩).trans_le
    (lp.norm_apply_le_norm ENNReal.top_ne_zero f ⟨z, hz⟩)

/-- The concrete actual bounded holomorphic automorphic quadratic differentials. -/
def automorphicSubmodule (Γ : Subgroup GammaMeasurableBeltrami.Deck) : Submodule ℂ Target :=
  (LiZhongQC.automorphicQD Γ).comap decodeLinearMap

abbrev Automorphic (Γ : Subgroup GammaMeasurableBeltrami.Deck) :=
  ↥(automorphicSubmodule Γ)

/-- The unchanged original automorphic function, including its canonical zero extension. -/
def Automorphic.toSource {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (φ : Automorphic Γ) : LiZhongQC.automorphicQD Γ :=
  ⟨decode φ.val, φ.property⟩

@[simp] theorem Automorphic.toSource_apply {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (φ : Automorphic Γ) (z : ℂ) : (φ.toSource : ℂ → ℂ) z = decode φ.val z := rfl

theorem Automorphic.toSource_injective {Γ : Subgroup GammaMeasurableBeltrami.Deck} :
    Function.Injective (Automorphic.toSource (Γ := Γ)) := by
  intro φ ψ h
  apply Subtype.ext
  apply decode_injective
  exact congrArg (fun q : LiZhongQC.automorphicQD Γ => (q : ℂ → ℂ)) h

/-- The norm is exactly the original square-height supremum of the original function. -/
theorem Automorphic.norm_eq_weightedSup {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (φ : Automorphic Γ) :
    ‖φ‖ = ⨆ z : Lower, ‖(φ.toSource : ℂ → ℂ) z‖ * z.val.im ^ 2 := by
  change ‖φ.val‖ = _
  rw [lp.norm_eq_ciSup]
  simp only [Automorphic.toSource_apply, norm_decode_mul_weight]

/-- Encoding and decoding preserve every actual canonically extended function. -/
theorem decode_encode (φ : ℂ → ℂ) (hφ)
    (hoff : ∀ z, z ∉ LiZhongQC.lowerHalf → φ z = 0) :
    decode (encode φ hφ) = φ := by
  funext z
  by_cases hz : z ∈ LiZhongQC.lowerHalf
  · rw [decode_coe _ (⟨z, hz⟩ : Lower), encode_apply]
    exact mul_div_cancel_right₀ _ (weight_ne_zero ⟨z, hz⟩)
  · rw [decode_off _ hz, hoff z hz]

/-- Every bounded actual automorphic function gives an element of the exact normed space. -/
def Automorphic.ofSource {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (φ : LiZhongQC.automorphicQD Γ)
    (hφ : ∃ C : ℝ, ∀ z ∈ LiZhongQC.lowerHalf, ‖(φ : ℂ → ℂ) z‖ * z.im ^ 2 ≤ C) :
    Automorphic Γ :=
  ⟨encode φ hφ, by
    change decode (encode φ hφ) ∈ LiZhongQC.automorphicQD Γ
    rw [decode_encode φ hφ φ.property.2.1]
    exact φ.property⟩

/-- The source function of this realization is exactly the given original function. -/
theorem Automorphic.toSource_ofSource {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (φ : LiZhongQC.automorphicQD Γ) (hφ) :
    (Automorphic.ofSource φ hφ).toSource = φ := by
  apply Subtype.ext
  exact decode_encode φ hφ φ.property.2.1

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
