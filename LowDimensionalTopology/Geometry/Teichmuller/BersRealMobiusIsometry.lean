module

public import LowDimensionalTopology.Geometry.Teichmuller.BersWeightedCoordinates
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# The literal real Möbius change of coordinates is a weighted Bers isometry

The group is the existing actual matrix conjugate `M Γ M⁻¹`. Pullback of
quadratic differentials is the literal fourth-power formula, including the
canonical zero extension. Its complex linearity, genuine automorphy and
inverse are proved, and the height transformation gives equality of the
original weighted supremum norms on every vector.

The automorphic-function convention uses Wu Xiaobin's Li-Zhong-QC-formalization,
commit `1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0).
See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open GammaMeasurableBeltrami

/-- The actual fourth-power denominator of a real unimodular fractional map. -/
def realMobiusDenom (M : Deck) (z : ℂ) : ℂ := (M 1 0 : ℂ) * z + M 1 1

/-- Literal pullback of the coefficient of a quadratic differential. -/
def realMobiusPullback (M : Deck) (φ : ℂ → ℂ) : ℂ → ℂ :=
  LiZhongQC.lowerHalf.indicator
    (fun z => φ (LiZhongQC.utm_b_mob M z) / realMobiusDenom M z ^ 4)

theorem realMobiusPullback_apply (M : Deck) (φ : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ LiZhongQC.lowerHalf) :
    realMobiusPullback M φ z = φ (LiZhongQC.utm_b_mob M z) / realMobiusDenom M z ^ 4 :=
  indicator_of_mem hz _

theorem realMobiusPullback_off (M : Deck) (φ : ℂ → ℂ) {z : ℂ}
    (hz : z ∉ LiZhongQC.lowerHalf) : realMobiusPullback M φ z = 0 :=
  indicator_of_notMem hz _

private theorem realMobius_comp (A B : Deck) {z : ℂ} (hz : z ∈ LiZhongQC.lowerHalf) :
    LiZhongQC.utm_b_mob (A * B) z =
      LiZhongQC.utm_b_mob A (LiZhongQC.utm_b_mob B z) := by
  have hzu : 0 < (conj z).im := by
    rw [Complex.conj_im]
    exact neg_pos.mpr hz
  have hu : LiZhongQC.utm_b_mob (A * B) (conj z) =
      LiZhongQC.utm_b_mob A (LiZhongQC.utm_b_mob B (conj z)) := by
    rw [LiZhongQC.utm_b_mob_smul (A * B) hzu,
      LiZhongQC.utm_b_mob_smul B hzu, LiZhongQC.utm_b_mob_coe, mul_smul]
  have h := congrArg conj hu
  simpa only [LiZhongQC.s33dim_conj_mob, Complex.conj_conj] using h

private theorem realMobiusDenom_comp (A B : Deck) {z : ℂ} (hz : z ∈ LiZhongQC.lowerHalf) :
    realMobiusDenom (A * B) z =
      realMobiusDenom A (LiZhongQC.utm_b_mob B z) * realMobiusDenom B z := by
  have h := UpperHalfPlane.denom_cocycle
    (Matrix.SpecialLinearGroup.mapGL ℝ A) (Matrix.SpecialLinearGroup.mapGL ℝ B)
    (show z.im ≠ 0 from ne_of_lt hz)
  change realMobiusDenom (A * B) z =
    realMobiusDenom A (LiZhongQC.utm_b_mob B z) * realMobiusDenom B z at h
  exact h

/-- The genuine pullbacks compose in the contravariant order. -/
theorem realMobiusPullback_comp (A B : Deck) (φ : ℂ → ℂ) :
    realMobiusPullback A (realMobiusPullback B φ) = realMobiusPullback (B * A) φ := by
  funext z
  by_cases hz : z ∈ LiZhongQC.lowerHalf
  · have hAz : LiZhongQC.utm_b_mob A z ∈ LiZhongQC.lowerHalf := LiZhongQC.bg2_a_mem A hz
    rw [realMobiusPullback_apply A _ hz, realMobiusPullback_apply B _ hAz,
      realMobiusPullback_apply (B * A) _ hz, realMobius_comp B A hz,
      realMobiusDenom_comp B A hz, mul_pow, div_div]
  · rw [realMobiusPullback_off A _ hz, realMobiusPullback_off (B * A) _ hz]

private theorem realMobiusPullback_one (φ : ℂ → ℂ)
    (hoff : ∀ z, z ∉ LiZhongQC.lowerHalf → φ z = 0) : realMobiusPullback 1 φ = φ := by
  funext z
  by_cases hz : z ∈ LiZhongQC.lowerHalf
  · simp [realMobiusPullback_apply _ _ hz, LiZhongQC.utm_b_mob, realMobiusDenom]
  · rw [realMobiusPullback_off _ _ hz, hoff z hz]

/-- Pullback by the actual inverse matrix recovers every canonically extended function. -/
theorem realMobiusPullback_inv (M : Deck) (φ : ℂ → ℂ)
    (hoff : ∀ z, z ∉ LiZhongQC.lowerHalf → φ z = 0) :
    realMobiusPullback M⁻¹ (realMobiusPullback M φ) = φ := by
  rw [realMobiusPullback_comp, mul_inv_cancel, realMobiusPullback_one φ hoff]

private theorem realMobiusPullback_eq_self {Γ : Subgroup Deck}
    (φ : LiZhongQC.automorphicQD Γ) {M : Deck} (hM : M ∈ Γ) :
    realMobiusPullback M (φ : ℂ → ℂ) = (φ : ℂ → ℂ) := by
  funext z
  by_cases hz : z ∈ LiZhongQC.lowerHalf
  · rw [realMobiusPullback_apply _ _ hz]
    exact φ.property.2.2 M hM z hz
  · rw [realMobiusPullback_off _ _ hz, φ.property.2.1 z hz]

/-- Every genuine automorphic differential transforms to the exact conjugate source group. -/
theorem realMobiusPullback_mem (Γ : Subgroup Deck) (M : Deck)
    (φ : LiZhongQC.automorphicQD (LiZhongQC.conjGroup Γ M)) :
    realMobiusPullback M (φ : ℂ → ℂ) ∈ LiZhongQC.automorphicQD Γ := by
  refine ⟨?_, fun z hz => realMobiusPullback_off M _ hz, ?_⟩
  · have hm : DifferentiableOn ℂ (LiZhongQC.utm_b_mob M) LiZhongQC.lowerHalf := by
      intro z hz
      exact (LiZhongQC.utm_b_hasDerivAt_mob M (LiZhongQC.bg2_a_den_ne M hz)).differentiableAt.differentiableWithinAt
    have hd : DifferentiableOn ℂ (fun z : ℂ => realMobiusDenom M z ^ 4) LiZhongQC.lowerHalf := by
      unfold realMobiusDenom
      fun_prop
    have h := (φ.property.1.comp hm (fun z hz => LiZhongQC.bg2_a_mem M hz)).div hd
      (fun z hz => pow_ne_zero 4 (LiZhongQC.bg2_a_den_ne M hz))
    exact h.congr fun z hz => realMobiusPullback_apply M _ hz
  · intro γ hγ z hz
    let δ : Deck := M * γ * M⁻¹
    have hδ : δ ∈ LiZhongQC.conjGroup Γ M := by
      apply Subgroup.mem_map.mpr
      exact ⟨γ, hγ, rfl⟩
    have hfix := realMobiusPullback_eq_self φ hδ
    calc
      _ = realMobiusPullback γ (realMobiusPullback M (φ : ℂ → ℂ)) z :=
        (realMobiusPullback_apply γ _ hz).symm
      _ = realMobiusPullback (M * γ) (φ : ℂ → ℂ) z :=
        congrFun (realMobiusPullback_comp γ M _) z
      _ = realMobiusPullback (δ * M) (φ : ℂ → ℂ) z := by simp [δ, mul_assoc]
      _ = realMobiusPullback M (realMobiusPullback δ (φ : ℂ → ℂ)) z :=
        congrFun (realMobiusPullback_comp M δ _).symm z
      _ = realMobiusPullback M (φ : ℂ → ℂ) z := by rw [hfix]

private theorem conjugateGroup_inverse (Γ : Subgroup Deck) (M : Deck) :
    LiZhongQC.conjGroup (LiZhongQC.conjGroup Γ M) M⁻¹ = Γ := by
  ext γ
  constructor
  · intro hγ
    obtain ⟨δ, hδ, hδγ⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨η, hη, hηδ⟩ := Subgroup.mem_map.mp hδ
    have he : γ = η := by
      rw [← hδγ, ← hηδ]
      simp [MulAut.conj_apply, mul_assoc]
    rwa [he]
  · intro hγ
    apply Subgroup.mem_map.mpr
    refine ⟨M * γ * M⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩
    · simp [mul_assoc]

/-- At every actual point the fourth-power derivative cancels precisely the height weight. -/
theorem realMobiusPullback_weighted_norm (M : Deck) (φ : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ LiZhongQC.lowerHalf) :
    ‖realMobiusPullback M φ z‖ * z.im ^ 2 =
      ‖φ (LiZhongQC.utm_b_mob M z)‖ * (LiZhongQC.utm_b_mob M z).im ^ 2 := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe M
    rwa [Matrix.det_fin_two] at h
  have him : (LiZhongQC.utm_b_mob M z).im = z.im / Complex.normSq (realMobiusDenom M z) :=
    LiZhongQC.utm_im_mobius hdet z
  have hd : realMobiusDenom M z ≠ 0 := LiZhongQC.bg2_a_den_ne M hz
  rw [realMobiusPullback_apply M φ hz, him, norm_div, norm_pow, div_pow,
    Complex.normSq_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr hd]

/-- The same bound holds in the unchanged actual weighted norm. -/
theorem realMobiusPullback_bound (Γ : Subgroup Deck) (M : Deck)
    (φ : Automorphic (LiZhongQC.conjGroup Γ M)) :
    ∀ z ∈ LiZhongQC.lowerHalf,
      ‖realMobiusPullback M (φ.toSource : ℂ → ℂ) z‖ * z.im ^ 2 ≤ ‖φ‖ := by
  intro z hz
  rw [realMobiusPullback_weighted_norm M _ hz]
  exact decode_weightedBound φ.val (LiZhongQC.utm_b_mob M z) (LiZhongQC.bg2_a_mem M hz)

/-- The literal native weighted pullback on every automorphic vector. -/
def realMobiusPullbackNative (Γ : Subgroup Deck) (M : Deck)
    (φ : Automorphic (LiZhongQC.conjGroup Γ M)) : Automorphic Γ :=
  Automorphic.ofSource ⟨realMobiusPullback M (φ.toSource : ℂ → ℂ),
    realMobiusPullback_mem Γ M φ.toSource⟩ ⟨‖φ‖, realMobiusPullback_bound Γ M φ⟩

@[simp] theorem realMobiusPullbackNative_toSource (Γ : Subgroup Deck) (M : Deck)
    (φ : Automorphic (LiZhongQC.conjGroup Γ M)) :
    ((realMobiusPullbackNative Γ M φ).toSource : ℂ → ℂ) =
      realMobiusPullback M (φ.toSource : ℂ → ℂ) := by
  exact congrArg (fun q : LiZhongQC.automorphicQD Γ => (q : ℂ → ℂ))
    (Automorphic.toSource_ofSource _ _)

private theorem realMobiusPullback_add (M : Deck) (φ ψ : ℂ → ℂ) :
    realMobiusPullback M (φ + ψ) = realMobiusPullback M φ + realMobiusPullback M ψ := by
  funext z
  by_cases hz : z ∈ LiZhongQC.lowerHalf
  · simp only [realMobiusPullback_apply _ _ hz, Pi.add_apply, add_div]
  · simp only [realMobiusPullback_off _ _ hz, Pi.add_apply, zero_add]

private theorem realMobiusPullback_smul (M : Deck) (a : ℂ) (φ : ℂ → ℂ) :
    realMobiusPullback M (a • φ) = a • realMobiusPullback M φ := by
  funext z
  by_cases hz : z ∈ LiZhongQC.lowerHalf
  · simp only [realMobiusPullback_apply _ _ hz, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [realMobiusPullback_off _ _ hz, Pi.smul_apply, smul_eq_mul, mul_zero]

private theorem toSource_add_function {Γ : Subgroup Deck} (φ ψ : Automorphic Γ) :
    ((φ + ψ).toSource : ℂ → ℂ) = (φ.toSource : ℂ → ℂ) + (ψ.toSource : ℂ → ℂ) :=
  congrArg (fun q : LiZhongQC.automorphicQD Γ => (q : ℂ → ℂ))
    (map_add (toSourceLinear Γ) φ ψ)

private theorem toSource_smul_function {Γ : Subgroup Deck} (a : ℂ) (φ : Automorphic Γ) :
    ((a • φ).toSource : ℂ → ℂ) = a • (φ.toSource : ℂ → ℂ) :=
  congrArg (fun q : LiZhongQC.automorphicQD Γ => (q : ℂ → ℂ))
    (map_smul (toSourceLinear Γ) a φ)

/-- Pullback is complex linear on the actual native weighted function spaces. -/
def realMobiusPullbackLinear (Γ : Subgroup Deck) (M : Deck) :
    Automorphic (LiZhongQC.conjGroup Γ M) →ₗ[ℂ] Automorphic Γ where
  toFun := realMobiusPullbackNative Γ M
  map_add' φ ψ := by
    apply Automorphic.toSource_injective
    apply Subtype.ext
    rw [realMobiusPullbackNative_toSource, toSource_add_function, realMobiusPullback_add,
      toSource_add_function, realMobiusPullbackNative_toSource, realMobiusPullbackNative_toSource]
  map_smul' a φ := by
    change realMobiusPullbackNative Γ M (a • φ) = a • realMobiusPullbackNative Γ M φ
    apply Automorphic.toSource_injective
    apply Subtype.ext
    rw [realMobiusPullbackNative_toSource, toSource_smul_function, realMobiusPullback_smul,
      toSource_smul_function, realMobiusPullbackNative_toSource]

private theorem norm_realMobiusPullbackNative_le (Γ : Subgroup Deck) (M : Deck)
    (φ : Automorphic (LiZhongQC.conjGroup Γ M)) : ‖realMobiusPullbackNative Γ M φ‖ ≤ ‖φ‖ := by
  change ‖(realMobiusPullbackNative Γ M φ).val‖ ≤ ‖φ‖
  apply lp.norm_le_of_forall_le (norm_nonneg φ)
  intro z
  rw [← norm_decode_mul_weight]
  change ‖((realMobiusPullbackNative Γ M φ).toSource : ℂ → ℂ) z‖ * z.val.im ^ 2 ≤ ‖φ‖
  rw [realMobiusPullbackNative_toSource]
  exact realMobiusPullback_bound Γ M φ z z.property

/-- The real coordinate change preserves the complete original weighted supremum norm. -/
theorem norm_realMobiusPullbackNative (Γ : Subgroup Deck) (M : Deck)
    (φ : Automorphic (LiZhongQC.conjGroup Γ M)) : ‖realMobiusPullbackNative Γ M φ‖ = ‖φ‖ := by
  apply le_antisymm (norm_realMobiusPullbackNative_le Γ M φ)
  change ‖φ.val‖ ≤ ‖realMobiusPullbackNative Γ M φ‖
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro z
  rw [← norm_decode_mul_weight]
  have he := realMobiusPullback_weighted_norm M⁻¹
    (realMobiusPullback M (φ.toSource : ℂ → ℂ)) z.property
  have hinv := congrFun (realMobiusPullback_inv M (φ.toSource : ℂ → ℂ)
    φ.toSource.property.2.1) z
  rw [hinv] at he
  change ‖(φ.toSource : ℂ → ℂ) z‖ * z.val.im ^ 2 ≤ _
  rw [he, ← realMobiusPullbackNative_toSource Γ M φ]
  exact decode_weightedBound (realMobiusPullbackNative Γ M φ).val _
    (LiZhongQC.bg2_a_mem M⁻¹ z.property)

theorem realMobiusPullbackNative_injective (Γ : Subgroup Deck) (M : Deck) :
    Function.Injective (realMobiusPullbackNative Γ M) := by
  intro φ ψ he
  apply Automorphic.toSource_injective
  apply Subtype.ext
  have h := congrArg (fun q : Automorphic Γ => (q.toSource : ℂ → ℂ)) he
  rw [realMobiusPullbackNative_toSource, realMobiusPullbackNative_toSource] at h
  have hi := congrArg (realMobiusPullback M⁻¹) h
  rw [realMobiusPullback_inv M _ φ.toSource.property.2.1,
    realMobiusPullback_inv M _ ψ.toSource.property.2.1] at hi
  exact hi

theorem realMobiusPullbackNative_surjective (Γ : Subgroup Deck) (M : Deck) :
    Function.Surjective (realMobiusPullbackNative Γ M) := by
  intro ψ
  let q : LiZhongQC.automorphicQD (LiZhongQC.conjGroup (LiZhongQC.conjGroup Γ M) M⁻¹) :=
    ⟨(ψ.toSource : ℂ → ℂ), by rw [conjugateGroup_inverse]; exact ψ.toSource.property⟩
  have hb : ∀ z ∈ LiZhongQC.lowerHalf,
      ‖realMobiusPullback M⁻¹ (ψ.toSource : ℂ → ℂ) z‖ * z.im ^ 2 ≤ ‖ψ‖ := by
    intro z hz
    rw [realMobiusPullback_weighted_norm M⁻¹ _ hz]
    exact decode_weightedBound ψ.val _ (LiZhongQC.bg2_a_mem M⁻¹ hz)
  let φ : Automorphic (LiZhongQC.conjGroup Γ M) :=
    Automorphic.ofSource ⟨realMobiusPullback M⁻¹ (ψ.toSource : ℂ → ℂ),
      realMobiusPullback_mem (LiZhongQC.conjGroup Γ M) M⁻¹ q⟩ ⟨‖ψ‖, hb⟩
  refine ⟨φ, ?_⟩
  apply Automorphic.toSource_injective
  apply Subtype.ext
  have hφ : (φ.toSource : ℂ → ℂ) = realMobiusPullback M⁻¹ (ψ.toSource : ℂ → ℂ) :=
    congrArg (fun q : LiZhongQC.automorphicQD (LiZhongQC.conjGroup Γ M) => (q : ℂ → ℂ))
      (Automorphic.toSource_ofSource _ _)
  rw [realMobiusPullbackNative_toSource, hφ]
  simpa only [inv_inv] using realMobiusPullback_inv M⁻¹ (ψ.toSource : ℂ → ℂ)
    ψ.toSource.property.2.1

/-- The genuine complex-linear isometry for the actual real Möbius conjugate group. -/
def automorphicRealMobiusIsometry (Γ : Subgroup Deck) (M : Deck) :
    Automorphic (LiZhongQC.conjGroup Γ M) ≃ₗᵢ[ℂ] Automorphic Γ where
  toLinearEquiv := LinearEquiv.ofBijective (realMobiusPullbackLinear Γ M)
    ⟨realMobiusPullbackNative_injective Γ M, realMobiusPullbackNative_surjective Γ M⟩
  norm_map' := norm_realMobiusPullbackNative Γ M

/-- The isometry retains every literal value of the original differential. -/
theorem automorphicRealMobiusIsometry_toSource (Γ : Subgroup Deck) (M : Deck)
    (φ : Automorphic (LiZhongQC.conjGroup Γ M)) :
    ((automorphicRealMobiusIsometry Γ M φ).toSource : ℂ → ℂ) =
      realMobiusPullback M (φ.toSource : ℂ → ℂ) :=
  realMobiusPullbackNative_toSource Γ M φ

/-- Its inverse is exactly pullback by the actual inverse matrix. -/
theorem automorphicRealMobiusIsometry_symm_toSource (Γ : Subgroup Deck) (M : Deck)
    (ψ : Automorphic Γ) :
    (((automorphicRealMobiusIsometry Γ M).symm ψ).toSource : ℂ → ℂ) =
      realMobiusPullback M⁻¹ (ψ.toSource : ℂ → ℂ) := by
  have h := congrArg (fun q : Automorphic Γ => (q.toSource : ℂ → ℂ))
    ((automorphicRealMobiusIsometry Γ M).apply_symm_apply ψ)
  rw [automorphicRealMobiusIsometry_toSource] at h
  have hi := congrArg (realMobiusPullback M⁻¹) h
  rw [realMobiusPullback_inv M _
    ((automorphicRealMobiusIsometry Γ M).symm ψ).toSource.property.2.1] at hi
  exact hi

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
