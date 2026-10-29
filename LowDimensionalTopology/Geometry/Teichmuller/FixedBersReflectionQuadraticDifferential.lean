module

public import LowDimensionalTopology.Geometry.Teichmuller.FixedBersMirrorCoefficient
public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicTarget

/-!
# The literal reflection preserves actual automorphic quadratic differentials

The supplied actual upper-half-plane action relation is conjugated to the
lower half-plane. Its already proved derivative identity gives the genuine
fourth-power denominator law. No matrix-subgroup identification is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open LiZhongQC GammaMeasurableBeltrami

/-- The SAME actual action relation also gives the literal lower-plane formula. -/
theorem fixedBersReflection_mobius_eq_lower
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    {γ γ0 : Deck} (hγ : ∀ τ, σ (γ • τ) = γ0 • σ τ)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    mobiusFn (γ0 0 0) (γ0 0 1) (γ0 1 0) (γ0 1 1) (-conj z) =
      -conj (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) := by
  have hzu : conj z ∈ upperHalf := by
    change 0 < -z.im
    exact neg_pos.mpr hz
  have h := congrArg conj (fixedBersReflection_mobius_eq σ hσ hγ hzu)
  simpa only [mobiusFn, map_div₀, map_add, map_mul, Complex.conj_ofReal,
    map_neg, Complex.conj_conj] using h

/-- The actual derivatives force the fourth powers needed by the QD automorphy law. -/
theorem fixedBersReflection_mobius_denominator_fourth
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    {γ γ0 : Deck} (hγ : ∀ τ, σ (γ • τ) = γ0 • σ τ)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    (((γ0 1 0 : ℂ) * (-conj z) + γ0 1 1) ^ 4) =
      conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 4) := by
  have hzu : conj z ∈ upperHalf := by
    change 0 < -z.im
    exact neg_pos.mpr hz
  have hσu : -conj (conj z) ∈ upperHalf := by
    simpa only [upperHalf, mem_ofPred_eq, neg_im, conj_im, neg_neg] using hzu
  have hd := fixedBersReflection_mobius_deriv σ hσ hγ hzu
  rw [(k24_d_deriv (h23l_b_det γ) (h23l_b_den_ne γ hzu)).deriv,
    (k24_d_deriv (h23l_b_det γ0) (h23l_b_den_ne γ0 hσu)).deriv] at hd
  have hi := congrArg (fun w : ℂ => w⁻¹) hd
  simp only [one_div, map_inv₀, inv_inv] at hi
  have htwo : (((γ0 1 0 : ℂ) * (-conj z) + γ0 1 1) ^ 2) =
      conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) := by
    simpa only [map_pow, map_add, map_mul, Complex.conj_ofReal,
      map_neg, Complex.conj_conj] using hi.symm
  let d0 : ℂ := (γ0 1 0 : ℂ) * (-conj z) + γ0 1 1
  let d : ℂ := (γ 1 0 : ℂ) * z + γ 1 1
  change d0 ^ 2 = conj (d ^ 2) at htwo
  change d0 ^ 4 = conj (d ^ 4)
  calc
    d0 ^ 4 = (d0 ^ 2) ^ 2 := pow_mul d0 2 2
    _ = (conj (d ^ 2)) ^ 2 := congrArg (fun w : ℂ => w ^ 2) htwo
    _ = conj ((d ^ 2) ^ 2) := (map_pow conj (d ^ 2) 2).symm
    _ = conj (d ^ 4) := congrArg conj (pow_mul d 2 2).symm

/-- Literal double reflection has the required holomorphy, zero extension and weight law. -/
theorem fixedBersReflectedPlaneFunction_mem_automorphicQD
    {Γ Γσ : Subgroup Deck} (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs : ∀ γ ∈ Γσ, ∃ γ0 ∈ Γ, ∀ τ, σ (γ • τ) = γ0 • σ τ)
    (φ : automorphicQD Γ) :
    fixedBersReflectedPlaneFunction (φ : ℂ → ℂ) ∈ automorphicQD Γσ := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hσz : -conj z ∈ lowerHalf := by
      simpa only [lowerHalf, mem_ofPred_eq, neg_im, conj_im, neg_neg] using hz
    have hneg : DifferentiableAt ℂ (fun w : ℂ => (φ : ℂ → ℂ) (-w)) (conj z) :=
      (φ.property.1.differentiableAt (isOpen_lowerHalf.mem_nhds hσz)).comp
        (conj z) differentiableAt_id.neg
    change DifferentiableWithinAt ℂ
      (fun w : ℂ => conj ((φ : ℂ → ℂ) (-conj w))) lowerHalf z
    simpa only [Function.comp_def, Complex.conj_conj]
      using hneg.conj_conj.differentiableWithinAt
  · intro z hz
    have hσz : -conj z ∉ lowerHalf := by
      simpa only [lowerHalf, mem_ofPred_eq, neg_im, conj_im, neg_neg] using hz
    simp only [fixedBersReflectedPlaneFunction, φ.property.2.1 _ hσz, map_zero]
  · intro γ hγ z hz
    obtain ⟨γ0, hγ0, hrel⟩ := hs γ hγ
    have hσz : -conj z ∈ lowerHalf := by
      simpa only [lowerHalf, mem_ofPred_eq, neg_im, conj_im, neg_neg] using hz
    have h := congrArg conj (φ.property.2.2 γ0 hγ0 (-conj z) hσz)
    change conj ((φ : ℂ → ℂ)
        (mobiusFn (γ0 0 0) (γ0 0 1) (γ0 1 0) (γ0 1 1) (-conj z)) /
        (((γ0 1 0 : ℂ) * (-conj z) + γ0 1 1) ^ 4)) =
      conj ((φ : ℂ → ℂ) (-conj z)) at h
    rw [map_div₀, fixedBersReflection_mobius_denominator_fourth σ hσ hrel hz,
      Complex.conj_conj, fixedBersReflection_mobius_eq_lower σ hσ hrel hz] at h
    exact h

/-- The other supplied action relation gives the opposite direction under the SAME sigma. -/
theorem fixedBersReflection_reverse_action
    {Γ Γσ : Subgroup Deck} (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs : ∀ γ0 ∈ Γ, ∃ γ ∈ Γσ, ∀ τ, σ (γ • τ) = γ0 • σ τ) :
    ∀ γ0 ∈ Γ, ∃ γ ∈ Γσ, ∀ τ, σ (γ0 • τ) = γ • σ τ := by
  have hinv (τ : UpperHalfPlane) : σ (σ τ) = τ := by
    apply UpperHalfPlane.ext
    rw [hσ, hσ]
    simp only [map_neg, Complex.conj_conj, neg_neg]
  intro γ0 hγ0
  obtain ⟨γ, hγ, hrel⟩ := hs γ0 hγ0
  refine ⟨γ, hγ, fun τ => ?_⟩
  have h := congrArg σ (hrel (σ τ))
  simpa only [hinv] using h.symm

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
