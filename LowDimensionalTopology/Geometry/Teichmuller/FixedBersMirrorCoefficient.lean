module

public import LowDimensionalTopology.Geometry.Teichmuller.RawBersFixedReflection

/-!
# The literal compatible coefficient for the given mirror action

The supplied reflection and its actual action relation are retained. Equality
of the corresponding Möbius maps on the upper half-plane transports their
derivatives and Beltrami phase factors, without identifying matrix subgroups.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

/-- The supplied action relation gives the literal reflected Möbius map. -/
theorem fixedBersReflection_mobius_eq
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    {γ γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : ∀ τ, σ (γ • τ) = γ₀ • σ τ)
    {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    LiZhongQC.mobiusFn (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) (-conj z) =
      -conj (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) := by
  let τ : UpperHalfPlane := ⟨z, hz⟩
  have h := congrArg (fun w : UpperHalfPlane => (w : ℂ)) (hγ τ)
  rw [hσ, LiZhongQC.h23l_b_coe_smul, LiZhongQC.h23l_b_coe_smul, hσ] at h
  exact h.symm

/-- The same action relation conjugates the actual complex derivatives. -/
theorem fixedBersReflection_mobius_deriv
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    {γ γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : ∀ τ, σ (γ • τ) = γ₀ • σ τ)
    {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z =
      conj (deriv (LiZhongQC.mobiusFn (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1))
        (-conj z)) := by
  have heq : EqOn
      (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1))
      (fun w => -fixedBersReflectedPlaneFunction
        (LiZhongQC.mobiusFn (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1)) w)
      LiZhongQC.upperHalf := by
    intro w hw
    have h := congrArg (fun v : ℂ => -conj v)
      (fixedBersReflection_mobius_eq σ hσ hγ hw)
    simpa only [fixedBersReflectedPlaneFunction, map_neg, Complex.conj_conj, neg_neg]
      using h.symm
  have hd := (heq.eventuallyEq_of_mem (LiZhongQC.isOpen_upperHalf.mem_nhds hz)).deriv_eq
  rw [deriv.fun_neg, fixedBersReflectedPlaneFunction_deriv, neg_neg] at hd
  exact hd

/-- The actual matrix phase equals the conjugate-derivative ratio. -/
theorem fixedBersReflection_mobius_phase_deriv
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 /
      conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)) =
      conj (deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z) /
        deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z := by
  let D : ℂ := ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2
  have hd : deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z =
      1 / D :=
    (LiZhongQC.k24_d_deriv (LiZhongQC.h23l_b_det γ)
      (LiZhongQC.h23l_b_den_ne γ hz)).deriv
  have hdc : conj (deriv (LiZhongQC.mobiusFn
      (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z) = (conj D)⁻¹ := by
    rw [hd, one_div, map_inv₀]
  calc
    D / conj D = (conj D)⁻¹ / D⁻¹ := (inv_div_inv (conj D) D).symm
    _ = conj (deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z) /
        deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z := by
      rw [hdc, hd, one_div]

/-- The supplied mirror action gives exactly the required conjugate phase. -/
theorem fixedBersReflection_mobius_phase
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    {γ γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : ∀ τ, σ (γ • τ) = γ₀ • σ τ)
    {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 /
      conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)) =
      conj (((γ₀ 1 0 : ℂ) * (-conj z) + γ₀ 1 1) ^ 2 /
        conj (((γ₀ 1 0 : ℂ) * (-conj z) + γ₀ 1 1) ^ 2)) := by
  have hσz : -conj z ∈ LiZhongQC.upperHalf := by
    simpa only [LiZhongQC.upperHalf, mem_ofPred_eq, neg_im, conj_im, neg_neg] using hz
  rw [fixedBersReflection_mobius_phase_deriv γ hz,
    fixedBersReflection_mobius_phase_deriv γ₀ hσz,
    fixedBersReflection_mobius_deriv σ hσ hγ hz]
  simp only [map_div₀, Complex.conj_conj]

/-- The unchanged reflected raw coefficient is compatible with the given mirror group. -/
theorem fixedBersReflectionCoefficient_compatible
    {Γ Γσ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs : ∀ γ ∈ Γσ, ∃ γ₀ ∈ Γ, ∀ τ, σ (γ • τ) = γ₀ • σ τ)
    (μ : LiZhongQC.BeltramiGamma Γ) :
    LiZhongQC.IsGammaCompatible Γσ (fixedBersReflectionCoefficient μ.val).val := by
  intro γ hγ
  obtain ⟨γ₀, hγ₀, hrel⟩ := hs γ hγ
  have hμ := μ.property γ₀ hγ₀
  rw [ae_restrict_iff' LiZhongQC.isOpen_upperHalf.measurableSet] at hμ ⊢
  filter_upwards [fixedBersReflection_measurePreserving.quasiMeasurePreserving.ae hμ]
    with z hz hzu
  have hσz : -conj z ∈ LiZhongQC.upperHalf := by
    simpa only [LiZhongQC.upperHalf, mem_ofPred_eq, neg_im, conj_im, neg_neg] using hzu
  have h := congrArg conj (hz hσz)
  rw [map_mul] at h
  change conj (μ.val.val (-conj z)) =
    conj (μ.val.val (LiZhongQC.mobiusFn (γ₀ 0 0) (γ₀ 0 1)
      (γ₀ 1 0) (γ₀ 1 1) (-conj z))) *
    conj ((((γ₀ 1 0 : ℂ) * (-conj z) + γ₀ 1 1) ^ 2) /
      conj (((γ₀ 1 0 : ℂ) * (-conj z) + γ₀ 1 1) ^ 2)) at h
  rw [fixedBersReflection_mobius_eq σ hσ hrel hzu,
    ← fixedBersReflection_mobius_phase σ hσ hrel hzu] at h
  change conj (μ.val.val (-conj z)) =
    conj (μ.val.val (-conj (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1)
      (γ 1 0) (γ 1 1) z))) *
    (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2))
  exact h

/-- Reflect the same coefficient into its supplied compatible mirror group. -/
def fixedBersReflectionGamma
    {Γ Γσ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs : ∀ γ ∈ Γσ, ∃ γ₀ ∈ Γ, ∀ τ, σ (γ • τ) = γ₀ • σ τ)
    (μ : LiZhongQC.BeltramiGamma Γ) : LiZhongQC.BeltramiGamma Γσ :=
  ⟨fixedBersReflectionCoefficient μ.val,
    fixedBersReflectionCoefficient_compatible σ hσ hs μ⟩

/-- Every pointwise value is the required literal reflection of the old coefficient. -/
@[simp] theorem fixedBersReflectionGamma_apply
    {Γ Γσ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ))
    (hs : ∀ γ ∈ Γσ, ∃ γ₀ ∈ Γ, ∀ τ, σ (γ • τ) = γ₀ • σ τ)
    (μ : LiZhongQC.BeltramiGamma Γ) (z : ℂ) :
    (fixedBersReflectionGamma σ hσ hs μ).val.val z = conj (μ.val.val (-conj z)) := rfl

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
