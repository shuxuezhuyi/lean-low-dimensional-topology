module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NormalizedPantsPeripheralRigidity
public import Mathlib.Tactic.LinearCombination

/-! The first actual full period fixes the normalized first matrix too.
The following consumer keeps BOTH original projections and all three literal
words. No pants normalization, core identification or isometry is assumed here. -/

public section
noncomputable section
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The expanding diagonal parameter is fixed by the actual squared trace. -/
theorem normalizedFirstPeripheral_eq_of_trace_sq
    (κ τ : ℝ) (hκ : 1 < κ) (hτ : 1 < τ)
    (D E : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hD : D.val = !![κ⁻¹, 0; 0, κ]) (hE : E.val = !![τ⁻¹, 0; 0, τ])
    (hs : (Matrix.trace D.val) ^ 2 = (Matrix.trace E.val) ^ 2) :
    κ = τ ∧ D = E := by
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hκ).ne'
  have hτ0 : τ ≠ 0 := (zero_lt_one.trans hτ).ne'
  have ht : (κ⁻¹ + κ) ^ 2 = (τ⁻¹ + τ) ^ 2 := by
    simpa [hD, hE, Matrix.trace_fin_two] using hs
  have he : κ⁻¹ + κ = τ⁻¹ + τ :=
    (sq_eq_sq₀ (by positivity) (by positivity)).mp ht
  field_simp [hκ0, hτ0] at he
  have hf : (κ - τ) * (κ * τ - 1) = 0 := by
    linear_combination he
  have hpos : 0 < κ * τ - 1 := by
    nlinarith [mul_pos (sub_pos.mpr hκ) (sub_pos.mpr hτ)]
  have hκτ := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hpos.ne')
  refine ⟨hκτ, ?_⟩
  apply Subtype.ext
  rw [hD, hE, hκτ]

/-- Equality of SAME actual original full-period lengths recovers both given
normalized peripheral generators, without assuming their first matrices equal. -/
theorem normalizedPeripheralPair_eq_of_original_lengths
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    (M : HyperbolicSurfaceModel R) (N : HyperbolicSurfaceModel S)
    (κ τ : ℝ) (hκ : 1 < κ) (hτ : 1 < τ)
    (D E A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hD : D.val = !![κ⁻¹, 0; 0, κ]) (hE : E.val = !![τ⁻¹, 0; 0, τ])
    (hAr : A 0 0 + A 0 1 = A 1 0 + A 1 1)
    (hBr : B 0 0 + B 0 1 = B 1 0 + B 1 1)
    (hAa : 1 < A 1 0 + A 1 1) (hBa : 1 < B 1 0 + B 1 1)
    (hAt : 0 < Matrix.trace A.val) (hBt : 0 < Matrix.trace B.val)
    (hAp : Matrix.trace (A * D).val < 0) (hBp : Matrix.trace (B * E).val < 0)
    (q : Fin 3 → OriginalClosedGeodesic M) (r : Fin 3 → OriginalClosedGeodesic N)
    (hlen : ∀ i, (q i).length = (r i).length)
    (hAM : ∀ i z, M.halfPlaneCover ((![D, A, (A * D)⁻¹] i) • z) = M.halfPlaneCover z)
    (hBN : ∀ i z, N.halfPlaneCover ((![E, B, (B * E)⁻¹] i) • z) = N.halfPlaneCover z)
    (hAh : ∀ i, 4 < (Matrix.trace (![D, A, (A * D)⁻¹] i).val) ^ 2)
    (hBh : ∀ i, 4 < (Matrix.trace (![E, B, (B * E)⁻¹] i).val) ^ 2)
    (hAc : ∀ i, LiZhongQC.Covers M.halfPlaneCover (![D, A, (A * D)⁻¹] i) (q i).toLoop)
    (hBc : ∀ i, LiZhongQC.Covers N.halfPlaneCover (![E, B, (B * E)⁻¹] i) (r i).toLoop) :
    D = E ∧ A = B := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨Δ, hΔ, hn⟩ := N.exists_halfPlaneCover_uniformization
  have hs : (Matrix.trace D.val) ^ 2 = (Matrix.trace E.val) ^ 2 := by
    have hm := (q 0).trace_sq_eq_four_cosh_length_sq_of_covers hp D
      ((hΓ D).2 (by simpa using hAM 0))
      (by simpa using hAh 0) (by simpa using hAc 0)
    have hn' := (r 0).trace_sq_eq_four_cosh_length_sq_of_covers hn E
      ((hΔ E).2 (by simpa using hBN 0))
      (by simpa using hBh 0) (by simpa using hBc 0)
    rw [hm, hn', hlen 0]
  obtain ⟨_, hDE⟩ := normalizedFirstPeripheral_eq_of_trace_sq κ τ hκ hτ D E hD hE hs
  subst E
  refine ⟨rfl, ?_⟩
  exact normalizedPeripheralPair_eq_of_original_period_lengths M N κ hκ D A B hD
    hAr hBr hAa hBa hAt hBt hAp hBp q r hlen hAM hBN hAh hBh hAc hBc

end LowDimensionalTopology.Geometry.Surfaces
