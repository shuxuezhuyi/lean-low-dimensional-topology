module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicLength
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HalfPlaneUniformization
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalRegions
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

/-! Finite recovery of a GIVEN normalized peripheral pair. The actual period
consumer keeps D,A,(A*D)⁻¹ and the original covering projections. It does not
construct the arbitrary pants' normalization or assert pants equivalence. -/

public section
noncomputable section
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- Two signed traces recover the same normalized second generator in its attracting branch. -/
theorem normalizedPeripheralPair_eq_of_signed_traces
    (κ : ℝ) (hκ : 1 < κ) (D A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hD : D.val = !![κ⁻¹, 0; 0, κ])
    (hAr : A 0 0 + A 0 1 = A 1 0 + A 1 1)
    (hBr : B 0 0 + B 0 1 = B 1 0 + B 1 1)
    (hAa : 1 < A 1 0 + A 1 1) (hBa : 1 < B 1 0 + B 1 1)
    (ht : Matrix.trace A.val = Matrix.trace B.val)
    (hp : Matrix.trace (A * D).val = Matrix.trace (B * D).val) : A = B := by
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hκ).ne'
  have ht' : A 0 0 + A 1 1 = B 0 0 + B 1 1 := by
    simpa only [Matrix.trace_fin_two] using ht
  have hp' : A 0 0 * κ⁻¹ + A 1 1 * κ = B 0 0 * κ⁻¹ + B 1 1 * κ := by
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, hD] using hp
  field_simp [hκ0] at hp'
  have hd : A 1 1 = B 1 1 := by
    have hf : (A 1 1 - B 1 1) * (κ ^ 2 - 1) = 0 := by
      linear_combination hp' - ht'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (by nlinarith))
  have ha : A 0 0 = B 0 0 := by linarith
  have hdetA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.det_coe
  have hdetB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using B.det_coe
  have hpa : (A 1 0 + A 1 1) ^ 2 -
      (A 0 0 + A 1 1) * (A 1 0 + A 1 1) + 1 = 0 := by
    linear_combination -A 1 0 * hAr - hdetA
  have hpb : (B 1 0 + B 1 1) ^ 2 -
      (A 0 0 + A 1 1) * (B 1 0 + B 1 1) + 1 = 0 := by
    rw [ha, hd]
    linear_combination -B 1 0 * hBr - hdetB
  have hf : ((A 1 0 + A 1 1) - (B 1 0 + B 1 1)) *
      ((A 1 0 + A 1 1) * (B 1 0 + B 1 1) - 1) = 0 := by
    linear_combination (B 1 0 + B 1 1) * hpa - (A 1 0 + A 1 1) * hpb
  have hpos : 0 < (A 1 0 + A 1 1) * (B 1 0 + B 1 1) - 1 := by
    nlinarith [mul_pos (sub_pos.mpr hAa) (sub_pos.mpr hBa)]
  have he := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hpos.ne')
  have hc : A 1 0 = B 1 0 := by linarith
  have hb : A 0 1 = B 0 1 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- The finite normalized-pants calculation consumes the SAME three actual
full-period geodesics and the literal peripheral words. Normalized geometry
(row sums, attracting branch and signed traces) remains explicit. -/
theorem normalizedPeripheralPair_eq_of_original_period_lengths
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    (M : HyperbolicSurfaceModel R) (N : HyperbolicSurfaceModel S)
    (κ : ℝ) (hκ : 1 < κ) (D A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hD : D.val = !![κ⁻¹, 0; 0, κ])
    (hAr : A 0 0 + A 0 1 = A 1 0 + A 1 1)
    (hBr : B 0 0 + B 0 1 = B 1 0 + B 1 1)
    (hAa : 1 < A 1 0 + A 1 1) (hBa : 1 < B 1 0 + B 1 1)
    (hAt : 0 < Matrix.trace A.val) (hBt : 0 < Matrix.trace B.val)
    (hAp : Matrix.trace (A * D).val < 0) (hBp : Matrix.trace (B * D).val < 0)
    (q : Fin 3 → OriginalClosedGeodesic M) (r : Fin 3 → OriginalClosedGeodesic N)
    (hlen : ∀ i, (q i).length = (r i).length)
    (hAM : ∀ i z, M.halfPlaneCover ((![D, A, (A * D)⁻¹] i) • z) = M.halfPlaneCover z)
    (hBN : ∀ i z, N.halfPlaneCover ((![D, B, (B * D)⁻¹] i) • z) = N.halfPlaneCover z)
    (hAh : ∀ i, 4 < (Matrix.trace (![D, A, (A * D)⁻¹] i).val) ^ 2)
    (hBh : ∀ i, 4 < (Matrix.trace (![D, B, (B * D)⁻¹] i).val) ^ 2)
    (hAc : ∀ i, LiZhongQC.Covers M.halfPlaneCover (![D, A, (A * D)⁻¹] i) (q i).toLoop)
    (hBc : ∀ i, LiZhongQC.Covers N.halfPlaneCover (![D, B, (B * D)⁻¹] i) (r i).toLoop) : A = B := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨Δ, hΔ, hn⟩ := N.exists_halfPlaneCover_uniformization
  have hs (i : Fin 3) : (Matrix.trace (![D, A, (A * D)⁻¹] i).val) ^ 2 =
      (Matrix.trace (![D, B, (B * D)⁻¹] i).val) ^ 2 := by
    rw [(q i).trace_sq_eq_four_cosh_length_sq_of_covers hp _ ((hΓ _).2 (hAM i)) (hAh i) (hAc i),
      (r i).trace_sq_eq_four_cosh_length_sq_of_covers hn _ ((hΔ _).2 (hBN i)) (hBh i) (hBc i), hlen i]
  have ht : Matrix.trace A.val = Matrix.trace B.val :=
    (sq_eq_sq₀ hAt.le hBt.le).mp (by simpa using hs 1)
  have hp' : Matrix.trace (A * D).val = Matrix.trace (B * D).val := by
    have he : (-Matrix.trace (A * D).val) ^ 2 = (-Matrix.trace (B * D).val) ^ 2 := by
      have h2 := hs 2
      change (Matrix.trace ((A * D)⁻¹).val) ^ 2 =
        (Matrix.trace ((B * D)⁻¹).val) ^ 2 at h2
      simpa only [hSL_trace_inverse, neg_sq] using h2
    exact neg_injective ((sq_eq_sq₀ (neg_nonneg.mpr hAp.le) (neg_nonneg.mpr hBp.le)).mp he)
  exact normalizedPeripheralPair_eq_of_signed_traces κ hκ D A B hD hAr hBr hAa hBa ht hp'

end LowDimensionalTopology.Geometry.Surfaces
