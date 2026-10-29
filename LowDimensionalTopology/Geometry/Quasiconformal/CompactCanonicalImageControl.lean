module

public import LowDimensionalTopology.External.LiZhongQC.LiZhongExternal.Topology.BrouwerClosedBall
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Actual disc inclusions for a plane homeomorphism close to the identity

The inverse-image inclusion follows from the existing Brouwer theorem on
the closed unit ball. Its fixed point lies strictly inside the radius-three
ball because the prescribed image has norm less than two and the error is
strictly less than one. No image-containment premise is supplied.

The imported Brouwer proof is by harfe, MIT-licensed, fixed upstream commit
`770940ddf9878cf61952ed53d910b92bca841838`; its license and source attribution
are retained in the existing External directory and THIRD_PARTY_NOTICES.md.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Metric

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Uniform error less than one on the closed radius-three disc forces the
entire radius-two disc into the image of the open radius-three disc. -/
theorem homeomorph_ball_two_subset_image_ball_three (G : ℂ ≃ₜ ℂ)
    (hclose : ∀ x ∈ closedBall (0 : ℂ) 3, ‖G x - x‖ < 1) :
    ball (0 : ℂ) 2 ⊆ G '' ball (0 : ℂ) 3 := by
  intro y hy
  have hy2 : ‖y‖ < 2 := mem_ball_zero_iff.mp hy
  have hscale (x : closedBall (0 : ℂ) 1) :
      (3 : ℂ) * (x : ℂ) ∈ closedBall (0 : ℂ) 3 := by
    rw [mem_closedBall_zero_iff]
    calc
      ‖(3 : ℂ) * (x : ℂ)‖ = 3 * ‖(x : ℂ)‖ := by
        rw [norm_mul]
        norm_num
      _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left
        (mem_closedBall_zero_iff.mp x.property) (by norm_num)
      _ = 3 := by norm_num
  let f : closedBall (0 : ℂ) 1 → closedBall (0 : ℂ) 1 := fun x =>
    ⟨(y - (G ((3 : ℂ) * (x : ℂ)) - (3 : ℂ) * (x : ℂ))) / (3 : ℂ), by
      rw [mem_closedBall_zero_iff, norm_div]
      have he := hclose _ (hscale x)
      have hn := norm_sub_le y (G ((3 : ℂ) * (x : ℂ)) - (3 : ℂ) * (x : ℂ))
      have hnorm3 : ‖(3 : ℂ)‖ = 3 := by norm_num
      rw [hnorm3]
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
      linarith⟩
  have hf : Continuous f := by
    exact ((continuous_const.sub
      ((G.continuous.comp (continuous_const.mul continuous_subtype_val)).sub
        (continuous_const.mul continuous_subtype_val))).div_const (3 : ℂ)).subtype_mk _
  obtain ⟨x, hx⟩ := LiZhongExternal.Topology.brouwer_closedBall f hf
  have hfix :
      (y - (G ((3 : ℂ) * (x : ℂ)) - (3 : ℂ) * (x : ℂ))) / (3 : ℂ) = (x : ℂ) :=
    congrArg Subtype.val hx
  have hGy : G ((3 : ℂ) * (x : ℂ)) = y := by
    have h := (div_eq_iff (by norm_num : (3 : ℂ) ≠ 0)).mp hfix
    linear_combination -h
  refine ⟨(3 : ℂ) * (x : ℂ), ?_, hGy⟩
  rw [mem_ball_zero_iff]
  have he := hclose _ (hscale x)
  have hn := norm_sub_le y (G ((3 : ℂ) * (x : ℂ)) - (3 : ℂ) * (x : ℂ))
  have hid : y - (G ((3 : ℂ) * (x : ℂ)) - (3 : ℂ) * (x : ℂ)) =
      (3 : ℂ) * (x : ℂ) := by
    rw [hGy]
    ring
  rw [hid] at hn
  linarith

/-- The same actual error bound sends the open unit disc into the radius-two disc. -/
theorem homeomorph_image_ball_one_subset_ball_two (G : ℂ ≃ₜ ℂ)
    (hclose : ∀ x ∈ closedBall (0 : ℂ) 3, ‖G x - x‖ < 1) :
    G '' ball (0 : ℂ) 1 ⊆ ball (0 : ℂ) 2 := by
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  have hx3 : x ∈ closedBall (0 : ℂ) 3 := by
    rw [mem_closedBall_zero_iff]
    linarith
  have he := hclose x hx3
  have hn := norm_add_le (G x - x) x
  rw [sub_add_cancel] at hn
  rw [mem_ball_zero_iff]
  linarith

/-- The genuine inverse of the given homeomorphism sends every radius-two
point into the open radius-three disc. -/
theorem homeomorph_symm_mapsTo_ball_two_ball_three (G : ℂ ≃ₜ ℂ)
    (hclose : ∀ x ∈ closedBall (0 : ℂ) 3, ‖G x - x‖ < 1) :
    MapsTo G.symm (ball (0 : ℂ) 2) (ball (0 : ℂ) 3) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := homeomorph_ball_two_subset_image_ball_three G hclose hy
  rw [← hxy, G.symm_apply_apply]
  exact hx

end LowDimensionalTopology.Geometry.Quasiconformal
