module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Tactic.Abel

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Metric Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- A real-linear differential on the plane is determined by its values on
the two real coordinate directions. -/
theorem realDifferential_eq_of_apply_one_I {A B : ℂ →L[ℝ] ℂ}
    (h1 : A 1 = B 1) (hI : A I = B I) : A = B := by
  ext z
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  calc
    A z = A (z.re • (1 : ℂ) + z.im • I) := congrArg A hz
    _ = z.re • A 1 + z.im • A I := by rw [A.map_add, A.map_smul, A.map_smul]
    _ = z.re • B 1 + z.im • B I := by rw [h1, hI]
    _ = B (z.re • (1 : ℂ) + z.im • I) := by rw [B.map_add, B.map_smul, B.map_smul]
    _ = B z := congrArg B hz.symm

/-- Actual real potentials with the same coordinate derivatives differ by a
constant on each connected open set. This is the rigidity required for the
local-potential germ covering, with no holomorphicity hypothesis. -/
theorem exists_eq_add_of_coordinate_derivatives_eq {U : Set ℂ} {F G : ℂ → ℂ}
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hF : DifferentiableOn ℝ F U) (hG : DifferentiableOn ℝ G U)
    (h1 : ∀ z ∈ U, fderiv ℝ F z 1 = fderiv ℝ G z 1)
    (hI : ∀ z ∈ U, fderiv ℝ F z I = fderiv ℝ G z I) :
    ∃ c : ℂ, EqOn F (fun z => G z + c) U :=
  hU.exists_eq_add_of_fderiv_eq hc hF hG fun z hz =>
    realDifferential_eq_of_apply_one_I (h1 z hz) (hI z hz)

/-- Pointwise equal coordinate derivatives imply locally constant differences
of actual potentials; no connectedness of the whole overlap is required. -/
theorem potential_difference_eventually_constant {U : Set ℂ} {F G : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℝ F U) (hG : DifferentiableOn ℝ G U)
    (h1 : ∀ z ∈ U, fderiv ℝ F z 1 = fderiv ℝ G z 1)
    (hI : ∀ z ∈ U, fderiv ℝ F z I = fderiv ℝ G z I)
    {x : ℂ} (hx : x ∈ U) :
    ∀ᶠ z in 𝓝 x, F z - G z = F x - G x := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  obtain ⟨c, hc⟩ := exists_eq_add_of_coordinate_derivatives_eq isOpen_ball
    (convex_ball x r).isPreconnected (hF.mono hball) (hG.mono hball)
    (fun z hz => h1 z (hball hz)) (fun z hz => hI z (hball hz))
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  rw [hc hz, hc (mem_ball_self hr)]
  simp only [add_sub_cancel_left]

end LowDimensionalTopology.Geometry.Quasiconformal
