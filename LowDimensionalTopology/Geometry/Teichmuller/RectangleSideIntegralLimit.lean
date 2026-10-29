module

public import LowDimensionalTopology.External.LiZhongQC.Ch07.S26_TeichmullerUniqueness
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Boundary integral limits on closed rectangles

Continuous data on a closed rectangle extend by coordinate clamping.
Dominated convergence then passes compact side integrals to the actual
boundary, retaining the original closed-rectangle domains.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology LiZhongQC

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- A continuous function on the actual closed rectangle extends
continuously by clamping the two real coordinates. This auxiliary map
does not extend the QC or ACL hypotheses beyond their original domain. -/
theorem rectangle_clamped_continuous_extension {g : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hg : ContinuousOn g (closure (rectangle r 1))) :
    ∃ G : ℂ → ℂ, Continuous G ∧ EqOn G g (closure (rectangle r 1)) := by
  let p : ℂ → ℂ := fun z =>
    ((max (0 : ℝ) (min r z.re) : ℝ) : ℂ) +
      ((max (0 : ℝ) (min 1 z.im) : ℝ) : ℂ) * I
  have hp : Continuous p := by
    dsimp [p]
    fun_prop
  have hpmem : ∀ z : ℂ, p z ∈ closure (rectangle r 1) := by
    intro z
    rw [mem_closure_rectangle_iff hr zero_lt_one]
    have hpre : (p z).re = max (0 : ℝ) (min r z.re) := by simp [p]
    have hpim : (p z).im = max (0 : ℝ) (min 1 z.im) := by simp [p]
    rw [hpre, hpim]
    exact ⟨le_max_left _ _, max_le hr.le (min_le_left _ _),
      le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hpid : ∀ z ∈ closure (rectangle r 1), p z = z := by
    intro z hz
    obtain ⟨hx0, hxr, hy0, hy1⟩ := (mem_closure_rectangle_iff hr zero_lt_one).mp hz
    dsimp [p]
    rw [min_eq_right hxr, max_eq_right hx0, min_eq_right hy1, max_eq_right hy0]
    exact Complex.re_add_im z
  refine ⟨g ∘ p, hg.comp_continuous hp hpmem, ?_⟩
  intro z hz
  change g (p z) = g z
  rw [hpid z hz]

/-- Existing one-dimensional parametric integration gives continuity
with both side endpoints varying. -/
theorem continuous_rectangle_vertical_intervalIntegral {G : ℂ → ℂ}
    (hG : Continuous G) {x a b : ℝ → ℝ}
    (hx : Continuous x) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun t : ℝ => ∫ y in a t..b t, G ((x t : ℂ) + (y : ℂ) * I)) := by
  have hf : Continuous (Function.uncurry
      (fun t y : ℝ => G ((x t : ℂ) + (y : ℂ) * I))) := by
    exact hG.comp (by fun_prop)
  have hu : Continuous (fun t : ℝ =>
      ∫ y in (0 : ℝ)..b t, G ((x t : ℂ) + (y : ℂ) * I)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf hb
  have hl : Continuous (fun t : ℝ =>
      ∫ y in (0 : ℝ)..a t, G ((x t : ℂ) + (y : ℂ) * I)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf ha
  apply (hu.sub hl).congr
  intro t
  have ht : Continuous (fun y : ℝ => G ((x t : ℂ) + (y : ℂ) * I)) :=
    hG.comp (by fun_prop)
  exact intervalIntegral.integral_interval_sub_left
    (ht.intervalIntegrable 0 (b t)) (ht.intervalIntegrable 0 (a t))

/-- The vertical side difference for the interior rectangle
`[t,r-t] × [t,1-t]` tends to the actual closed-side difference.
The preceding clamping lemma allows this to be used for the descended
closed extension, without demanding global continuity of the QC map. -/
theorem rectangle_vertical_side_integrals_tendsto {G : ℂ → ℂ}
    (hG : Continuous G) (r : ℝ) :
    Tendsto (fun t : ℝ =>
      (∫ y in t..(1 - t), G (((r - t : ℝ) : ℂ) + (y : ℂ) * I)) -
      (∫ y in t..(1 - t), G ((t : ℂ) + (y : ℂ) * I)))
      (𝓝 0)
      (𝓝 ((∫ y in (0 : ℝ)..1, G ((r : ℂ) + (y : ℂ) * I)) -
        (∫ y in (0 : ℝ)..1, G ((y : ℂ) * I)))) := by
  have hright := continuous_rectangle_vertical_intervalIntegral hG
    (show Continuous (fun t : ℝ => r - t) by fun_prop)
    continuous_id (show Continuous (fun t : ℝ => 1 - t) by fun_prop)
  have hleft := continuous_rectangle_vertical_intervalIntegral hG
    continuous_id continuous_id (show Continuous (fun t : ℝ => 1 - t) by fun_prop)
  simpa only [Pi.sub_def, id_eq, sub_zero, Complex.ofReal_zero, zero_add] using
    (hright.sub hleft).tendsto (0 : ℝ)

end LowDimensionalTopology.Geometry.Teichmuller
