module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergmanKernel
public import LowDimensionalTopology.Geometry.Teichmuller.GammaSourceCoefficient

/-!
# Actual Bers first variation in every bounded compatible direction

Every direction in the full measurable deck-compatible Banach space is scaled
by `1 / (1 + ‖μ‖)` into the actual source coefficient ball. The source's analytic
normalized-solution family and the chain rule then give the literal first
variation for the original direction. The resulting kernel is tested against
all original-atlas quadratic differentials.

The analytic scalar-variation theorem is due to Wu Xiaobin, from
Li-Zhong-QC-formalization, commit `1c0d5473c020b66ed5106331a38a61536760b9b2`
(Apache-2.0), `S36_Hamilton.lean`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergman

open Surfaces LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- The actual normalized Bers family has the stated first variation in every
bounded compatible direction, with no subunit restriction on that direction. -/
theorem bersFunction_directional
    (hΓ : IsFuchsian Γ) (μ : GammaMeasurableBeltrami.Space Γ)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    HasDerivAt (fun t : ℂ => bersFunction
      (fun w => t * GammaMeasurableBeltrami.planeRepresentative μ.val w) z)
      (bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z) 0 := by
  let κ := GammaMeasurableBeltrami.planeRepresentative μ.val
  let c : ℝ := (1 + ‖μ‖)⁻¹
  have hc : 0 < c := inv_pos.mpr (by positivity)
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsmall : ‖(c : ℂ)‖ * ‖μ‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    change (1 + ‖μ‖)⁻¹ * ‖μ‖ < 1
    rw [inv_mul_eq_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  let ν := GammaMeasurableBeltrami.sourceGammaOfScalar μ (c : ℂ) hsmall
  let νfun : ℂ → ℂ := fun w => (c : ℂ) * κ w
  have hd : HasDerivAt (fun t : ℂ => bersFunction (fun w => t * νfun w) z)
      (bersDerivative νfun z) 0 :=
    (bers_scalar_line_variation hΓ ν).2 ν z hz
  have hlinear : bersDerivative νfun z = (c : ℂ) * bersDerivative κ z := by
    unfold bersDerivative
    have he : (fun w => νfun w / (w - z) ^ 4) =
        fun w => (c : ℂ) * (κ w / (w - z) ^ 4) := by
      funext w
      dsimp only [νfun]
      ring
    rw [he, integral_const_mul]
    ring
  have hcomp := hd.comp_of_eq 0 ((hasDerivAt_id (0 : ℂ)).div_const (c : ℂ)) (by simp)
  change HasDerivAt (fun t : ℂ => bersFunction (fun w => (t / (c : ℂ)) * νfun w) z)
    (bersDerivative νfun z * (1 / (c : ℂ))) 0 at hcomp
  have he : (fun t : ℂ => bersFunction (fun w => (t / (c : ℂ)) * νfun w) z) =
      fun t : ℂ => bersFunction (fun w => t * κ w) z := by
    funext t
    apply congrArg (fun b : ℂ → ℂ => bersFunction b z)
    funext w
    dsimp only [νfun]
    field_simp [hc0]
  rw [he, hlinear] at hcomp
  have hcancel : ((c : ℂ) * bersDerivative κ z) * (1 / (c : ℂ)) =
      bersDerivative κ z := by field_simp [hc0]
  rw [hcancel] at hcomp
  exact hcomp

/-- The actual native Bers projection along the scalar line near the origin.
The value outside its coefficient ball is extended by zero. -/
def nativeBersLine (μ : GammaMeasurableBeltrami.Space Γ) (t : ℂ) : ℂ → ℂ := by
  classical
  exact if h : ‖t‖ * ‖μ‖ < 1 then
    GammaMeasurableBeltrami.bersProjection
      (⟨t • μ, by simpa only [Metric.mem_ball, dist_zero_right, norm_smul] using h⟩ :
        GammaMeasurableBeltrami.Ball Γ)
    else 0

/-- The first variation is that of the actual native Gamma-ball projection,
using its literal scalar coefficient throughout a neighborhood of the origin. -/
theorem nativeBersLine_directional
    (hΓ : IsFuchsian Γ) (μ : GammaMeasurableBeltrami.Space Γ)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    HasDerivAt (fun t : ℂ => nativeBersLine μ t z)
      (bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z) 0 := by
  classical
  apply (bersFunction_directional hΓ μ hz).congr_of_eventuallyEq
  have hnear : ∀ᶠ t : ℂ in 𝓝 0, ‖t‖ * ‖μ‖ < 1 :=
    (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).mem_nhds (by simp)
  filter_upwards [hnear] with t ht
  dsimp only [nativeBersLine]
  rw [dite_eq_left ht]
  exact congrFun (GammaMeasurableBeltrami.bersProjection_smul μ t ht) z

/-- Vanishing of the actual directional first variation is exactly annihilation
of every actual original-atlas quadratic differential by the literal integral. -/
theorem bersDirectional_iff_nativeQuadraticAnnihilator
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (p : ℍ → X) (hΓ : IsFuchsian Γ)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    (∀ z ∈ lowerHalf, deriv (fun t : ℂ => nativeBersLine μ t z) 0 = 0) ↔
      ∀ q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
        ∫ z in F, GammaMeasurableBeltrami.planeRepresentative μ.val z *
          uniformizedQuadratic R p q z = 0 := by
  constructor
  · intro hzero
    apply (bersKernel_iff_nativeQuadraticAnnihilator R p hΓ hp hF μ).mp
    intro z hz
    exact (nativeBersLine_directional hΓ μ hz).deriv.symm.trans (hzero z hz)
  · intro hnative z hz
    exact (nativeBersLine_directional hΓ μ hz).deriv.trans
      ((bersKernel_iff_nativeQuadraticAnnihilator R p hΓ hp hF μ).mpr hnative z hz)

end LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergman
