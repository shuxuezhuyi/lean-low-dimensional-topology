/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicAxes
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# The quadratic seed attached to an actual hyperbolic geodesic

The coefficient is determined by the two actual ideal endpoints, including
infinity. The final consumer uses the actual axis of the same real Mobius map.
-/

@[expose] public section

noncomputable section

open Set
open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries

open LowDimensionalTopology.Geometry.Hyperbolic

/-- The rational quadratic coefficient for two ideal endpoints. -/
def endpointSeed : OnePoint ℂ → OnePoint ℂ → ℂ → ℂ
  | ∞, ∞, _ => 0
  | ∞, OnePoint.some b, z => 1 / (z - b) ^ 2
  | OnePoint.some a, ∞, z => 1 / (z - a) ^ 2
  | OnePoint.some a, OnePoint.some b, z =>
      (a - b) ^ 2 / ((z - a) ^ 2 * (z - b) ^ 2)

@[simp] theorem endpointSeed_finite (a b z : ℂ) :
    endpointSeed a b z = (a - b) ^ 2 / ((z - a) ^ 2 * (z - b) ^ 2) := rfl

@[simp] theorem endpointSeed_infty (a z : ℂ) :
    endpointSeed a ∞ z = 1 / (z - a) ^ 2 := rfl

theorem endpointSeed_symm (a b : OnePoint ℂ) : endpointSeed a b = endpointSeed b a := by
  funext z
  cases a using OnePoint.rec <;> cases b using OnePoint.rec <;>
    simp [endpointSeed, sub_sq_comm, mul_comm]

theorem endpointSeed_eq_of_pair_eq {a b c d : OnePoint ℂ}
    (h : ({a, b} : Set (OnePoint ℂ)) = {c, d}) : endpointSeed a b = endpointSeed c d := by
  rcases Set.pair_eq_pair_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact endpointSeed_symm _ _

theorem endpointSeed_differentiableOn {a b : OnePoint ℂ}
    (ha : a ∈ halfPlaneIdealBoundary) (hb : b ∈ halfPlaneIdealBoundary) :
    DifferentiableOn ℂ (endpointSeed a b) {z : ℂ | 0 < z.im} := by
  have hn (w : ℂ) (hw : w.im = 0) (z : ℂ) (hz : 0 < z.im) : z - w ≠ 0 := by
    intro he
    have him := congrArg Complex.im (sub_eq_zero.mp he)
    linarith
  have hd (w : ℂ) : DifferentiableOn ℂ (fun z : ℂ => (z - w) ^ 2)
      {z : ℂ | 0 < z.im} := (differentiableOn_id.sub_const w).pow 2
  have hc (w : ℂ) : DifferentiableOn ℂ (fun _ : ℂ => w) {z : ℂ | 0 < z.im} :=
    differentiableOn_const w
  cases a using OnePoint.rec with
  | infty =>
    cases b using OnePoint.rec with
    | infty => exact hc 0
    | coe b =>
      have hb' := (coe_mem_halfPlaneIdealBoundary b).mp hb
      exact (hc 1).div (hd b) (fun z hz => pow_ne_zero 2 (hn b hb' z hz))
  | coe a =>
    have ha' := (coe_mem_halfPlaneIdealBoundary a).mp ha
    cases b using OnePoint.rec with
    | infty =>
      exact (hc 1).div (hd a) (fun z hz => pow_ne_zero 2 (hn a ha' z hz))
    | coe b =>
      have hb' := (coe_mem_halfPlaneIdealBoundary b).mp hb
      exact (hc ((a - b) ^ 2)).div ((hd a).mul (hd b)) (fun z hz =>
        mul_ne_zero (pow_ne_zero 2 (hn a ha' z hz)) (pow_ne_zero 2 (hn b hb' z hz)))

/-- The seed of an actual half-plane geodesic, with its full ideal-endpoint pair. -/
def seed : HalfPlaneLine → ℂ → ℂ
  | .vertical x => endpointSeed (x : ℂ) ∞
  | .circle c r _ => endpointSeed ((c - r : ℝ) : ℂ) ((c + r : ℝ) : ℂ)

theorem seed_eq_endpointSeed {L : HalfPlaneLine} {a b : OnePoint ℂ}
    (h : L.idealEndpoints = {a, b}) : seed L = endpointSeed a b := by
  cases L with
  | vertical x =>
    exact endpointSeed_eq_of_pair_eq ((vertical_idealEndpoints x).symm.trans h)
  | circle c r hr =>
    exact endpointSeed_eq_of_pair_eq ((circle_idealEndpoints c r hr).symm.trans h)

theorem seed_differentiableOn (L : HalfPlaneLine) :
    DifferentiableOn ℂ (seed L) {z : ℂ | 0 < z.im} := by
  obtain ⟨a, b, _, _, ha, hb, hends, _⟩ := L.exists_idealEndpoints_pair
  rw [seed_eq_endpointSeed hends]
  exact endpointSeed_differentiableOn ha hb

/-- Every actual hyperbolic real Mobius map has the source coefficient on all of
`H`, for every choice of its two actual fixed endpoints. -/
theorem seed_hyperbolic_spec (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2) :
    DifferentiableOn ℂ (seed (hHyperbolicAxis A hA ht)) {z : ℂ | 0 < z.im} ∧
      ∀ a b : OnePoint ℂ, Function.fixedPoints (realSLMobius A).val = {a, b} →
        seed (hHyperbolicAxis A hA ht) = endpointSeed a b := by
  refine ⟨seed_differentiableOn _, ?_⟩
  intro a b hab
  exact seed_eq_endpointSeed ((hHyperbolicAxis_idealEndpoints A hA ht).trans hab)

end LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries
