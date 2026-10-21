module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ModelCoordinates
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.Geodesic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.Closed
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Ambient Poincaré–Klein coordinate maps.

The radial coordinate maps extend to ambient Euclidean space. This module records their
continuity, boundary behavior, and inverse identities on the closed unit ball.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Module
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

theorem continuous_kleinFormula : Continuous kleinFormula := by
  have hn : Continuous (fun z : ℂ => ‖z‖ ^ 2) := continuous_norm.pow 2
  have hs : Continuous (fun z : ℂ => (2 : ℝ) / (1 + ‖z‖ ^ 2)) :=
    continuous_const.div (continuous_const.add hn) (fun _ => by positivity)
  exact (Complex.continuous_ofReal.comp hs).mul continuous_id

theorem continuous_inverseKleinFormula : Continuous inverseKleinFormula := by
  have hn : Continuous (fun z : ℂ => ‖z‖ ^ 2) := continuous_norm.pow 2
  have hs : Continuous (fun z : ℂ => (1 : ℝ) / (1 + Real.sqrt (1 - ‖z‖ ^ 2))) :=
    continuous_const.div (continuous_const.add ((continuous_const.sub hn).sqrt)) (fun _ => by positivity)
  exact (Complex.continuous_ofReal.comp hs).mul continuous_id

theorem kleinFormula_norm_one {z : ℂ} (hz : ‖z‖ = 1) : kleinFormula z = z := by
  norm_num [kleinFormula,hz]

theorem inverseKleinFormula_norm_one {z : ℂ} (hz : ‖z‖ = 1) : inverseKleinFormula z = z := by
  simp only [inverseKleinFormula,hz,one_pow,sub_self,Real.sqrt_zero,add_zero,div_one,
    Complex.ofReal_one,one_mul]

/-- Extend the actual closed-disc Klein map to the plane by the identity outside the disc. -/
def ambientKleinFormula (z : ℂ) : ℂ := by
  classical
  exact if ‖z‖ ≤ 1 then kleinFormula z else z

def ambientInverseKleinFormula (z : ℂ) : ℂ := by
  classical
  exact if ‖z‖ ≤ 1 then inverseKleinFormula z else z

theorem DiscLine.closedKlein_affine_equation (L : DiscLine) :
    ∃ (n : ℂ) (t : ℝ), n ≠ 0 ∧
      ∀ p : 𝕔𝔻, p ∈ L.closedCarrier ↔ inner ℝ n (closedKleinCoordinate p) = t := by
  obtain ⟨n,t,hn,he⟩ := L.exists_closedKlein_affine_chord
  refine ⟨n,t,hn,fun p => ?_⟩
  constructor
  · intro hp
    have hm := mem_image_of_mem closedKleinCoordinate hp
    rw [he] at hm
    exact hm.1
  · intro hp
    apply closedKleinCoordinate_injective.mem_set_image.mp
    rw [he]
    exact ⟨hp,by simpa only [Metric.mem_closedBall,dist_zero_right,closedKleinCoordinate]
      using (closedPoincareToKlein p).norm_le_one⟩

theorem continuous_ambientKleinFormula : Continuous ambientKleinFormula := by
  classical
  apply Continuous.if _ continuous_kleinFormula continuous_id
  intro z hz
  have he : {w : ℂ | ‖w‖ ≤ 1} = Metric.closedBall 0 1 := by ext w; simp
  rw [he] at hz
  have hn : ‖z‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using Metric.frontier_closedBall_subset_sphere hz
  exact kleinFormula_norm_one hn

theorem continuous_ambientInverseKleinFormula : Continuous ambientInverseKleinFormula := by
  classical
  apply Continuous.if _ continuous_inverseKleinFormula continuous_id
  intro z hz
  have he : {w : ℂ | ‖w‖ ≤ 1} = Metric.closedBall 0 1 := by ext w; simp
  rw [he] at hz
  have hn : ‖z‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using Metric.frontier_closedBall_subset_sphere hz
  exact inverseKleinFormula_norm_one hn

theorem ambientInverseKleinFormula_ambientKleinFormula (z : ℂ) :
    ambientInverseKleinFormula (ambientKleinFormula z) = z := by
  by_cases hz : ‖z‖ ≤ 1
  · have hK : ‖kleinFormula z‖ ≤ 1 := kleinFormula_mem_closedDisc (Complex.UnitClosedDisc.mk z hz)
    rw [ambientKleinFormula,ite_eq_left hz,ambientInverseKleinFormula,ite_eq_left hK]
    exact congrArg (fun p : 𝕔𝔻 => (p : ℂ))
      (closedKleinToPoincare_closedPoincareToKlein (Complex.UnitClosedDisc.mk z hz))
  · rw [ambientKleinFormula,ite_eq_right hz,ambientInverseKleinFormula,ite_eq_right hz]

theorem ambientKleinFormula_ambientInverseKleinFormula (z : ℂ) :
    ambientKleinFormula (ambientInverseKleinFormula z) = z := by
  by_cases hz : ‖z‖ ≤ 1
  · have hK : ‖inverseKleinFormula z‖ ≤ 1 := inverseKleinFormula_mem_closedDisc (Complex.UnitClosedDisc.mk z hz)
    rw [ambientInverseKleinFormula,ite_eq_left hz,ambientKleinFormula,ite_eq_left hK]
    exact congrArg (fun p : 𝕔𝔻 => (p : ℂ))
      (closedPoincareToKlein_closedKleinToPoincare (Complex.UnitClosedDisc.mk z hz))
  · rw [ambientInverseKleinFormula,ite_eq_right hz,ambientKleinFormula,ite_eq_right hz]

/-- A genuine ambient-plane homeomorphism agreeing with the actual compact Klein model. -/
def ambientKleinHomeomorph : ℂ ≃ₜ ℂ where
  toFun := ambientKleinFormula
  invFun := ambientInverseKleinFormula
  left_inv := ambientInverseKleinFormula_ambientKleinFormula
  right_inv := ambientKleinFormula_ambientInverseKleinFormula
  continuous_toFun := continuous_ambientKleinFormula
  continuous_invFun := continuous_ambientInverseKleinFormula

theorem ambientKleinHomeomorph_closed (p : 𝕔𝔻) :
    ambientKleinHomeomorph (p : ℂ) = closedKleinCoordinate p := by
  change ambientKleinFormula (p : ℂ) = _
  rw [ambientKleinFormula,ite_eq_left p.norm_le_one]
  rfl

end LowDimensionalTopology.Geometry.Hyperbolic
