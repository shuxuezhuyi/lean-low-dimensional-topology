module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularMirrorCapGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeLineReflections
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane Pointwise

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The two literal reflection products and their genuine inverses satisfy
the four closed-cap mapping clauses of the free-group ping-pong lemma. -/
theorem annular_four_closed_caps_pingPong_mappings (E r x : ℝ)
    (hE : 0 < E) (hr : 0 < r) :
    let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
    let σ1 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 E hE)
    let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
    let γ1 := σ0 * σ1
    let γ2 := σ2 * σ0
    let O := {z : ℍ | E ≤ ‖(z : ℂ)‖}
    let B := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ ≤ r}
    γ1 • Oᶜ ⊆ σ0 '' O ∧ γ1⁻¹ • (σ0 '' O)ᶜ ⊆ O ∧
      γ2 • (σ0 '' B)ᶜ ⊆ B ∧ γ2⁻¹ • Bᶜ ⊆ σ0 '' B := by
  let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
  let σ1 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 E hE)
  let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
  let O := {z : ℍ | E ≤ ‖(z : ℂ)‖}
  let B := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ ≤ r}
  change (σ0 * σ1) • Oᶜ ⊆ σ0 '' O ∧
    (σ0 * σ1)⁻¹ • (σ0 '' O)ᶜ ⊆ O ∧
    (σ2 * σ0) • (σ0 '' B)ᶜ ⊆ B ∧
    (σ2 * σ0)⁻¹ • Bᶜ ⊆ σ0 '' B
  have h0 (z : ℍ) : σ0 (σ0 z) = z :=
    (HalfPlaneLine.circle 0 1 zero_lt_one).reflection_involutive z
  have h1 (z : ℍ) : σ1 (σ1 z) = z :=
    (HalfPlaneLine.circle 0 E hE).reflection_involutive z
  have hOiff (z : ℍ) : ‖(σ1 z : ℂ)‖ ≤ E ↔ E ≤ ‖(z : ℂ)‖ := by
    change ‖((HalfPlaneLine.circle 0 E hE).reflection z : ℂ)‖ ≤ E ↔ E ≤ ‖(z : ℂ)‖
    simpa only [Complex.ofReal_zero, sub_zero] using
      circle_reflection_radius_le_iff 0 E hE z
  have hO (z : ℍ) (hz : z ∈ Oᶜ) : σ1 z ∈ O := by
    change ¬ E ≤ ‖(z : ℂ)‖ at hz
    apply (hOiff (σ1 z)).mp
    simpa only [h1] using (lt_of_not_ge hz).le
  have hB (z : ℍ) (hz : z ∈ Bᶜ) : σ2 z ∈ B := by
    change ¬ ‖(z : ℂ) - (x : ℂ)‖ ≤ r at hz
    exact (circle_reflection_radius_le_iff x r hr z).mpr (lt_of_not_ge hz).le
  have hnot0 (S : Set ℍ) (z : ℍ) (hz : z ∈ (σ0 '' S)ᶜ) : σ0 z ∈ Sᶜ := by
    intro hmem
    exact hz ⟨σ0 z, hmem, h0 z⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change σ0 (σ1 z) ∈ σ0 '' O
    exact ⟨σ1 z, hO z hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    change σ1 (σ0 z) ∈ O
    exact hO (σ0 z) (hnot0 O z hz)
  · rintro _ ⟨z, hz, rfl⟩
    change σ2 (σ0 z) ∈ B
    exact hB (σ0 z) (hnot0 B z hz)
  · rintro _ ⟨z, hz, rfl⟩
    change σ0 (σ2 z) ∈ σ0 '' B
    exact ⟨σ2 z, hB z hz, rfl⟩

end LowDimensionalTopology.Geometry.Hyperbolic
