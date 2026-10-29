module

public import LowDimensionalTopology.Geometry.Teichmuller.LiteralKobayashiFiniteness
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Real continuity of the original connected-manifold infimum

Two original single-link comparisons bound a change of endpoints by
their actual local disk costs. Real conversion is used only after the
Kobayashi values are proved finite and the endpoint error is eventually
finite. Continuity uses the original product topology.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore

universe u

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]

private theorem kobayashiEDist_le_add_endpoint_costs (a b p q : M) :
    kobayashiEDist (d := d) p q ≤ kobayashiEDist (d := d) a b +
      (oneDiskEDist (d := d) a p + oneDiskEDist (d := d) b q) := by
  calc
    kobayashiEDist (d := d) p q ≤
        oneDiskEDist (d := d) p a + kobayashiEDist (d := d) a q :=
      kobayashiEDist_prepend_one_le (d := d) p a q
    _ ≤ oneDiskEDist (d := d) p a +
        (kobayashiEDist (d := d) a b + oneDiskEDist (d := d) b q) :=
      add_le_add le_rfl (kobayashiEDist_append_one_le (d := d) a b q)
    _ = kobayashiEDist (d := d) a b +
        (oneDiskEDist (d := d) a p + oneDiskEDist (d := d) b q) := by
      rw [oneDiskEDist_comm (d := d) p a, ← add_assoc,
        add_comm (oneDiskEDist (d := d) a p) (kobayashiEDist (d := d) a b), add_assoc]

/-- The faithful real-valued infimum is jointly continuous on the original product topology. -/
theorem continuous_kobayashiEDist_toReal [ConnectedSpace M] :
    Continuous (fun z : M × M => (kobayashiEDist (d := d) z.1 z.2).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  rcases z₀ with ⟨a, b⟩
  let E : M × M → ℝ≥0∞ := fun z =>
    oneDiskEDist (d := d) a z.1 + oneDiskEDist (d := d) b z.2
  have hfirst : Tendsto (fun z : M × M => oneDiskEDist (d := d) a z.1)
      (𝓝 (a, b)) (𝓝 0) :=
    (oneDiskEDist_tendsto_right (d := d) a).comp (continuous_fst.tendsto (a, b))
  have hsecond : Tendsto (fun z : M × M => oneDiskEDist (d := d) b z.2)
      (𝓝 (a, b)) (𝓝 0) :=
    (oneDiskEDist_tendsto_right (d := d) b).comp (continuous_snd.tendsto (a, b))
  have hE : Tendsto E (𝓝 (a, b)) (𝓝 0) := by
    simpa only [add_zero] using hfirst.add hsecond
  have hEfinite : ∀ᶠ z in 𝓝 (a, b), E z ≠ ⊤ := by
    have hsmall : ∀ᶠ z in 𝓝 (a, b), E z < 1 :=
      hE.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 from zero_lt_one))
    exact hsmall.mono (fun _ h => ne_top_of_lt h)
  have herror : Tendsto (fun z => (E z).toReal) (𝓝 (a, b)) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
  have hcenter : kobayashiEDist (d := d) a b ≠ ⊤ := kobayashiEDist_ne_top (d := d) a b
  have hsandwich : ∀ᶠ z in 𝓝 (a, b),
      (kobayashiEDist (d := d) a b).toReal - (E z).toReal ≤
          (kobayashiEDist (d := d) z.1 z.2).toReal ∧
        (kobayashiEDist (d := d) z.1 z.2).toReal ≤
          (kobayashiEDist (d := d) a b).toReal + (E z).toReal := by
    apply hEfinite.mono
    intro z hz
    have hupper : kobayashiEDist (d := d) z.1 z.2 ≤
        kobayashiEDist (d := d) a b + E z :=
      kobayashiEDist_le_add_endpoint_costs (d := d) a b z.1 z.2
    have hlower := kobayashiEDist_le_add_endpoint_costs (d := d) z.1 z.2 a b
    rw [oneDiskEDist_comm (d := d) z.1 a,
      oneDiskEDist_comm (d := d) z.2 b] at hlower
    have hcurrent : kobayashiEDist (d := d) z.1 z.2 ≠ ⊤ :=
      kobayashiEDist_ne_top (d := d) z.1 z.2
    have hupperReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hcenter, hz⟩) hupper
    rw [ENNReal.toReal_add hcenter hz] at hupperReal
    have hlowerReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hcurrent, hz⟩) hlower
    rw [ENNReal.toReal_add hcurrent hz] at hlowerReal
    exact ⟨sub_le_iff_le_add.mpr hlowerReal, hupperReal⟩
  have hconst : Tendsto (fun _ : M × M => (kobayashiEDist (d := d) a b).toReal)
      (𝓝 (a, b)) (𝓝 (kobayashiEDist (d := d) a b).toReal) := tendsto_const_nhds
  have hlowerLimit : Tendsto
      (fun z : M × M => (kobayashiEDist (d := d) a b).toReal - (E z).toReal)
      (𝓝 (a, b)) (𝓝 (kobayashiEDist (d := d) a b).toReal) := by
    simpa only [sub_zero] using hconst.sub herror
  have hupperLimit : Tendsto
      (fun z : M × M => (kobayashiEDist (d := d) a b).toReal + (E z).toReal)
      (𝓝 (a, b)) (𝓝 (kobayashiEDist (d := d) a b).toReal) := by
    simpa only [add_zero] using hconst.add herror
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun z : M × M => (kobayashiEDist (d := d) z.1 z.2).toReal)
    (g := fun z : M × M => (kobayashiEDist (d := d) a b).toReal - (E z).toReal)
    (h := fun z : M × M => (kobayashiEDist (d := d) a b).toReal + (E z).toReal)
    hlowerLimit hupperLimit (hsandwich.mono fun _ h => h.1) (hsandwich.mono fun _ h => h.2)

end LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore
