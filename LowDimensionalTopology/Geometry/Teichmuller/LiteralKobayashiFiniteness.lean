module

public import LowDimensionalTopology.Geometry.Teichmuller.LiteralKobayashiLocalDisk
public import LowDimensionalTopology.Geometry.Teichmuller.LiteralKobayashiOneLink
public import Mathlib.Topology.Connected.Clopen

/-!
# Finiteness of the literal chains on a connected complex manifold

Local actual disks make the set reached by some finite-cost chain both
open and closed. Connectedness then gives a finite chain length between
each pair of original points. Individual fixed-length infima may still
be infinite.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore

universe u

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]

private theorem eventually_oneDiskEDist_ne_top (p : M) :
    ∀ᶠ q in 𝓝 p, oneDiskEDist (d := d) p q ≠ ⊤ := by
  have hnear : ∀ᶠ q in 𝓝 p, oneDiskEDist (d := d) p q < 1 :=
    (oneDiskEDist_tendsto_right (d := d) p).eventually
      (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 from zero_lt_one))
  exact hnear.mono (fun _ h => ne_top_of_lt h)

/-- Each pair in a connected original manifold has some positive finite chain length
whose literal comparison value is finite. -/
theorem exists_finiteChainEDist_ne_top [ConnectedSpace M] (p q : M) :
    ∃ n : ℕ, finiteChainEDist (d := d) n p q ≠ ⊤ := by
  let A : Set M := {r | ∃ n : ℕ, finiteChainEDist (d := d) n p r ≠ ⊤}
  have hpA : p ∈ A := by
    refine ⟨0, ?_⟩
    simpa only [finiteChainEDist_zero, oneDiskEDist_self] using ENNReal.zero_ne_top
  have hA : IsOpen A := by
    apply isOpen_iff_eventually.mpr
    intro r hr
    obtain ⟨n, hn⟩ := hr
    apply (eventually_oneDiskEDist_ne_top (d := d) r).mono
    intro s hs
    refine ⟨n + 1, ?_⟩
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hn, hs⟩)
      (finiteChainEDist_append_one_le (d := d) n p r s)
  have hAc : IsOpen Aᶜ := by
    apply isOpen_iff_eventually.mpr
    intro r hr
    apply (eventually_oneDiskEDist_ne_top (d := d) r).mono
    intro s hs hsA
    apply hr
    obtain ⟨n, hn⟩ := hsA
    have hsr : oneDiskEDist (d := d) s r ≠ ⊤ := by
      rw [oneDiskEDist_comm (d := d) s r]
      exact hs
    refine ⟨n + 1, ?_⟩
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hn, hsr⟩)
      (finiteChainEDist_append_one_le (d := d) n p s r)
  have hclosed : IsClosed A := by
    simpa only [compl_compl] using hAc.isClosed_compl
  have hAll : A = univ := (show IsClopen A from ⟨hclosed, hA⟩).eq_univ ⟨p, hpA⟩
  change q ∈ A
  simpa only [hAll] using (Set.mem_univ q)

/-- The original connected-manifold Kobayashi infimum is finite at every pair. -/
theorem kobayashiEDist_ne_top [ConnectedSpace M] (p q : M) :
    kobayashiEDist (d := d) p q ≠ ⊤ := by
  obtain ⟨n, hn⟩ := exists_finiteChainEDist_ne_top (d := d) p q
  exact ne_top_of_le_ne_top hn
    (show kobayashiEDist (d := d) p q ≤ finiteChainEDist (d := d) n p q from
      iInf_le (fun m => finiteChainEDist (d := d) m p q) n)

end LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore
