module

public import LowDimensionalTopology.Geometry.Surfaces.Covering.DiscUniversalDeck
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The literal disk and finite-chain definitions for a complex manifold

The model is an ordinary finite-dimensional complex manifold. The disk
cost has density `2 / (1 - |z|^2)`, hence the full logarithmic radial
formula. Extended nonnegative reals retain empty infima as infinity.
The only additional calculation is the decreasing-chain observation
and its decreasing limit. All-pair finiteness, real-valued continuity,
the pseudometric axioms and completeness remain separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Manifold ContDiff BigOperators Complex.UnitDisc UpperHalfPlane ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore

open Surfaces Hyperbolic

universe u
local notation "Δ" => extendedUnitDisc

/-- One actual holomorphic disk, with full Poincaré cost; empty families have value infinity. -/
def oneDiskEDist {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M] (p q : M) : ℝ≥0∞ :=
  letI := discRiemannSurface.toRiemannAtlas.toChartedSpace
  ⨅ (f : Δ → M) (_ : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin d → ℂ) ω f)
    (a : Δ) (b : Δ) (_ : f a = p) (_ : f b = q),
      discPathEDist (discFiniteHomeomorph a) (discFiniteHomeomorph b)

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]

/-- The literal finite-chain infimum; Lean index `n` means exactly source `n+1` links. -/
def finiteChainEDist (n : ℕ) (p q : M) : ℝ≥0∞ :=
  ⨅ (s : Fin (n + 2) → M) (_ : s 0 = p) (_ : s (Fin.last (n + 1)) = q),
    ∑ i : Fin (n + 1), oneDiskEDist (d := d) (s i.castSucc) (s i.succ)

/-- The infimum over all positive finite chain lengths, before any finiteness assertion. -/
def kobayashiEDist (p q : M) : ℝ≥0∞ := ⨅ n : ℕ, finiteChainEDist (d := d) n p q

theorem oneDiskEDist_le {f : Δ → M}
    (hf : let := discRiemannSurface.toRiemannAtlas.toChartedSpace
      ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin d → ℂ) ω f) (a b : Δ) :
    oneDiskEDist (d := d) (f a) (f b) ≤
      discPathEDist (discFiniteHomeomorph a) (discFiniteHomeomorph b) := by
  let := discRiemannSurface.toRiemannAtlas.toChartedSpace
  unfold oneDiskEDist
  exact iInf_le_of_le f (iInf_le_of_le hf (iInf_le_of_le a
    (iInf_le_of_le b (iInf_le_of_le rfl (iInf_le _ rfl)))))

/-- A constant holomorphic disk supplies the zero final link used below. -/
theorem oneDiskEDist_self (p : M) : oneDiskEDist (d := d) p p = 0 := by
  let := discRiemannSurface.toRiemannAtlas.toChartedSpace
  let a : Δ := discFiniteHomeomorph.symm (0 : 𝔻)
  have h := oneDiskEDist_le (d := d) (f := fun _ : Δ => p) contMDiff_const a a
  apply le_antisymm
  · apply h.trans
    unfold discPathEDist
    exact iInf_le_of_le (DiscPiecewiseC1Curve.nil _) (by
      change ENNReal.ofReal (0 : ℝ) ≤ 0
      exact le_of_eq ENNReal.ofReal_zero)
  · exact bot_le

theorem finiteChainEDist_le_sum (n : ℕ) (p q : M) (s : Fin (n + 2) → M)
    (h0 : s 0 = p) (hq : s (Fin.last (n + 1)) = q) :
    finiteChainEDist (d := d) n p q ≤
      ∑ i : Fin (n + 1), oneDiskEDist (d := d) (s i.castSucc) (s i.succ) := by
  unfold finiteChainEDist
  exact iInf_le_of_le s (iInf_le_of_le h0 (iInf_le _ hq))

/-- The first chain infimum is exactly the source's one-disk function. -/
theorem finiteChainEDist_zero (p q : M) :
    finiteChainEDist (d := d) 0 p q = oneDiskEDist (d := d) p q := by
  apply le_antisymm
  · simpa using finiteChainEDist_le_sum (d := d) 0 p q ![p, q] rfl rfl
  · unfold finiteChainEDist
    refine le_iInf fun s => le_iInf fun h0 => le_iInf fun hq => ?_
    rw [Fin.sum_univ_one]
    change oneDiskEDist (d := d) p q ≤ oneDiskEDist (d := d) (s 0) (s 1)
    rw [h0, show s 1 = q from hq]

/-- The notes' decreasing-chain observation: append a constant final link. -/
theorem finiteChainEDist_succ_le (n : ℕ) (p q : M) :
    finiteChainEDist (d := d) (n + 1) p q ≤ finiteChainEDist (d := d) n p q := by
  unfold finiteChainEDist
  refine le_iInf fun s => le_iInf fun h0 => le_iInf fun hq => ?_
  let t : Fin (n + 3) → M := Fin.snoc (α := fun _ => M) s q
  have htcast (i : Fin (n + 2)) : t i.castSucc = s i :=
    Fin.snoc_castSucc (n := n + 2) (α := fun _ => M) q s i
  have ht0 : t 0 = p := by simpa only [t, Fin.snoc_apply_zero] using h0
  have htq : t (Fin.last (n + 2)) = q := by simp only [t, Fin.snoc_last]
  have htail : oneDiskEDist (d := d) (t ((Fin.last (n + 1)).castSucc))
      (t ((Fin.last (n + 1)).succ)) = 0 := by
    change oneDiskEDist (d := d) (t ((Fin.last (n + 1)).castSucc)) (t (Fin.last (n + 2))) = 0
    rw [htq, htcast, hq, oneDiskEDist_self (d := d)]
  have hsum : (∑ i : Fin (n + 2), oneDiskEDist (d := d) (t i.castSucc) (t i.succ)) =
      ∑ i : Fin (n + 1), oneDiskEDist (d := d) (s i.castSucc) (s i.succ) := by
    rw [Fin.sum_univ_castSucc]
    have hinit : (∑ i : Fin (n + 1),
        oneDiskEDist (d := d) (t i.castSucc.castSucc) (t i.castSucc.succ)) =
        ∑ i : Fin (n + 1), oneDiskEDist (d := d) (s i.castSucc) (s i.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : (i.castSucc : Fin (n + 2)).succ = i.succ.castSucc := rfl
      rw [hi, htcast, htcast]
    rw [hinit, htail, add_zero]
  exact (finiteChainEDist_le_sum (d := d) (n + 1) p q t ht0 htq).trans_eq hsum

/-- The extended chain infimum is the decreasing order-topological limit in the definition. -/
theorem finiteChainEDist_tendsto (p q : M) :
    Tendsto (fun n => finiteChainEDist (d := d) n p q)
      atTop (𝓝 (kobayashiEDist (d := d) p q)) :=
  tendsto_atTop_iInf
    (antitone_nat_of_succ_le (fun n => finiteChainEDist_succ_le (d := d) n p q))

end LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore
