module

public import LowDimensionalTopology.Geometry.Teichmuller.LiteralKobayashiExtendedCore
public import Mathlib.Basic.ENNReal.Operations

/-!
# Single-link comparisons for the literal disk chains

Exchange the endpoints of an actual disk, or add one actual link to an
existing finite chain. The original extended infima and their positive
link counts are unchanged. These comparisons require no finite-distance
or global connectedness assertion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff Complex.UnitDisc BigOperators ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore

open Surfaces Hyperbolic

private theorem discCost_comm (a b : 𝔻) : discPathEDist a b = discPathEDist b a := by
  simp only [discPathEDist_eq_halfPlane, piecewisePathEDist_eq_metric, dist_comm]

universe u

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]

/-- Exchanging the two endpoints of each actual disk preserves its infimum. -/
theorem oneDiskEDist_comm (p q : M) :
    oneDiskEDist (d := d) p q = oneDiskEDist (d := d) q p := by
  let := discRiemannSurface.toRiemannAtlas.toChartedSpace
  have hle (p q : M) : oneDiskEDist (d := d) p q ≤ oneDiskEDist (d := d) q p := by
    conv_rhs => unfold oneDiskEDist
    refine le_iInf fun f => le_iInf fun hf => le_iInf fun a =>
      le_iInf fun b => le_iInf fun hfa => le_iInf fun hfb => ?_
    simpa only [hfa, hfb] using!
      (oneDiskEDist_le (d := d) hf b a).trans_eq
        (discCost_comm (discFiniteHomeomorph b) (discFiniteHomeomorph a))
  exact le_antisymm (hle p q) (hle q p)

/-- Appending one endpoint link adds its actual one-disk cost. -/
theorem finiteChainEDist_append_one_le (n : ℕ) (p q r : M) :
    finiteChainEDist (d := d) (n + 1) p r ≤
      finiteChainEDist (d := d) n p q + oneDiskEDist (d := d) q r := by
  conv_rhs =>
    unfold finiteChainEDist
    simp only [ENNReal.iInf_add]
  refine le_iInf fun s => le_iInf fun h0 => le_iInf fun hq => ?_
  let t : Fin (n + 3) → M := Fin.snoc (α := fun _ => M) s r
  have htcast (i : Fin (n + 2)) : t i.castSucc = s i :=
    Fin.snoc_castSucc (n := n + 2) (α := fun _ => M) r s i
  have ht0 : t 0 = p := by simpa only [t, Fin.snoc_apply_zero] using h0
  have htr : t (Fin.last (n + 2)) = r := by simp only [t, Fin.snoc_last]
  have htail : oneDiskEDist (d := d) (t ((Fin.last (n + 1)).castSucc))
      (t ((Fin.last (n + 1)).succ)) = oneDiskEDist (d := d) q r := by
    change oneDiskEDist (d := d) (t ((Fin.last (n + 1)).castSucc))
      (t (Fin.last (n + 2))) = oneDiskEDist (d := d) q r
    rw [htr, htcast, hq]
  have hsum : (∑ i : Fin (n + 2), oneDiskEDist (d := d) (t i.castSucc) (t i.succ)) =
      (∑ i : Fin (n + 1), oneDiskEDist (d := d) (s i.castSucc) (s i.succ)) +
        oneDiskEDist (d := d) q r := by
    rw [Fin.sum_univ_castSucc]
    have hinit : (∑ i : Fin (n + 1),
        oneDiskEDist (d := d) (t i.castSucc.castSucc) (t i.castSucc.succ)) =
        ∑ i : Fin (n + 1), oneDiskEDist (d := d) (s i.castSucc) (s i.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : (i.castSucc : Fin (n + 2)).succ = i.succ.castSucc := rfl
      rw [hi, htcast, htcast]
    rw [hinit, htail]
  simpa only [hsum] using!
    finiteChainEDist_le_sum (d := d) (n + 1) p r t ht0 htr

/-- Prepending one endpoint link adds its actual one-disk cost. -/
theorem finiteChainEDist_prepend_one_le (n : ℕ) (p q r : M) :
    finiteChainEDist (d := d) (n + 1) p r ≤
      oneDiskEDist (d := d) p q + finiteChainEDist (d := d) n q r := by
  conv_rhs =>
    unfold finiteChainEDist
    simp only [ENNReal.add_iInf]
  refine le_iInf fun s => le_iInf fun h0 => le_iInf fun hq => ?_
  let t : Fin (n + 3) → M := Fin.cons (α := fun _ => M) p s
  have htsucc (i : Fin (n + 2)) : t i.succ = s i := by
    simp only [t, Fin.cons_succ]
  have ht0 : t 0 = p := by simp only [t, Fin.cons_zero]
  have htr : t (Fin.last (n + 2)) = r := by
    change t ((Fin.last (n + 1)).succ) = r
    rw [htsucc, hq]
  have hhead : oneDiskEDist (d := d) (t ((0 : Fin (n + 2)).castSucc))
      (t ((0 : Fin (n + 2)).succ)) = oneDiskEDist (d := d) p q := by
    change oneDiskEDist (d := d) (t 0) (t ((0 : Fin (n + 2)).succ)) =
      oneDiskEDist (d := d) p q
    rw [ht0, htsucc, h0]
  have hsum : (∑ i : Fin (n + 2), oneDiskEDist (d := d) (t i.castSucc) (t i.succ)) =
      oneDiskEDist (d := d) p q +
        ∑ i : Fin (n + 1), oneDiskEDist (d := d) (s i.castSucc) (s i.succ) := by
    rw [Fin.sum_univ_succ]
    have hrest : (∑ i : Fin (n + 1),
        oneDiskEDist (d := d) (t i.succ.castSucc) (t i.succ.succ)) =
        ∑ i : Fin (n + 1), oneDiskEDist (d := d) (s i.castSucc) (s i.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : (i.succ.castSucc : Fin (n + 3)) = i.castSucc.succ := rfl
      rw [hi, htsucc, htsucc]
    rw [hhead, hrest]
  simpa only [hsum] using!
    finiteChainEDist_le_sum (d := d) (n + 1) p r t ht0 htr

/-- The infimum over all chain lengths also admits one appended endpoint link. -/
theorem kobayashiEDist_append_one_le (p q r : M) :
    kobayashiEDist (d := d) p r ≤
      kobayashiEDist (d := d) p q + oneDiskEDist (d := d) q r := by
  conv_rhs =>
    unfold kobayashiEDist
    rw [ENNReal.iInf_add]
  refine le_iInf fun n => ?_
  have hleft : kobayashiEDist (d := d) p r ≤ finiteChainEDist (d := d) (n + 1) p r :=
    iInf_le (fun m => finiteChainEDist (d := d) m p r) (n + 1)
  simpa only [kobayashiEDist] using!
    hleft.trans (finiteChainEDist_append_one_le (d := d) n p q r)

/-- The infimum over all chain lengths also admits one prepended endpoint link. -/
theorem kobayashiEDist_prepend_one_le (p q r : M) :
    kobayashiEDist (d := d) p r ≤
      oneDiskEDist (d := d) p q + kobayashiEDist (d := d) q r := by
  conv_rhs =>
    unfold kobayashiEDist
    rw [ENNReal.add_iInf]
  refine le_iInf fun n => ?_
  have hleft : kobayashiEDist (d := d) p r ≤ finiteChainEDist (d := d) (n + 1) p r :=
    iInf_le (fun m => finiteChainEDist (d := d) m p r) (n + 1)
  simpa only [kobayashiEDist] using!
    hleft.trans (finiteChainEDist_prepend_one_le (d := d) n p q r)

end LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore
