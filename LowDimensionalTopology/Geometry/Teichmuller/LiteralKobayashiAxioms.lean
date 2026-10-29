module

public import LowDimensionalTopology.Geometry.Teichmuller.LiteralKobayashiFiniteness
public import Mathlib.Basic.ENNReal.Real

/-!
# Pseudodistance axioms of the literal chain infimum

Induction on the original finite chain length extends the proved
single-link comparisons across each actual chain. Taking the same
infima gives symmetry and the triangle inequality. On the original
connected manifold, the proved finite values then give the real axioms.
No manifold topology or metric-space structure is replaced.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff BigOperators ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore

universe u

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]

private theorem kobayashiEDist_le_oneDiskEDist (p q : M) :
    kobayashiEDist (d := d) p q ≤ oneDiskEDist (d := d) p q := by
  simpa only [finiteChainEDist_zero] using!
    (show kobayashiEDist (d := d) p q ≤ finiteChainEDist (d := d) 0 p q from
      iInf_le (fun n => finiteChainEDist (d := d) n p q) 0)

/-- A constant positive-length chain gives zero diagonal value. -/
theorem kobayashiEDist_self (p : M) : kobayashiEDist (d := d) p p = 0 := by
  apply le_antisymm
  · simpa only [oneDiskEDist_self] using! kobayashiEDist_le_oneDiskEDist (d := d) p p
  · exact bot_le

private theorem kobayashiEDist_reverse_le_chain :
    ∀ (n : ℕ) (s : Fin (n + 2) → M),
      kobayashiEDist (d := d) (s (Fin.last (n + 1))) (s 0) ≤
        ∑ i : Fin (n + 1), oneDiskEDist (d := d) (s i.castSucc) (s i.succ) := by
  intro n
  induction n with
  | zero =>
      intro s
      rw [Fin.sum_univ_one]
      change kobayashiEDist (d := d) (s 1) (s 0) ≤ oneDiskEDist (d := d) (s 0) (s 1)
      exact (kobayashiEDist_le_oneDiskEDist (d := d) (s 1) (s 0)).trans_eq
        (oneDiskEDist_comm (d := d) (s 1) (s 0))
  | succ n ih =>
      intro s
      let t : Fin (n + 2) → M := fun i => s i.castSucc
      rw [Fin.sum_univ_castSucc]
      change kobayashiEDist (d := d) (s (Fin.last (n + 2))) (t 0) ≤
        (∑ i : Fin (n + 1), oneDiskEDist (d := d) (t i.castSucc) (t i.succ)) +
          oneDiskEDist (d := d) (t (Fin.last (n + 1))) (s (Fin.last (n + 2)))
      calc
        kobayashiEDist (d := d) (s (Fin.last (n + 2))) (t 0) ≤
            oneDiskEDist (d := d) (s (Fin.last (n + 2))) (t (Fin.last (n + 1))) +
              kobayashiEDist (d := d) (t (Fin.last (n + 1))) (t 0) :=
          kobayashiEDist_prepend_one_le (d := d) _ _ _
        _ ≤ oneDiskEDist (d := d) (s (Fin.last (n + 2))) (t (Fin.last (n + 1))) +
            ∑ i : Fin (n + 1), oneDiskEDist (d := d) (t i.castSucc) (t i.succ) :=
          add_le_add le_rfl (ih t)
        _ = (∑ i : Fin (n + 1), oneDiskEDist (d := d) (t i.castSucc) (t i.succ)) +
            oneDiskEDist (d := d) (t (Fin.last (n + 1))) (s (Fin.last (n + 2))) := by
          rw [oneDiskEDist_comm (d := d) (s (Fin.last (n + 2))) (t (Fin.last (n + 1))),
            add_comm]

/-- Reversing actual chain endpoints and taking the original infima gives symmetry. -/
theorem kobayashiEDist_comm (p q : M) :
    kobayashiEDist (d := d) p q = kobayashiEDist (d := d) q p := by
  have hle (p q : M) : kobayashiEDist (d := d) q p ≤ kobayashiEDist (d := d) p q := by
    conv_rhs => unfold kobayashiEDist
    refine le_iInf fun n => ?_
    conv_rhs => unfold finiteChainEDist
    refine le_iInf fun s => le_iInf fun h0 => le_iInf fun hq => ?_
    simpa only [h0, hq] using! kobayashiEDist_reverse_le_chain (d := d) n s
  exact le_antisymm (hle q p) (hle p q)

private theorem kobayashiEDist_le_add_chain (p : M) :
    ∀ (n : ℕ) (s : Fin (n + 2) → M),
      kobayashiEDist (d := d) p (s (Fin.last (n + 1))) ≤
        kobayashiEDist (d := d) p (s 0) +
          ∑ i : Fin (n + 1), oneDiskEDist (d := d) (s i.castSucc) (s i.succ) := by
  intro n
  induction n with
  | zero =>
      intro s
      rw [Fin.sum_univ_one]
      change kobayashiEDist (d := d) p (s 1) ≤
        kobayashiEDist (d := d) p (s 0) + oneDiskEDist (d := d) (s 0) (s 1)
      exact kobayashiEDist_append_one_le (d := d) p (s 0) (s 1)
  | succ n ih =>
      intro s
      let t : Fin (n + 2) → M := fun i => s i.castSucc
      rw [Fin.sum_univ_castSucc]
      change kobayashiEDist (d := d) p (s (Fin.last (n + 2))) ≤
        kobayashiEDist (d := d) p (t 0) +
          ((∑ i : Fin (n + 1), oneDiskEDist (d := d) (t i.castSucc) (t i.succ)) +
            oneDiskEDist (d := d) (t (Fin.last (n + 1))) (s (Fin.last (n + 2))))
      calc
        kobayashiEDist (d := d) p (s (Fin.last (n + 2))) ≤
            kobayashiEDist (d := d) p (t (Fin.last (n + 1))) +
              oneDiskEDist (d := d) (t (Fin.last (n + 1))) (s (Fin.last (n + 2))) :=
          kobayashiEDist_append_one_le (d := d) _ _ _
        _ ≤ (kobayashiEDist (d := d) p (t 0) +
            ∑ i : Fin (n + 1), oneDiskEDist (d := d) (t i.castSucc) (t i.succ)) +
              oneDiskEDist (d := d) (t (Fin.last (n + 1))) (s (Fin.last (n + 2))) :=
          add_le_add (ih t) le_rfl
        _ = kobayashiEDist (d := d) p (t 0) +
            ((∑ i : Fin (n + 1), oneDiskEDist (d := d) (t i.castSucc) (t i.succ)) +
              oneDiskEDist (d := d) (t (Fin.last (n + 1))) (s (Fin.last (n + 2)))) :=
          add_assoc _ _ _

/-- The original extended chain infimum satisfies the full triangle inequality. -/
theorem kobayashiEDist_triangle (p q r : M) :
    kobayashiEDist (d := d) p r ≤
      kobayashiEDist (d := d) p q + kobayashiEDist (d := d) q r := by
  change kobayashiEDist (d := d) p r ≤
    kobayashiEDist (d := d) p q + (⨅ n : ℕ, finiteChainEDist (d := d) n q r)
  rw [ENNReal.add_iInf]
  refine le_iInf fun n => ?_
  conv_rhs =>
    unfold finiteChainEDist
    simp only [ENNReal.add_iInf]
  refine le_iInf fun s => le_iInf fun h0 => le_iInf fun hr => ?_
  simpa only [h0, hr] using! kobayashiEDist_le_add_chain (d := d) p n s

/-- The faithful real expression has the four pseudodistance axioms on the original
connected manifold; finiteness is proved before the additive conversion. -/
theorem kobayashiEDist_toReal_pseudodistance_axioms [ConnectedSpace M] :
    (∀ p q : M, 0 ≤ (kobayashiEDist (d := d) p q).toReal) ∧
      (∀ p : M, (kobayashiEDist (d := d) p p).toReal = 0) ∧
      (∀ p q : M, (kobayashiEDist (d := d) p q).toReal =
        (kobayashiEDist (d := d) q p).toReal) ∧
      (∀ p q r : M, (kobayashiEDist (d := d) p r).toReal ≤
        (kobayashiEDist (d := d) p q).toReal + (kobayashiEDist (d := d) q r).toReal) := by
  have hfinite (p q : M) : kobayashiEDist (d := d) p q ≠ ⊤ :=
    kobayashiEDist_ne_top (d := d) p q
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p q
    exact ENNReal.toReal_nonneg
  · intro p
    simp only [kobayashiEDist_self, ENNReal.toReal_zero]
  · intro p q
    exact congrArg ENNReal.toReal (kobayashiEDist_comm (d := d) p q)
  · intro p q r
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinite p q, hfinite q r⟩)
      (kobayashiEDist_triangle (d := d) p q r)
    simpa only [ENNReal.toReal_add (hfinite p q) (hfinite q r)] using h

end LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore
