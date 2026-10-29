module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalProjectiveRelator
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

/-!
# A fixed source word evaluated in raw canonical matrices

Negative letters use the adjugate, a polynomial operation. This definition is
only a finite expression for a FIXED word; it is not a homomorphism on arbitrary
raw matrices. In dimension two, nonzero scalar multiples of actual SL letters
give the same `trace² / determinant` invariant for this expression.

-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

abbrev FrickeRawWordMatrix := Matrix (Fin 2) (Fin 2) ℝ

def frickeRawWordEval {g : ℕ} (w : FreeGroup (StandardLabels g))
    (A : StandardLabels g → FrickeRawWordMatrix) : FrickeRawWordMatrix :=
  (w.toWord.map fun b => cond b.2 (A b.1) (Matrix.adjugate (A b.1))).prod

def frickeRawWordTraceInvariant {g : ℕ} (w : FreeGroup (StandardLabels g))
    (A : StandardLabels g → FrickeRawWordMatrix) : ℝ :=
  Matrix.trace (frickeRawWordEval w A) ^ 2 / (frickeRawWordEval w A).det

/-- Only scalar entrywise analyticity is needed, so no matrix normed-ring
instance or off-image group homomorphism enters the argument. -/
theorem frickeRawWordEval_entry_analyticAt {g d : ℕ}
    (w : FreeGroup (StandardLabels g))
    (A : (Fin d → ℝ) → StandardLabels g → FrickeRawWordMatrix) (x : Fin d → ℝ)
    (hA : ∀ s i j, AnalyticAt ℝ (fun t => A t s i j) x) :
    ∀ i j, AnalyticAt ℝ (fun t => frickeRawWordEval w (A t) i j) x := by
  have hb (b : StandardLabels g × Bool) (i j : Fin 2) :
      AnalyticAt ℝ
        (fun t => (cond b.2 (A t b.1) (Matrix.adjugate (A t b.1))) i j) x := by
    rcases b with ⟨s, b⟩
    cases b
    · fin_cases i <;> fin_cases j
      · simpa [Matrix.adjugate_fin_two] using hA s 1 1
      · change AnalyticAt ℝ (fun t => Matrix.adjugate (A t s) 0 1) x
        simp only [Matrix.adjugate_fin_two, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        change AnalyticAt ℝ (fun t => -A t s 0 1) x
        exact (hA s 0 1).neg
      · change AnalyticAt ℝ (fun t => Matrix.adjugate (A t s) 1 0) x
        simp only [Matrix.adjugate_fin_two, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        change AnalyticAt ℝ (fun t => -A t s 1 0) x
        exact (hA s 1 0).neg
      · simpa [Matrix.adjugate_fin_two] using hA s 0 0
    · exact hA s i j
  have hL (L : List (StandardLabels g × Bool)) :
      ∀ i j, AnalyticAt ℝ
        (fun t => (L.map fun b =>
          cond b.2 (A t b.1) (Matrix.adjugate (A t b.1))).prod i j) x := by
    induction L with
    | nil =>
        intro i j
        exact analyticAt_const
    | cons b L ih =>
        intro i j
        simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two]
        exact ((hb b i 0).mul (ih 0 j)).add ((hb b i 1).mul (ih 1 j))
  exact hL w.toWord

/-- A genuine analytic ambient germ exists wherever the evaluated determinant
is nonzero; the actual-model comparison below supplies that nonvanishing. -/
theorem frickeRawWordTraceInvariant_analyticAt {g d : ℕ}
    (w : FreeGroup (StandardLabels g))
    (A : (Fin d → ℝ) → StandardLabels g → FrickeRawWordMatrix) (x : Fin d → ℝ)
    (hA : ∀ s i j, AnalyticAt ℝ (fun t => A t s i j) x)
    (hdet : (frickeRawWordEval w (A x)).det ≠ 0) :
    AnalyticAt ℝ (fun t => frickeRawWordTraceInvariant w (A t)) x := by
  have he := frickeRawWordEval_entry_analyticAt w A x hA
  have ht : AnalyticAt ℝ
      (fun t => frickeRawWordEval w (A t) 0 0 + frickeRawWordEval w (A t) 1 1) x := by
    exact (he 0 0).add (he 1 1)
  have hd : AnalyticAt ℝ
      (fun t => frickeRawWordEval w (A t) 0 0 * frickeRawWordEval w (A t) 1 1 -
        frickeRawWordEval w (A t) 0 1 * frickeRawWordEval w (A t) 1 0) x := by
    exact ((he 0 0).mul (he 1 1)).sub ((he 0 1).mul (he 1 0))
  have hx : frickeRawWordEval w (A x) 0 0 * frickeRawWordEval w (A x) 1 1 -
      frickeRawWordEval w (A x) 0 1 * frickeRawWordEval w (A x) 1 0 ≠ 0 := by
    simpa only [Matrix.det_fin_two] using hdet
  simp only [frickeRawWordTraceInvariant, Matrix.trace_fin_two, Matrix.det_fin_two]
  exact (ht.pow 2).div hd hx

/-- Compare the FIXED raw word with the SAME original special-linear lift.
Positive and negative letters both contribute the same scalar in dimension
two. No primitive word, replacement word, or arbitrary deck lift is chosen. -/
theorem frickeRawWordEval_eq_smul_lift {g : ℕ}
    (w : FreeGroup (StandardLabels g)) (A : StandardLabels g → FrickeRawWordMatrix)
    (S : StandardLabels g → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (c : StandardLabels g → ℝ) (hc : ∀ s, c s ≠ 0)
    (hA : ∀ s, A s = c s • (S s).val) :
    ∃ q : ℝ, q ≠ 0 ∧ frickeRawWordEval w A = q • (FreeGroup.lift S w).val := by
  let a (b : StandardLabels g × Bool) :=
    cond b.2 (A b.1) (Matrix.adjugate (A b.1))
  let s (b : StandardLabels g × Bool) := cond b.2 (S b.1) (S b.1)⁻¹
  have hb (b : StandardLabels g × Bool) : a b = c b.1 • (s b).val := by
    rcases b with ⟨i, b⟩
    cases b <;> simp [a, s, hA i, Matrix.adjugate_smul,
      Matrix.SpecialLinearGroup.coe_inv]
  have hL (L : List (StandardLabels g × Bool)) :
      ∃ q : ℝ, q ≠ 0 ∧ (L.map a).prod = q • ((L.map s).prod).val := by
    induction L with
    | nil => exact ⟨1, one_ne_zero, by simp⟩
    | cons b L ih =>
        obtain ⟨q, hq, hEq⟩ := ih
        refine ⟨c b.1 * q, mul_ne_zero (hc b.1) hq, ?_⟩
        simp only [List.map_cons, List.prod_cons, Matrix.SpecialLinearGroup.coe_mul]
        rw [hb, hEq, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  obtain ⟨q, hq, hEq⟩ := hL w.toWord
  have hw : (w.toWord.map s).prod = FreeGroup.lift S w := by
    simpa only [FreeGroup.mk_toWord] using
      (FreeGroup.lift_mk (f := S) (L := w.toWord)).symm
  refine ⟨q, hq, ?_⟩
  change (w.toWord.map a).prod = q • (FreeGroup.lift S w).val
  rw [← hw]
  exact hEq

theorem frickeRawWordTraceInvariant_eq_trace_sq {g : ℕ}
    (w : FreeGroup (StandardLabels g)) (A : StandardLabels g → FrickeRawWordMatrix)
    (S : StandardLabels g → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (c : StandardLabels g → ℝ) (hc : ∀ s, c s ≠ 0)
    (hA : ∀ s, A s = c s • (S s).val) :
    (frickeRawWordEval w A).det ≠ 0 ∧
      frickeRawWordTraceInvariant w A = Matrix.trace (FreeGroup.lift S w).val ^ 2 := by
  obtain ⟨q, hq, hEq⟩ := frickeRawWordEval_eq_smul_lift w A S c hc hA
  constructor
  · rw [hEq, Matrix.det_smul, Matrix.SpecialLinearGroup.det_coe]
    simpa only [Fintype.card_fin, mul_one] using pow_ne_zero 2 hq
  · unfold frickeRawWordTraceInvariant
    rw [hEq, Matrix.trace_smul, Matrix.det_smul, Matrix.SpecialLinearGroup.det_coe]
    simp only [Fintype.card_fin, smul_eq_mul, mul_one]
    field_simp [hq]

end LowDimensionalTopology.Geometry.Teichmuller
