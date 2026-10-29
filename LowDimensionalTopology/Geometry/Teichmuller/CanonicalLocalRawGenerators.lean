module

public import LowDimensionalTopology.Geometry.Teichmuller.AmbientFirstBookMatrices
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalLastPairRational
public import LowDimensionalTopology.Geometry.Teichmuller.FrickeRawWordTrace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Order.OrderClosed

/-!
# A local ambient raw family for the SAME ordered canonical generators

The first pairs retain the literal six-entry book order. The final pair uses
one CONSTANT sign of the prefix, selected at the chosen actual model. Only
entrywise analyticity at that point is asserted; nearby actual models agree
up to explicit nonzero scalar factors. No analytic model choice is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Matrix.Norms.Elementwise Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation NormalizedCanonicalFuchsianModel Filter

variable {g : ℕ}

def ambientFirstCommutatorPrefix (v : Fin (6 * g - 6) → ℝ) : LastPairRawMatrix :=
  (List.ofFn fun i : Fin (g - 1) =>
    ambientFirstBookMatrix v i 0 * ambientFirstBookMatrix v i 1 *
      Matrix.adjugate (ambientFirstBookMatrix v i 0) *
        Matrix.adjugate (ambientFirstBookMatrix v i 1)).prod

def ambientCanonicalRaw (epsilon : ℝ)
    (v : Fin (6 * g - 6) → ℝ) (d : Edge g) : LastPairRawMatrix :=
  if h : d.1.val < g - 1 then ambientFirstBookMatrix v ⟨d.1.val, h⟩ d.2
  else if d.2 = 0 then lastPairAlphaRaw (epsilon • ambientFirstCommutatorPrefix v)
  else lastPairBetaRaw (epsilon • ambientFirstCommutatorPrefix v)

private theorem rawMul_entry_analyticAt
    (A B : (Fin (6 * g - 6) → ℝ) → LastPairRawMatrix)
    (v : Fin (6 * g - 6) → ℝ)
    (hA : ∀ i j, AnalyticAt ℝ (fun w => A w i j) v)
    (hB : ∀ i j, AnalyticAt ℝ (fun w => B w i j) v) :
    ∀ i j, AnalyticAt ℝ (fun w => (A w * B w) i j) v := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hA i 0).mul (hB 0 j)).add ((hA i 1).mul (hB 1 j))

private theorem rawAdj_entry_analyticAt
    (A : (Fin (6 * g - 6) → ℝ) → LastPairRawMatrix)
    (v : Fin (6 * g - 6) → ℝ)
    (hA : ∀ i j, AnalyticAt ℝ (fun w => A w i j) v) :
    ∀ i j, AnalyticAt ℝ (fun w => Matrix.adjugate (A w) i j) v := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using hA 1 1
  · simp only [Matrix.adjugate_fin_two, Matrix.of_apply]
    change AnalyticAt ℝ (fun w => -A w 0 1) v
    exact (hA 0 1).neg
  · simp only [Matrix.adjugate_fin_two, Matrix.of_apply]
    change AnalyticAt ℝ (fun w => -A w 1 0) v
    exact (hA 1 0).neg
  · simpa [Matrix.adjugate_fin_two] using hA 0 0

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m : MarkedRiemannSurface.{0, 0} R}

def canonicalPrefixSL (P : NormalizedCanonicalFuchsianModel hg e m) : RealSL :=
  (List.ofFn fun i : Fin (g - 1) => LiZhongQC.commutatorSL
    (P.matrices (firstBookIndex i, 0)) (P.matrices (firstBookIndex i, 1))).prod

/-- The prefix is EXACTLY the original SL prefix at every actual model, not
merely an unspecified scalar multiple. All positive-c signs cancel. -/
theorem ambientFirstCommutatorPrefix_model
    (P : NormalizedCanonicalFuchsianModel hg e m) :
    ambientFirstCommutatorPrefix (flattenFirstBookData P.firstBookCoordinates) =
      (canonicalPrefixSL P).val := by
  have hi (i : Fin (g - 1)) :
      ambientFirstBookMatrix (flattenFirstBookData P.firstBookCoordinates) i 0 *
        ambientFirstBookMatrix (flattenFirstBookData P.firstBookCoordinates) i 1 *
        Matrix.adjugate
          (ambientFirstBookMatrix (flattenFirstBookData P.firstBookCoordinates) i 0) *
        Matrix.adjugate
          (ambientFirstBookMatrix (flattenFirstBookData P.firstBookCoordinates) i 1) =
      (LiZhongQC.commutatorSL (P.matrices (firstBookIndex i, 0))
        (P.matrices (firstBookIndex i, 1))).val := by
    rw [ambientFirstBookMatrix_model, ambientFirstBookMatrix_model]
    have h := congrArg (fun A : RealSL => A.val)
      (LiZhongQC.s27f_comm_pm (P.firstBookMatrix_eq_or_neg i 0)
        (P.firstBookMatrix_eq_or_neg i 1))
    simpa only [LiZhongQC.commutatorSL, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv] using h
  unfold ambientFirstCommutatorPrefix canonicalPrefixSL
  rw [show (List.ofFn fun i : Fin (g - 1) =>
      ambientFirstBookMatrix (flattenFirstBookData P.firstBookCoordinates) i 0 *
        ambientFirstBookMatrix (flattenFirstBookData P.firstBookCoordinates) i 1 *
        Matrix.adjugate
          (ambientFirstBookMatrix (flattenFirstBookData P.firstBookCoordinates) i 0) *
        Matrix.adjugate
          (ambientFirstBookMatrix (flattenFirstBookData P.firstBookCoordinates) i 1)) =
      List.ofFn (fun i : Fin (g - 1) =>
        (LiZhongQC.commutatorSL (P.matrices (firstBookIndex i, 0))
          (P.matrices (firstBookIndex i, 1))).val) from
      congrArg List.ofFn (funext hi)]
  simpa only [List.map_ofFn, Function.comp_def,
    Matrix.SpecialLinearGroup.coeMonoidHom_apply] using
    (map_list_prod (Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := ℝ))
      (List.ofFn fun i : Fin (g - 1) => LiZhongQC.commutatorSL
        (P.matrices (firstBookIndex i, 0)) (P.matrices (firstBookIndex i, 1)))).symm

theorem ambientFirstCommutatorPrefix_entry_analyticAt_model
    (P : NormalizedCanonicalFuchsianModel hg e m) :
    ∀ i j, AnalyticAt ℝ (fun v => ambientFirstCommutatorPrefix v i j)
      (flattenFirstBookData P.firstBookCoordinates) := by
  let v0 := flattenFirstBookData P.firstBookCoordinates
  let C (v : Fin (6 * g - 6) → ℝ) (i : Fin (g - 1)) :=
    ambientFirstBookMatrix v i 0 * ambientFirstBookMatrix v i 1 *
      Matrix.adjugate (ambientFirstBookMatrix v i 0) *
        Matrix.adjugate (ambientFirstBookMatrix v i 1)
  have hF (i : Fin (g - 1)) (b : Fin 2) (r s : Fin 2) :
      AnalyticAt ℝ (fun v => ambientFirstBookMatrix v i b r s) v0 :=
    analyticAt_pi_iff.mp
      (analyticAt_pi_iff.mp (ambientFirstBookMatrix_analyticAt_model P i b) r) s
  have hC (i : Fin (g - 1)) : ∀ r s, AnalyticAt ℝ (fun v => C v i r s) v0 :=
    rawMul_entry_analyticAt _ _ v0
      (rawMul_entry_analyticAt _ _ v0
        (rawMul_entry_analyticAt _ _ v0 (hF i 0) (hF i 1))
        (rawAdj_entry_analyticAt _ v0 (hF i 0)))
      (rawAdj_entry_analyticAt _ v0 (hF i 1))
  have hL (L : List (Fin (g - 1))) :
      ∀ r s, AnalyticAt ℝ (fun v => (L.map (C v)).prod r s) v0 := by
    induction L with
    | nil => intro r s; exact analyticAt_const
    | cons i L ih =>
        intro r s
        simpa only [List.map_cons, List.prod_cons] using
          rawMul_entry_analyticAt (fun v => C v i)
            (fun v => (L.map (C v)).prod) v0 (hC i) ih r s
  simpa only [List.map_ofFn, Function.comp_def, ambientFirstCommutatorPrefix, C, v0] using
    hL (List.ofFn fun i : Fin (g - 1) => i)

/-- One concrete ambient family works for EVERY nearby actual model. The
only existing unproved input is actual last-pair axis alternation. -/
theorem exists_canonicalLocalRawGenerators
    (P : NormalizedCanonicalFuchsianModel hg e m)
    (hP : Unproved.Teichmuller.CanonicalLastPairAxisAlternation P) :
    ∃ A : (Fin (6 * g - 6) → ℝ) → Edge g → LastPairRawMatrix,
      (∀ d i j, AnalyticAt ℝ (fun v => A v d i j)
        (flattenFirstBookData P.firstBookCoordinates)) ∧
      ∀ᶠ v in 𝓝 (flattenFirstBookData P.firstBookCoordinates),
        ∀ (n : MarkedRiemannSurface.{0, 0} R)
          (Q : NormalizedCanonicalFuchsianModel hg e n),
          Unproved.Teichmuller.CanonicalLastPairAxisAlternation Q →
          flattenFirstBookData Q.firstBookCoordinates = v →
          ∀ d, ∃ c : ℝ, c ≠ 0 ∧ A v d = c • (Q.matrices d).val := by
  let v0 := flattenFirstBookData P.firstBookCoordinates
  let eta := canonicalPrefixSL P
  let gamma := P.matrices (finalHandle hg, 0)
  let delta := P.matrices (finalHandle hg, 1)
  let epsilon : ℝ := if 0 < eta 1 1 then 1 else -1
  let B (v : Fin (6 * g - 6) → ℝ) := epsilon • ambientFirstCommutatorPrefix v
  have hrel : eta * LiZhongQC.commutatorSL gamma delta = 1 ∨
      eta * LiZhongQC.commutatorSL gamma delta = -1 :=
    P.firstCommutatorProduct_mul_final_commutator
  have hM := LiZhongQC.s27t_comm_inv_11 gamma delta P.final_beta_diagonal_expanding hP
  have heta : eta 1 1 ≠ 0 := by
    rcases LiZhongQC.s27t_eta_eq hrel with h | h
    · rw [h]
      linarith
    · rw [h, LiZhongQC.s27t_neg_apply]
      linarith
  have hB0 : B v0 = ((LiZhongQC.commutatorSL gamma delta)⁻¹).val := by
    dsimp only [B, v0]
    rw [ambientFirstCommutatorPrefix_model]
    have hs := congrArg (fun A : RealSL => A.val)
      (lastPair_inverse_commutator_from_prefix eta gamma delta
        P.final_beta_diagonal_expanding hP hrel)
    by_cases hp : 0 < eta 1 1
    · simpa only [epsilon, hp, ite_true, one_smul] using hs.symm
    · simpa only [epsilon, hp, ite_false, neg_one_smul,
        Matrix.SpecialLinearGroup.coe_neg] using hs.symm
  have he := ambientFirstCommutatorPrefix_entry_analyticAt_model P
  have hB : AnalyticAt ℝ B v0 := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    exact analyticAt_const.mul (he i j)
  have hr := lastPairRational_recovery gamma delta P.final_beta_diagonal_expanding
    P.finalAlpha_fixes_one hP
  rw [← LiZhongQC.s27t_comm_inv gamma delta] at hr
  have hlast : AnalyticAt ℝ (fun v => lastPairAlphaRaw (B v)) v0 ∧
      AnalyticAt ℝ (fun v => lastPairBetaRaw (B v)) v0 := by
    have ha := lastPairRaw_analyticAt _ hr.1.1 hr.1.2.1 hr.1.2.2.1 hr.1.2.2.2
    rw [← hB0] at ha
    exact ⟨ha.1.comp hB, ha.2.comp hB⟩
  refine ⟨ambientCanonicalRaw (g := g) epsilon, ?_, ?_⟩
  · rintro ⟨i, b⟩ r s
    by_cases hi : i.val < g - 1
    · simp only [ambientCanonicalRaw, dite_eq_left hi]
      exact analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (ambientFirstBookMatrix_analyticAt_model P ⟨i.val, hi⟩ b) r) s
    · by_cases hb : b = 0
      · simp only [ambientCanonicalRaw, dite_eq_right hi, hb, ite_true]
        exact analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hlast.1 r) s
      · simp only [ambientCanonicalRaw, dite_eq_right hi, hb, ite_false]
        exact analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hlast.2 r) s
  · have hcont := (he 1 1).continuousAt
    have hsign : ∀ᶠ v in 𝓝 v0,
        (0 < ambientFirstCommutatorPrefix v 1 1 ↔ 0 < eta 1 1) := by
      by_cases hp : 0 < eta 1 1
      · have hp0 : 0 < ambientFirstCommutatorPrefix v0 1 1 := by
          rw [ambientFirstCommutatorPrefix_model]
          exact hp
        filter_upwards [continuousAt_const.eventually_lt hcont hp0] with v hv
        exact iff_of_true hv hp
      · have hn : eta 1 1 < 0 := lt_of_le_of_ne (le_of_not_gt hp) heta
        have hn0 : ambientFirstCommutatorPrefix v0 1 1 < 0 := by
          rw [ambientFirstCommutatorPrefix_model]
          exact hn
        filter_upwards [hcont.eventually_lt continuousAt_const hn0] with v hv
        exact iff_of_false (not_lt_of_gt hv) hp
    filter_upwards [hsign] with v hv n Q hQ hcoord
    let gammaQ := Q.matrices (finalHandle hg, 0)
    let deltaQ := Q.matrices (finalHandle hg, 1)
    have hrelQ : canonicalPrefixSL Q * LiZhongQC.commutatorSL gammaQ deltaQ = 1 ∨
        canonicalPrefixSL Q * LiZhongQC.commutatorSL gammaQ deltaQ = -1 :=
      Q.firstCommutatorProduct_mul_final_commutator
    have hsignQ : (0 < canonicalPrefixSL Q 1 1) ↔ 0 < eta 1 1 := by
      rw [← hcoord, ambientFirstCommutatorPrefix_model] at hv
      exact hv
    have hBQ : B v = ((LiZhongQC.commutatorSL gammaQ deltaQ)⁻¹).val := by
      dsimp only [B]
      rw [← hcoord, ambientFirstCommutatorPrefix_model]
      have hs := congrArg (fun A : RealSL => A.val)
        (lastPair_inverse_commutator_from_prefix (canonicalPrefixSL Q) gammaQ deltaQ
          Q.final_beta_diagonal_expanding hQ hrelQ)
      by_cases hp : 0 < eta 1 1
      · have hq := hsignQ.mpr hp
        simpa only [epsilon, hp, hq, ite_true, one_smul] using hs.symm
      · have hq : ¬0 < canonicalPrefixSL Q 1 1 := fun h => hp (hsignQ.mp h)
        simpa only [epsilon, hp, hq, ite_false, neg_one_smul,
          Matrix.SpecialLinearGroup.coe_neg] using hs.symm
    have hrQ := lastPairRational_recovery gammaQ deltaQ Q.final_beta_diagonal_expanding
      Q.finalAlpha_fixes_one hQ
    rw [← LiZhongQC.s27t_comm_inv gammaQ deltaQ, ← hBQ] at hrQ
    rintro ⟨i, b⟩
    by_cases hi : i.val < g - 1
    · have hindex : firstBookIndex (⟨i.val, hi⟩ : Fin (g - 1)) = i := Fin.ext rfl
      simpa only [ambientCanonicalRaw, dite_eq_left hi, hindex, hcoord] using
        ambientFirstBookMatrix_model_scale Q ⟨i.val, hi⟩ b
    · have hindex : i = finalHandle hg := by
        apply Fin.ext
        change i.val = g - 1
        omega
      subst i
      fin_cases b
      · refine ⟨(gammaQ 1 0)⁻¹, inv_ne_zero hrQ.2.2.2.1, ?_⟩
        simp only [ambientCanonicalRaw, dite_eq_right hi]
        change lastPairAlphaRaw (B v) = (gammaQ 1 0)⁻¹ • gammaQ.val
        exact hrQ.2.1
      · refine ⟨deltaQ 0 0, hrQ.2.2.2.2, ?_⟩
        simp only [ambientCanonicalRaw, dite_eq_right hi]
        change lastPairBetaRaw (B v) = deltaQ 0 0 • deltaQ.val
        exact hrQ.2.2.1

end LowDimensionalTopology.Geometry.Teichmuller
