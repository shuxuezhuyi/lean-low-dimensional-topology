module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalGlobalFricke
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Matrix.Normed

/-!
# Ambient rational matrices in the literal six-entry Fricke order

The order is EXACTLY `(a,c,d,a',c',d')`, transported by the existing
`bookIndexEquiv`; no replacement coordinate equivalence is introduced.
The formulas make sense on the ambient finite real vector space. At every
actual normalized model they recover its genuine positive-c first matrices.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Matrix.Norms.Elementwise

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation NormalizedCanonicalFuchsianModel

variable {g : ℕ}

/-- Read one triple from the existing ascending-handle six-entry coordinates. -/
def ambientFirstBookTriple (v : Fin (6 * g - 6) → ℝ)
    (i : Fin (g - 1)) (b : Fin 2) : ℝ × ℝ × ℝ :=
  if b = 0 then
    (v (bookIndexEquiv g (i, 0)), v (bookIndexEquiv g (i, 1)),
      v (bookIndexEquiv g (i, 2)))
  else
    (v (bookIndexEquiv g (i, 3)), v (bookIndexEquiv g (i, 4)),
      v (bookIndexEquiv g (i, 5)))

/-- The same determinant-one reconstruction formula, without a subtype domain. -/
def ambientFirstBookMatrix (v : Fin (6 * g - 6) → ℝ)
    (i : Fin (g - 1)) (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  let u := ambientFirstBookTriple v i b
  !![u.1, (u.1 * u.2.2 - 1) / u.2.1; u.2.1, u.2.2]

theorem ambientFirstBookTriple_analyticAt (v : Fin (6 * g - 6) → ℝ)
    (i : Fin (g - 1)) (b : Fin 2) :
    AnalyticAt ℝ (fun w => ambientFirstBookTriple w i b) v := by
  have hid : AnalyticAt ℝ (fun w : Fin (6 * g - 6) → ℝ => w) v := analyticAt_id
  have he (j : Fin (6 * g - 6)) :
      AnalyticAt ℝ (fun w : Fin (6 * g - 6) → ℝ => w j) v :=
    analyticAt_pi_iff.mp hid j
  fin_cases b
  · exact (he (bookIndexEquiv g (i, 0))).prod
      ((he (bookIndexEquiv g (i, 1))).prod (he (bookIndexEquiv g (i, 2))))
  · exact (he (bookIndexEquiv g (i, 3))).prod
      ((he (bookIndexEquiv g (i, 4))).prod (he (bookIndexEquiv g (i, 5))))

/-- Only the actual lower-left coordinate must be nonzero. -/
theorem ambientFirstBookMatrix_analyticAt (v : Fin (6 * g - 6) → ℝ)
    (i : Fin (g - 1)) (b : Fin 2)
    (hc : (ambientFirstBookTriple v i b).2.1 ≠ 0) :
    AnalyticAt ℝ (fun w => ambientFirstBookMatrix w i b) v := by
  have ht := ambientFirstBookTriple_analyticAt v i b
  have ha : AnalyticAt ℝ (fun w => (ambientFirstBookTriple w i b).1) v :=
    analyticAt_fst.comp ht
  have hcd := analyticAt_snd.comp ht
  have hcf : AnalyticAt ℝ (fun w => (ambientFirstBookTriple w i b).2.1) v :=
    analyticAt_fst.comp hcd
  have hd : AnalyticAt ℝ (fun w => (ambientFirstBookTriple w i b).2.2) v :=
    analyticAt_snd.comp hcd
  apply AnalyticAt.pi
  intro r
  apply AnalyticAt.pi
  intro s
  fin_cases r <;> fin_cases s
  · exact ha
  · exact ((ha.mul hd).sub analyticAt_const).div hcf hc
  · exact hcf
  · exact hd

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m : MarkedRiemannSurface.{0, 0} R}

/-- This identity retains the existing flattening equivalence and all six slots. -/
theorem ambientFirstBookTriple_model (P : NormalizedCanonicalFuchsianModel hg e m)
    (i : Fin (g - 1)) (b : Fin 2) :
    ambientFirstBookTriple (flattenFirstBookData P.firstBookCoordinates) i b =
      bookMatrixCoordinates (P.firstBookMatrix i b) := by
  fin_cases b <;>
    simp [ambientFirstBookTriple, flattenFirstBookData, sixBookEntries,
      NormalizedCanonicalFuchsianModel.firstBookCoordinates, bookMatrixCoordinates]

/-- Exact agreement holds for EVERY actual canonical model, globally. -/
theorem ambientFirstBookMatrix_model (P : NormalizedCanonicalFuchsianModel hg e m)
    (i : Fin (g - 1)) (b : Fin 2) :
    ambientFirstBookMatrix (flattenFirstBookData P.firstBookCoordinates) i b =
      (P.firstBookMatrix i b).val := by
  unfold ambientFirstBookMatrix
  rw [ambientFirstBookTriple_model]
  change (matrixFromBookCoordinates
    ⟨bookMatrixCoordinates (P.firstBookMatrix i b), P.firstBookMatrix_lowerLeft_pos i b⟩).val = _
  exact congrArg (fun A : RealSL => A.val)
    (matrixFromBook_bookCoordinates (P.firstBookMatrix i b)
      (P.firstBookMatrix_lowerLeft_pos i b))

/-- Actual geometry proves the sole denominator hypothesis at every model point. -/
theorem ambientFirstBookMatrix_analyticAt_model
    (P : NormalizedCanonicalFuchsianModel hg e m) (i : Fin (g - 1)) (b : Fin 2) :
    AnalyticAt ℝ (fun w => ambientFirstBookMatrix w i b)
      (flattenFirstBookData P.firstBookCoordinates) := by
  apply ambientFirstBookMatrix_analyticAt
  rw [ambientFirstBookTriple_model]
  exact (P.firstBookMatrix_lowerLeft_pos i b).ne'

/-- The raw first matrix differs from the ORIGINAL given SL lift only by a
nonzero scalar, with no assumption about analytic dependence of that lift. -/
theorem ambientFirstBookMatrix_model_scale
    (P : NormalizedCanonicalFuchsianModel hg e m) (i : Fin (g - 1)) (b : Fin 2) :
    ∃ c : ℝ, c ≠ 0 ∧
      ambientFirstBookMatrix (flattenFirstBookData P.firstBookCoordinates) i b =
        c • (P.matrices (firstBookIndex i, b)).val := by
  rw [ambientFirstBookMatrix_model]
  rcases P.firstBookMatrix_eq_or_neg i b with h | h
  · refine ⟨1, one_ne_zero, ?_⟩
    simp only [h, one_smul]
  · refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ?_⟩
    simp only [h, Matrix.SpecialLinearGroup.coe_neg, neg_one_smul]

/-- Identification with the genuine literal native Fricke coordinates. -/
theorem finiteFrickeCoordinates_eq_model
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (P : NormalizedCanonicalFuchsianModel hg e m) :
    finiteFrickeCoordinates hA (TeichmullerSpace.mk m) =
      flattenFirstBookData P.firstBookCoordinates := by
  change flattenFirstBookData (groupedFrickeCoordinates hA (TeichmullerSpace.mk m)) = _
  rw [groupedFrickeCoordinates_eq_model hA P]

end LowDimensionalTopology.Geometry.Teichmuller
