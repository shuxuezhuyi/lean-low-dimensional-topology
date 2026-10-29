/-
Definition and analytic interface adapted from Wu Xiaobin's
Li-Zhong-QC-formalization, commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.AnalyticGeometric
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Absolute continuity on lines

The linewise condition is stated for arbitrary functions on a planar domain and
contains no joint continuity requirement. On each compact axis-parallel rectangle,
almost every horizontal and vertical restriction is absolutely continuous.
The source analytic predicate additionally includes continuity; its exact relation
to this condition is proved using the nullity of interval endpoints.
-/

@[expose] public section

open Set MeasureTheory Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Almost every horizontal and vertical restriction to every compact axis-parallel
rectangle in the domain is absolutely continuous. Joint continuity is not required. -/
def IsAbsolutelyContinuousOnLines (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∀ a b c d : ℝ, a < b → c < d → LiZhongQC.closedRect a b c d ⊆ D →
    (∀ᵐ (x : ℝ) ∂(volume.restrict (Icc a b)),
        AbsolutelyContinuousOnInterval (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) c d) ∧
      ∀ᵐ (y : ℝ) ∂(volume.restrict (Icc c d)),
        AbsolutelyContinuousOnInterval (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) a b

/-- The existing source ACL predicate is precisely continuity together with the
bare linewise condition. Its open exceptional-variable intervals give the same
almost-everywhere assertions as closed intervals because endpoints are null. -/
theorem source_isACL_iff_continuousOn_and_lines {f : ℂ → ℂ} {D : Set ℂ} :
    LiZhongQC.IsACL f D ↔ ContinuousOn f D ∧ IsAbsolutelyContinuousOnLines f D := by
  simp only [LiZhongQC.IsACL, IsAbsolutelyContinuousOnLines,
    MeasureTheory.restrict_Ioo_eq_restrict_Icc]

/-- An actual quasiconformal map satisfies the bare linewise condition. -/
theorem quasiconformal_isAbsolutelyContinuousOnLines
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : LiZhongQC.IsKQC f D K) :
    IsAbsolutelyContinuousOnLines f D :=
  (source_isACL_iff_continuousOn_and_lines.mp (LiZhongQC.thm9_1_isACL hf)).2

end LowDimensionalTopology.Geometry.Quasiconformal
