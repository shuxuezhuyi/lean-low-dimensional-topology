/- Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegion.CanonicalRegionFormulas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section

noncomputable section

open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The radial half-width of a hyperbolic collar in terms of its core length. -/
def collarHalfWidth (l : ℝ) : ℝ :=
  Real.log ((Real.exp (l / 2) + 1) / (Real.exp (l / 2) - 1))

/-- A positive core length gives a strictly positive half-width. -/
theorem collarHalfWidth_pos {l : ℝ} (hl : 0 < l) : 0 < collarHalfWidth l := by
  have hq : 1 < Real.exp (l / 2) := Real.one_lt_exp_iff.mpr (by linarith)
  have hden : 0 < Real.exp (l / 2) - 1 := by linarith
  unfold collarHalfWidth
  apply Real.log_pos
  apply (lt_div_iff₀ hden).mpr
  linarith

/-- The half-width satisfies the exact hyperbolic sine product identity. -/
theorem sinh_collarHalfWidth_mul {l : ℝ} (hl : 0 < l) :
    Real.sinh (collarHalfWidth l) * Real.sinh (l / 2) = 1 := by
  let q := Real.exp (l / 2)
  have hq : 1 < q := Real.one_lt_exp_iff.mpr (by linarith)
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q - 1 := by linarith
  have hqp : 0 < q + 1 := by linarith
  change Real.sinh (Real.log ((q + 1) / (q - 1))) * Real.sinh (l / 2) = 1
  rw [Real.sinh_log (div_pos hqp hqm), Real.sinh_eq, Real.exp_neg]
  change (((q + 1) / (q - 1) - ((q + 1) / (q - 1))⁻¹) / 2) *
    ((q - q⁻¹) / 2) = 1
  field_simp [hq0.ne', hqm.ne', hqp.ne']
  ring

/-- The hyperbolic sine of the half-width is the reciprocal core factor. -/
theorem sinh_collarHalfWidth {l : ℝ} (hl : 0 < l) :
    Real.sinh (collarHalfWidth l) = 1 / Real.sinh (l / 2) := by
  have hs : 0 < Real.sinh (l / 2) := Real.sinh_pos_iff.mpr (by linarith)
  exact (eq_div_iff hs.ne').mpr (sinh_collarHalfWidth_mul hl)

/-- The distance half-width is equivalent to the strict sine strip inequality. -/
theorem lt_collarHalfWidth_iff {l : ℝ} (hl : 0 < l) (d : ℝ) :
    d < collarHalfWidth l ↔ Real.sinh d * Real.sinh (l / 2) < 1 := by
  have hs : 0 < Real.sinh (l / 2) := Real.sinh_pos_iff.mpr (by linarith)
  calc
    d < collarHalfWidth l ↔ Real.sinh d < Real.sinh (collarHalfWidth l) :=
      Real.sinh_lt_sinh.symm
    _ ↔ Real.sinh d < 1 / Real.sinh (l / 2) := by rw [sinh_collarHalfWidth hl]
    _ ↔ Real.sinh d * Real.sinh (l / 2) < 1 := lt_div_iff₀ hs

/-- The genuine hyperbolic canonical region is the tube around its actual axis
with half-width determined by its actual translation infimum. -/
theorem canonical_region_hyperbolic_tube (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusHyperbolic (realSLMobius A)) :
    let ht := (realSLMobius_hyperbolic_iff A hA.1.1).mp hA
    let L := hHyperbolicAxis A hA.1.1 ht
    hCanonicalRegion A =
      {z : ℍ | L.pointDist z < collarHalfWidth (hTranslationLength (hSLIsometry A))} := by
  dsimp only
  have hT : 0 < hTranslationLength (hSLIsometry A) :=
    hHyperbolic_translationLength_pos A hA.1.1
      ((realSLMobius_hyperbolic_iff A hA.1.1).mp hA)
  rw [(canonical_region_hyperbolic A hA).1]
  ext z
  exact (lt_collarHalfWidth_iff hT _).symm

end LowDimensionalTopology.Geometry.Hyperbolic
