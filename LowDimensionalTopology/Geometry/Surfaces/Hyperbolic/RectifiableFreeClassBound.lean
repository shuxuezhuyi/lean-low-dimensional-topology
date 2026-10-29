module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableLoopNormalization
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.RectifiableDistance

/-!
# The source free-class minimum bounds every actual rectifiable lift

The original continuous BV lift may have a singular parameter. Its genuine
free homotopy to the lossless normalized Lipschitz loop supplies an admissible
source witness with exactly the original weighted arclength integral.
-/

public section
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane unitInterval ENNReal NNReal

namespace LowDimensionalTopology.Geometry.RectifiableCurve
open LowDimensionalTopology.Geometry.Hyperbolic

/-- Every actual continuous rectifiable lift of the given loop bounds its
source free-class minimum below. No absolute continuity or Lipschitz condition
is imposed on the original parameter. -/
theorem freeHomotopyLength_le_weightedLength
    {X : Type*} [TopologicalSpace X] (p : ℍ → X) (hp : Continuous p)
    (c : RectifiableCurve) (ha : c.a = 0) (hb : c.b = 1)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c.curve t).im)
    (α : LiZhongQC.Loop X)
    (hα : ∀ t : I, p ⟨c.curve t, hpos t t.property⟩ = α.2 t) :
    LiZhongQC.freeHomotopyLength p α ≤
      c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := by
  let ρ : ℂ → ℝ≥0∞ := fun ζ => ENNReal.ofReal (1 / ζ.im)
  have hρ : Measurable ρ := measurable_halfPlane_poincareDensity
  have hNorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 < (c.normalizedParam t).im := by
    have himage : c.normalizedParam '' Icc 0 1 = c.curve '' Icc c.a c.b :=
      c.normalizedCurve_closedTrace
    obtain ⟨s, hs, heq⟩ := himage ▸ (show c.normalizedParam t ∈
      c.normalizedParam '' Icc 0 1 from ⟨t, ht, rfl⟩)
    rw [← heq]
    exact hpos s (by simpa only [ha, hb] using hs)
  have hK : ∃ K : ℝ≥0, LipschitzOnWith K c.normalizedParam (Icc 0 1) :=
    ⟨_, c.normalizedParam_lipschitz.lipschitzOnWith⟩
  let e := LiZhongQC.s30a_pathOf c.normalizedParam hK hNorm
  have ht0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have ht1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have he0 : e 0 = (⟨c.curve 0, hpos 0 ht0⟩ : ℍ) := by
    apply UpperHalfPlane.ext
    change c.normalizedParam 0 = c.curve 0
    have h := c.normalizedCurve_endpoints.1
    change c.normalizedParam 0 = c.curve c.a at h
    rw [ha] at h
    exact h
  have he1 : e 1 = (⟨c.curve 1, hpos 1 ht1⟩ : ℍ) := by
    apply UpperHalfPlane.ext
    change c.normalizedParam 1 = c.curve 1
    have h := c.normalizedCurve_endpoints.2
    change c.normalizedParam 1 = c.curve c.b at h
    rw [hb] at h
    exact h
  have hclosed : p (e 1) = p (e 0) := by
    have hα0 := hα (0 : I)
    have hα1 := hα (1 : I)
    have heα0 : p (e 0) = α.2 (0 : I) := (congrArg p he0).trans hα0
    have heα1 : p (e 1) = α.2 (1 : I) := (congrArg p he1).trans hα1
    exact heα1.trans ((α.2.target.trans α.2.source.symm).trans heα0.symm)
  let β := LiZhongQC.s30a_projLoop p hp e hclosed
  have hβ (t : I) (h : 0 < (c.normalizedParam t).im) :
      p ⟨c.normalizedParam t, h⟩ = β.2 t := rfl
  have hhom : LiZhongQC.FreelyHomotopic α β :=
    freelyHomotopic_normalized_projection p hp c ha hb hpos α β hα hβ
  have hupper : LiZhongQC.poincareLengthLoop p β ≤ LiZhongQC.hypLength c.normalizedParam := by
    refine iInf₂_le c.normalizedParam ⟨hK, hNorm, ?_⟩
    intro t ht h
    calc
      p ⟨c.normalizedParam t, h⟩ = β.2 ⟨t, ht⟩ := rfl
      _ = β.2.extend t := (Path.extend_apply β.2 ht).symm
  have hlength : LiZhongQC.hypLength c.normalizedParam = c.normalizedCurve.rhoLength ρ := by
    unfold LiZhongQC.hypLength LiZhongQC.LRCurve.rhoLength
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    change ‖deriv c.normalizedParam t‖ₑ / ENNReal.ofReal (c.normalizedParam t).im =
      ENNReal.ofReal (1 / (c.normalizedParam t).im) * ‖deriv c.normalizedParam t‖ₑ
    rw [ENNReal.ofReal_div_of_pos (hNorm t (Ioo_subset_Icc_self ht)), ENNReal.ofReal_one]
    simp only [div_eq_mul_inv, one_mul, mul_comm]
  calc
    LiZhongQC.freeHomotopyLength p α ≤ LiZhongQC.poincareLengthLoop p β := iInf₂_le β hhom
    _ ≤ LiZhongQC.hypLength c.normalizedParam := hupper
    _ = c.normalizedCurve.rhoLength ρ := hlength
    _ = c.weightedLength ρ := c.normalizedCurve_rhoLength hρ

end LowDimensionalTopology.Geometry.RectifiableCurve
