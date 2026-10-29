module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.IntervalClockHomotopy
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableNormalizedLength

/-!
# A rectifiable projected loop is freely homotopic to its lossless normalization

The homotopy uses the actual cumulative variation clock. It therefore applies
to singular parametrizations, pauses, multiple traversals and constant curves.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane unitInterval

namespace LowDimensionalTopology.Geometry.RectifiableCurve
open LowDimensionalTopology.Geometry.Surfaces

/-- Original and normalized projected loops are joined by an actual continuous
cylinder. All points of the homotopy remain on the same arclength factor inside
the upper half-plane; equality of the two trace sets is not substituted for a
homotopy. -/
theorem freelyHomotopic_normalized_projection
    {X : Type*} [TopologicalSpace X] (p : ℍ → X) (hp : Continuous p)
    (c : RectifiableCurve) (ha : c.a = 0) (hb : c.b = 1)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c.curve t).im)
    (α β : LiZhongQC.Loop X)
    (hα : ∀ t : I, p ⟨c.curve t, hpos t t.property⟩ = α.2 t)
    (hβ : ∀ (t : I) (h : 0 < (c.normalizedParam t).im),
      p ⟨c.normalizedParam t, h⟩ = β.2 t) :
    LiZhongQC.FreelyHomotopic α β := by
  have hpar (t : I) : (t : ℝ) ∈ Icc c.a c.b := by
    simpa only [ha, hb] using t.property
  have hclockMem (t : I) : c.clock t ∈ Icc 0 c.euclideanLength := by
    rw [← c.clock_spec.2.2.2.2]
    exact ⟨t, hpar t, rfl⟩
  have hfactorpos (r : ℝ) (hr : r ∈ Icc 0 c.euclideanLength) :
      0 < (c.arclengthFactor r).im := by
    rw [← c.clock_spec.2.2.2.2] at hr
    obtain ⟨t, ht, htr⟩ := hr
    have hf : c.curve t = c.arclengthFactor r := by
      simpa only [Function.comp_apply, htr] using c.arclengthFactor_spec.2.1 ht
    rw [← hf]
    exact hpos t (by simpa only [ha, hb] using ht)
  have hγc : Continuous (fun r : Icc (0 : ℝ) c.euclideanLength =>
      c.arclengthFactor (r : ℝ)) :=
    c.arclengthFactor_spec.1.continuous.comp continuous_subtype_val
  have hγ : Continuous (fun r : Icc (0 : ℝ) c.euclideanLength =>
      (⟨c.arclengthFactor r, hfactorpos r r.property⟩ : ℍ)) :=
    Continuous.upperHalfPlaneMk hγc (fun r => hfactorpos (r : ℝ) r.property)
  let F : C(Icc (0 : ℝ) c.euclideanLength, X) :=
    ⟨fun r => p ⟨c.arclengthFactor r, hfactorpos r r.property⟩, hp.comp hγ⟩
  let u : C(I, Icc (0 : ℝ) c.euclideanLength) :=
    ⟨fun t => ⟨c.clock t, hclockMem t⟩,
      (c.clock_spec.2.1.comp_continuous continuous_subtype_val hpar).subtype_mk hclockMem⟩
  have hvMem (t : I) : c.euclideanLength * (t : ℝ) ∈ Icc 0 c.euclideanLength := by
    refine ⟨mul_nonneg c.clock_spec.1 t.property.1, ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left t.property.2 c.clock_spec.1
  let v : C(I, Icc (0 : ℝ) c.euclideanLength) :=
    ⟨fun t => ⟨c.euclideanLength * t, hvMem t⟩,
      (continuous_const.mul continuous_subtype_val).subtype_mk hvMem⟩
  have hv0 : v 0 = u 0 := by
    apply Subtype.ext
    change c.euclideanLength * 0 = c.clock 0
    have hz : c.clock 0 = 0 := by simpa only [ha] using c.clock_spec.2.2.2.1
    rw [mul_zero, hz]
  have hv1 : v 1 = u 1 := by
    apply Subtype.ext
    change c.euclideanLength * 1 = c.clock 1
    simp only [euclideanLength, hb, mul_one]
  apply freelyHomotopic_of_interval_clocks F u v hv0 hv1
  · intro t
    have hpt : (⟨c.curve t, hpos t t.property⟩ : ℍ) =
        ⟨c.arclengthFactor (c.clock t), hfactorpos _ (hclockMem t)⟩ :=
      UpperHalfPlane.ext (c.arclengthFactor_spec.2.1 (hpar t))
    exact (hα t).symm.trans (congrArg p hpt)
  · intro t
    exact (hβ t (hfactorpos _ (hvMem t))).symm

end LowDimensionalTopology.Geometry.RectifiableCurve
