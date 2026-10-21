/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IsometryClassification
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The genuine evaluation action, made explicit here without adding a competing global action instance. -/
@[instance_reducible]
def nativeIsometryEvaluationAction : MulAction (ℍ≃ᵢℍ) ℍ where
  smul f z:=f z
  one_smul _:=rfl
  mul_smul _ _ _:=rfl

/-- Every actual hyperbolic isometry preserves the genuine density area, including reflections. -/
theorem nativeIsometry_measurePreserving (f:ℍ≃ᵢℍ) : MeasurePreserving f volume volume := by
  obtain ⟨A,hA⟩:=isometry_exists_realGL f.isometry
  rw [hA]
  exact measurePreserving_smul A volume

/-- Pushforward by any genuine native isometry preserves the actual hyperbolic density measure. -/
theorem nativeIsometry_volume_map (f:ℍ≃ᵢℍ) : Measure.map f (volume:Measure ℍ)=volume :=
  (nativeIsometry_measurePreserving f).map_eq

/-- The full native isometry group, with both orientations, preserves actual hyperbolic area. -/
instance nativeIsometryGroup_smulInvariantMeasure :
    letI:=nativeIsometryEvaluationAction
    SMulInvariantMeasure (ℍ≃ᵢℍ) ℍ volume := by
  let nativeIsometryAreaAction:=nativeIsometryEvaluationAction
  exact ⟨by
    intro f S hS
    exact (nativeIsometry_measurePreserving f).measure_preimage hS.nullMeasurableSet⟩

/-- Every original native subgroup preserves area, with no discreteness, non-elementarity or orientation hypothesis. -/
instance nativeIsometrySubgroup_smulInvariantMeasure (H:Subgroup (ℍ≃ᵢℍ)) :
    letI:=nativeIsometryEvaluationAction
    SMulInvariantMeasure H ℍ volume := by
  let nativeIsometrySubgroupAreaAction:=nativeIsometryEvaluationAction
  exact ⟨by
    intro f S hS
    exact (nativeIsometry_measurePreserving f.val).measure_preimage hS.nullMeasurableSet⟩

end LowDimensionalTopology.Geometry.Hyperbolic
