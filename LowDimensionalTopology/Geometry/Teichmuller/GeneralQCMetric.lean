/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCDistanceSeparation
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCTargetDistance
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCDistanceTopology
public import Mathlib.Topology.MetricSpace.Defs

/-!
# The original general QC Teichmüller metric

For the book's actual uniformized reference in its fixed-triple coordinates,
the same full-log distance separates independently sized original targets.
The resulting named metric preserves the pre-existing distance-ball topology
definitionally. Compactness, genus and completeness are not assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u v

variable (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
  {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
  (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
    ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)

include hp hfixed in
/-- Zero original full-log distance gives equality in the original quotient,
with independently sized native targets and their actual markings retained. -/
theorem eq_of_distance_zero (a b : Space.{u, v} R) (hzero : distance a b = 0) : a = b := by
  obtain ⟨m, rfl⟩ := Quotient.exists_rep a
  obtain ⟨n, rfl⟩ := Quotient.exists_rep b
  apply (mk_eq_mk_iff_sourceCarrierRepresentatives m n).mpr
  apply mk_eq_of_distance_zero R hp hfixed m.sourceCarrierRepresentative n.sourceCarrierRepresentative
  exact (distance_eq_sourceCarrierRepresentatives m n).symm.trans hzero

/-- This named metric has the actual original full-log distance and preserves
the actual original distance-ball topology; it is not a global instance. -/
@[instance_reducible] def metricSpace : MetricSpace (Space.{u, v} R) where
  toPseudoMetricSpace := pseudoMetricSpace.{u, v} R
  eq_of_dist_eq_zero {a b} h := eq_of_distance_zero R hp hfixed a b h

@[simp] theorem metricSpace_dist (a b : Space.{u, v} R) :
    @dist _ (metricSpace.{u, v} R hp hfixed).toDist a b = distance a b := rfl

@[simp] theorem metricSpace_topology :
    (metricSpace.{u, v} R hp hfixed).toUniformSpace.toTopologicalSpace =
      distanceTopology.{u, v} R := rfl

include hp hfixed in
/-- Consequently the existing original distance-ball topology is Hausdorff. -/
theorem distanceTopology_t2Space :
    letI := distanceTopology.{u, v} R
    T2Space (Space.{u, v} R) := by
  let := metricSpace.{u, v} R hp hfixed
  infer_instance

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
