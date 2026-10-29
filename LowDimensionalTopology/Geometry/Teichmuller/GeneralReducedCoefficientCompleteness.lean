/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCCompleteness
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralReducedCoefficientSpace
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# The original full-log metric on the actual reduced coefficient quotient

The natural coefficient equivalence transports the original marked-class
metric to the entire raw reduced quotient T#(Γ). Its forward map remains the
literal original marking's lifted coefficient. The same natural equivalence
is an isometry, so the original completeness theorem also proves the reduced
space complete. No compactness or additional mathematical premise is used.
These are named metric structures, not global instances.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u v

variable (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
  {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
  (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
    ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)

/-- The actual all-raw reduced quotient, with the original full-log metric
transported by the inverse of the natural original coefficient equivalence. -/
@[instance_reducible] def reducedCoefficientMetricSpace :
    MetricSpace (ReducedCoefficient.Space Γ) :=
  (metricSpace.{u, v} R hp hfixed).induced
    (reducedCoefficientEquivGeneral.{u, v} R hp hfixed).symm
    (reducedCoefficientEquivGeneral.{u, v} R hp hfixed).symm.injective

/-- Distances in the actual reduced quotient are exactly the original
full-log distances of their natural original marked preimages. -/
theorem reducedCoefficientMetricSpace_dist (a b : ReducedCoefficient.Space Γ) :
    @dist _ (reducedCoefficientMetricSpace.{u, v} R hp hfixed).toDist a b =
      distance ((reducedCoefficientEquivGeneral.{u, v} R hp hfixed).symm a)
        ((reducedCoefficientEquivGeneral.{u, v} R hp hfixed).symm b) := rfl

/-- The actual original coefficient equivalence is an isometric equivalence
for this same original full-log metric, with independent target universes. -/
def reducedCoefficientIsometryEquiv :
    letI := metricSpace.{u, v} R hp hfixed
    letI := reducedCoefficientMetricSpace.{u, v} R hp hfixed
    Space.{u, v} R ≃ᵢ ReducedCoefficient.Space Γ := by
  letI := metricSpace.{u, v} R hp hfixed
  letI := reducedCoefficientMetricSpace.{u, v} R hp hfixed
  let e := reducedCoefficientEquivGeneral.{u, v} R hp hfixed
  refine { toEquiv := e, isometry_toFun := ?_ }
  apply Isometry.of_dist_eq
  intro a b
  change distance (e.symm (e a)) (e.symm (e b)) = distance a b
  exact congrArg₂ distance (e.symm_apply_apply a) (e.symm_apply_apply b)

/-- The isometry sends each actual original class to the reduced class of
its literal original lifted coefficient, retaining the natural forward law. -/
theorem reducedCoefficientIsometryEquiv_mk (m : Marked.{u, v} R) :
    letI := metricSpace.{u, v} R hp hfixed
    letI := reducedCoefficientMetricSpace.{u, v} R hp hfixed
    reducedCoefficientIsometryEquiv.{u, v} R hp hfixed (mk m) =
      ReducedCoefficient.mk (markedCoefficientGeneral R hp m) :=
  reducedCoefficientEquivGeneral_mk R hp hfixed m

/-- The literal coefficient classes of two actual markings have precisely
their original full-log Teichmüller distance. -/
theorem reducedCoefficientMetricSpace_dist_mk (m n : Marked.{u, v} R) :
    letI := reducedCoefficientMetricSpace.{u, v} R hp hfixed
    dist (ReducedCoefficient.mk (markedCoefficientGeneral R hp m))
        (ReducedCoefficient.mk (markedCoefficientGeneral R hp n)) =
      distance (mk m) (mk n) := by
  let := metricSpace.{u, v} R hp hfixed
  let := reducedCoefficientMetricSpace.{u, v} R hp hfixed
  exact (reducedCoefficientIsometryEquiv.{u, v} R hp hfixed).dist_eq (mk m) (mk n)

/-- The actual all-raw reduced coefficient quotient
T#(Γ) is complete for this same original full-log Teichmüller metric. -/
theorem reducedCoefficient_completeSpace :
    letI := reducedCoefficientMetricSpace.{u, v} R hp hfixed
    CompleteSpace (ReducedCoefficient.Space Γ) := by
  let := metricSpace.{u, v} R hp hfixed
  let := reducedCoefficientMetricSpace.{u, v} R hp hfixed
  let : CompleteSpace (Space.{u, v} R) := completeSpace.{u, v} R hp hfixed
  exact (reducedCoefficientIsometryEquiv.{u, v} R hp hfixed).symm.completeSpace

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
