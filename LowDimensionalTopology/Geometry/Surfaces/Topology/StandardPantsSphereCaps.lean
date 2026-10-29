module

public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Surfaces.Topology.PairOfPantsModel
public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Three concrete closed spherical caps for the literal standard pants region

The outer cap chart is `z ↦ 2/z`, including the value infinity at zero.
The other two cap charts are `z ↦ z/2 - 1` and `z ↦ z/2 + 1`.
All caps have the same actual closed-unit-disc domain as the Nielsen caps.
-/

@[expose] public section
noncomputable section
open Set
open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Mobius

/-- The exact two-sphere carrier used by the genus-zero classification. -/
def pantsComplexSphereHomeomorph :
    ExtendedComplex ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])

/-- The literal outer, left inner and right inner closed-cap charts. -/
def pantsStandardCapChart (i : Fin 3) : ExtendedComplex ≃ₜ ExtendedComplex :=
  if i = 0 then
    (mobiusBoundaryHomeomorph reciprocalMobius).trans (affineHomeomorph 2 0 (by norm_num))
  else if i = 1 then affineHomeomorph ((1 : ℂ) / 2) (-1) (by norm_num)
  else affineHomeomorph ((1 : ℂ) / 2) 1 (by norm_num)

/-- Actual closed-disc embeddings into the same unit two-sphere. -/
def pantsStandardSphereCap (i : Fin 3) (z : Complex.UnitClosedDisc) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  pantsComplexSphereHomeomorph (pantsStandardCapChart i ((z : ℂ) : ExtendedComplex))

theorem pantsStandardSphereCap_isClosedEmbedding (i : Fin 3) :
    Topology.IsClosedEmbedding (pantsStandardSphereCap i) := by
  let : CompactSpace Complex.UnitClosedDisc :=
    inferInstanceAs (CompactSpace (Metric.closedBall (0 : ℂ) 1))
  have hbase : Topology.IsEmbedding
      (fun z : Complex.UnitClosedDisc => ((z : ℂ) : ExtendedComplex)) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp Complex.UnitClosedDisc.isEmbedding_coe
  have hcap : Topology.IsEmbedding (pantsStandardSphereCap i) :=
    pantsComplexSphereHomeomorph.isEmbedding.comp ((pantsStandardCapChart i).isEmbedding.comp hbase)
  exact hcap.continuous.isClosedEmbedding hcap.injective

end LowDimensionalTopology.Geometry.Surfaces
