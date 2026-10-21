/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.PolygonalQuotient
public import Mathlib.Topology.Constructions
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
namespace LowDimensionalTopology.Geometry.Surfaces
open LeanEval.Topology.ClassificationOfSurfaces

/-- The actual standard marked circular arcs cover the genuine boundary circle. -/
def polygonSideCircleCover (n:ℕ) (x:Σ _:Fin n,unitInterval) : Circle:=
  Circle.exp (PolygonCell.sideAngle x.1 x.2)

theorem continuous_polygonSideCircleCover (n:ℕ) : Continuous (polygonSideCircleCover n) := by
  apply continuous_sigma_iff.mpr
  intro i
  exact Circle.exp.continuous.comp (PolygonCell.continuous_sideAngle i)

theorem polygonSideCircleCover_surjective (n:ℕ) (hn:0<n) :
    Function.Surjective (polygonSideCircleCover n) := by
  intro z
  obtain ⟨i,t,ht⟩:=PolygonCell.exists_side_eq_of_mem_sphere hn (PolygonCell.ofCircle n z) z.property
  refine ⟨⟨i,t⟩,?_⟩
  apply Subtype.ext
  exact congrArg PolygonCell.val ht

theorem polygonSideCircleCover_isQuotientMap (n:ℕ) (hn:0<n) :
    IsQuotientMap (polygonSideCircleCover n) :=
  (continuous_polygonSideCircleCover n).isClosedMap.isQuotientMap
    (continuous_polygonSideCircleCover n) (polygonSideCircleCover_surjective n hn)

/-- Adjacent true marked circle arcs have the same genuine endpoint. -/
theorem polygonSideCircleCover_endpoint_rotate {n:ℕ} (i:Fin n) :
    polygonSideCircleCover n ⟨i,1⟩=polygonSideCircleCover n ⟨finRotate n i,0⟩ := by
  apply Subtype.ext
  exact congrArg PolygonCell.val (PolygonCell.side_one_eq_rotate_zero i)
end LowDimensionalTopology.Geometry.Surfaces
