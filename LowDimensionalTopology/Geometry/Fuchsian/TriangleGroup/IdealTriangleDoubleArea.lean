/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.IdealTriangleConformalDomains
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology MeasureTheory
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The two physical open halves of a genuine doubled ideal triangle are disjoint. -/
theorem idealTriangle_double_interiors_disjoint (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    Disjoint (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one) ''
        (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior) := by
  apply disjoint_left.mpr
  rintro _ hz ⟨x,hx,rfl⟩
  have hN:=((prescribedIdealHTriangle_mem_interior_iff α β hα.nonneg hβ.nonneg hs x).mp hx).2
  have hR:=((prescribedIdealHTriangle_mem_interior_iff α β hα.nonneg hβ.nonneg hs _).mp hz).2
  rw [unitCircleReflection_norm_sq] at hR
  have hi : (‖(x:ℂ)‖^2)⁻¹<1:=(inv_lt_one₀ (by linarith : 0<‖(x:ℂ)‖^2)).mpr hN
  exact (lt_irrefl (1:ℝ)) (hR.trans hi)

/-- The genuine conformal doubled domain has exactly twice the original physical triangle area. -/
theorem idealTwoCornerGap_volume_eq_double (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    volume (idealTwoCornerGap α β)=
      2*volume (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior := by
  let T:=prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs
  let C:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.circle 0 1 zero_lt_one)
  have hT:=prescribedIdealHTriangle_interior_subset_gap α β hα hβ hs
  have hC : C '' T.interior⊆idealTwoCornerGap α β:=by
    rintro _ ⟨z,hz,rfl⟩
    exact (idealTwoCornerGap_circleReflection_iff α β z).mpr (hT hz)
  have hdisj : Disjoint T.interior (C '' T.interior):=
    idealTriangle_double_interiors_disjoint α β hα hβ hs
  have hLower : volume T.interior+volume T.interior≤volume (idealTwoCornerGap α β):=by
    calc
      _ = volume (T.interior∪C '' T.interior) := by
        rw [measure_union hdisj
          (C.toHomeomorph.isOpenMap _ T.interior_isOpen).measurableSet,
          native_isometry_volume_image]
      _ ≤ _ := measure_mono (union_subset hT hC)
  have hCl : volume (closure T.interior)=volume T.interior:=
    measure_closure_of_null_frontier
      (prescribedIdealHTriangle_frontier_volume_zero α β hα.nonneg hβ.nonneg hs)
  have hUpper : volume (idealTwoCornerGap α β)≤volume T.interior+volume T.interior:=by
    calc
      _ ≤ volume (closure T.interior∪C '' closure T.interior) :=
        measure_mono (idealTwoCornerGap_subset_doubleClosure α β hα hβ hs)
      _ ≤ volume (closure T.interior)+volume (C '' closure T.interior) := measure_union_le _ _
      _ = _ := by rw [native_isometry_volume_image,hCl]
  rw [two_mul]
  exact le_antisymm hUpper hLower

/-- Actual hyperbolic density area, rather than a formal signature expression, for the doubled domain. -/
theorem idealTwoCornerGap_volume (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    volume (idealTwoCornerGap α β)=ENNReal.ofReal (2*(Real.pi-α-β)) := by
  rw [idealTwoCornerGap_volume_eq_double α β hα hβ hs,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.area_eq_angle_defect]
  have hθ:=prescribedIdealHTriangle_angles α β hα.nonneg hβ.nonneg hs
  rw [hθ.1,hθ.2.1,hθ.2.2,sub_zero]
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  norm_num

end LowDimensionalTopology.Geometry.Fuchsian
