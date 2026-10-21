/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology MeasureTheory
open scoped UpperHalfPlane Pointwise ComplexConjugate
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

/-- Each actual corner sector is the intersection of two genuine hyperbolic half-planes. -/
theorem idealCornerSector_eq_halfPlanes (θ : ℝ) :
    idealCornerSector θ=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hReCutLt (Real.cos θ) ∩
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one) ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.hReCutLt (Real.cos θ) := by
  ext z
  have hn : 0<‖(z:ℂ)‖^2:=sq_pos_of_pos (norm_pos_iff.mpr z.ne_zero)
  change (z.re<Real.cos θ ∧ z.re<Real.cos θ*Complex.normSq (z:ℂ)) ↔
    (z.re<Real.cos θ ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z).re<Real.cos θ)
  rw [unitCircleReflection_re,div_lt_iff₀ hn,Complex.normSq_eq_norm_sq]

theorem idealCornerSector_hConvex
    (θ : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (idealCornerSector θ) := by
  rw [idealCornerSector_eq_halfPlanes]
  intro z hz w hw u hu
  exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hReCutLt_hConvex _ z hz.1 w hw.1 hu,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.isometry_preimage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hReCutLt_hConvex _)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_isometry 0 1 zero_lt_one) z hz.2 w hw.2 hu⟩

theorem idealCornerSector_isOpen (θ : ℝ) : IsOpen (idealCornerSector θ) := by
  rw [idealCornerSector_eq_halfPlanes]
  exact (isOpen_lt UpperHalfPlane.continuous_re continuous_const).inter
    ((isOpen_lt UpperHalfPlane.continuous_re continuous_const).preimage
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_isometry 0 1 zero_lt_one).continuous)

theorem idealTwoCornerGap_hConvex
    (α β : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (idealTwoCornerGap α β) := by
  intro z hz w hw u hu
  exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.isometry_preimage (idealCornerSector_hConvex α) idealTriangleAxisMirror.isometry
    z hz.1 w hw.1 hu,idealCornerSector_hConvex β z hz.2 w hw.2 hu⟩

theorem idealTwoCornerGap_isOpen (α β : ℝ) : IsOpen (idealTwoCornerGap α β) :=
  ((idealCornerSector_isOpen α).preimage idealTriangleAxisMirror.continuous).inter
    (idealCornerSector_isOpen β)

/-- The true conformal gap lies in the two original closed physical triangles. -/
theorem idealTwoCornerGap_subset_doubleClosure (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    idealTwoCornerGap α β⊆closure (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior ∪
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one) '' closure (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior := by
  have hUp (z : ℍ) (hz:z∈idealTwoCornerGap α β) (hN:1≤‖(z:ℂ)‖^2) :
      z∈closure (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior:=by
    rw [prescribedIdealHTriangle_interior_closure]
    have hL : -Real.cos α<z.re:=by
      have hh:=hz.1.1
      change (idealTriangleAxisMirror z).re<Real.cos α at hh
      rw [idealTriangleAxisMirror_re] at hh
      linarith
    exact ⟨⟨hL.le,hz.2.1.le⟩,hN⟩
  intro z hz
  by_cases hN : 1≤‖(z:ℂ)‖^2
  · exact Or.inl (hUp z hz hN)
  · right
    have hn : 0<‖(z:ℂ)‖^2:=sq_pos_of_pos (norm_pos_iff.mpr z.ne_zero)
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z,hUp _
      ((idealTwoCornerGap_circleReflection_iff α β z).mpr hz) ?_,?_⟩
    · rw [unitCircleReflection_norm_sq]
      exact (one_le_inv₀ hn).mpr (le_of_not_ge hN)
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one).reflection_involutive z

/-- Both closed halves of the actual doubled triangle lie in the true gap closure. -/
theorem idealTwoCornerGap_doubleClosure_subset (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    closure (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior ∪
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one) '' closure (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior ⊆
      closure (idealTwoCornerGap α β) := by
  have hT:=prescribedIdealHTriangle_interior_subset_gap α β hα hβ hs
  have hC : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one) ''
      (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior⊆idealTwoCornerGap α β:=by
    rintro _ ⟨z,hz,rfl⟩
    exact (idealTwoCornerGap_circleReflection_iff α β z).mpr (hT hz)
  rintro z (hz|⟨x,hx,rfl⟩)
  · exact closure_mono hT hz
  · exact closure_mono hC (map_mem_closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_isometry 0 1 zero_lt_one).continuous hx (fun _ hz=>mem_image_of_mem _ hz))

/-- Exact closure of the true conformal two-triangle domain. -/
theorem idealTwoCornerGap_closure (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    closure (idealTwoCornerGap α β)=closure (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior ∪
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one) '' closure (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior := by
  apply subset_antisymm
  · apply closure_minimal (idealTwoCornerGap_subset_doubleClosure α β hα hβ hs)
    exact isClosed_closure.union
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.circle 0 1 zero_lt_one)).toHomeomorph.isClosedMap _ isClosed_closure)
  · exact idealTwoCornerGap_doubleClosure_subset α β hα hβ hs


/-- The actual conformal subgroup covers the plane with the two-triangle domain closure. -/
theorem idealTwoCornerGap_closure_meetsEveryOrbit (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit (triangleConformalGroup (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs)) ℍ
      (closure (idealTwoCornerGap α β)) := by
  let T:=prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs
  let C:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC
  have hC (z : ℍ) : C z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z:=by
    change T.sideLineC.reflection z=_
    rw [prescribedIdealHTriangle_circle]
    rfl
  have hCi (z : ℍ) : C⁻¹ z=C z:=rfl
  intro x
  obtain ⟨g,hg⟩:=prescribedIdealHTriangle_closure_meetsEveryOrbit α β hα hβ hs x
  rcases triangleReflectionGroup_conformal_or_thirdMirror T g.val⁻¹
    ((triangleReflectionGroup T).inv_mem g.property) with hconf|hconf
  · refine ⟨⟨g.val,(triangleConformalGroup T).inv_mem hconf⟩,?_⟩
    exact idealTwoCornerGap_doubleClosure_subset α β hα hβ hs (Or.inl hg)
  · refine ⟨⟨(g.val⁻¹*C)⁻¹,(triangleConformalGroup T).inv_mem hconf⟩,?_⟩
    change (g.val⁻¹*C)⁻¹ x∈closure (idealTwoCornerGap α β)
    have he : (g.val⁻¹*C)⁻¹ x=_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one (g.val x):=by
      simp only [mul_inv_rev,inv_inv,IsometryEquiv.mul_apply,hCi,hC]
    rw [he]
    exact idealTwoCornerGap_doubleClosure_subset α β hα hβ hs (Or.inr ⟨g.val x,hg,rfl⟩)

/-- The doubled domain has genuine density-area-zero frontier, including its ideal cusps. -/
theorem idealTwoCornerGap_frontier_volume_zero (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    volume (frontier (idealTwoCornerGap α β))=0 := by
  let T:=prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs
  let C:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.circle 0 1 zero_lt_one)
  have hc (z : ℍ) : C z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z:=rfl
  have hsub : frontier (idealTwoCornerGap α β)⊆frontier T.interior ∪ C '' frontier T.interior:=by
    rw [frontier,(idealTwoCornerGap_isOpen α β).interior_eq,idealTwoCornerGap_closure α β hα hβ hs]
    rintro z ⟨(hz|⟨x,hx,rfl⟩),hnot⟩
    · left
      rw [frontier,T.interior_isOpen.interior_eq]
      exact ⟨hz,fun ht=>hnot (prescribedIdealHTriangle_interior_subset_gap α β hα hβ hs ht)⟩
    · right
      refine ⟨x,?_,rfl⟩
      rw [frontier,T.interior_isOpen.interior_eq]
      exact ⟨hx,fun ht=>hnot ((idealTwoCornerGap_circleReflection_iff α β x).mpr
        (prescribedIdealHTriangle_interior_subset_gap α β hα hβ hs ht))⟩
  have hT : volume (frontier T.interior)=0:=
    prescribedIdealHTriangle_frontier_volume_zero α β hα.nonneg hβ.nonneg hs
  apply measure_mono_null hsub
  exact measure_union_null hT (by rw [native_isometry_volume_image,hT])

/-- The genuine open two-triangle region is a fundamental domain for the original conformal group. -/
theorem idealTwoCornerGap_fundamentalDomain (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (triangleConformalGroup (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs)) ℍ
      volume (idealTwoCornerGap α β) := by
  let T:=prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs
  have hconn : IsConnected (idealTwoCornerGap α β):=⟨
    T.interior_nonempty.mono (prescribedIdealHTriangle_interior_subset_gap α β hα hβ hs),
    (idealTwoCornerGap_hConvex α β).isPreconnected⟩
  refine ⟨idealTwoCornerGap_isOpen α β,hconn,?_,idealTwoCornerGap_frontier_volume_zero α β hα hβ hs⟩
  apply exists_fundamentalSet_between _ _ subset_closure
    (idealTwoCornerGap_closure_meetsEveryOrbit α β hα hβ hs)
  intro x hx y hy he
  obtain ⟨g,hg⟩:=(Quotient.exact he : MulAction.orbitRel (triangleConformalGroup T) ℍ x y)
  by_cases h1 : g.val=1
  · simpa only [show g=1 from Subtype.ext h1,one_smul] using hg.symm
  · have hp:=idealTwoCornerGap_wandering α β hα hβ hs g.val
      ((prescribedIdealHTriangle_conformal_eq_twoCornerGroup α β hα.nonneg hβ.nonneg hs) ▸ g.property) h1
    exact False.elim (disjoint_left.mp hp ⟨y,hy,hg⟩ hx)

end LowDimensionalTopology.Geometry.Fuchsian
