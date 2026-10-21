/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenBoundaryGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.FiniteNielsenCoreGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeometricFuchsianCharts
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealTriangleIsometries

/-!
# Actual finite Nielsen-core polygon geometry
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc OnePoint RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

def nielsenHalfPlaneChart {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) : P.domain.carrier≃ₜℍ :=
  geometricHalfPlaneChart P.asFuchsianDisc (P.asFuchsianDisc.nielsenArcNormalizer hNE)
    (P.asFuchsianDisc.nielsenArcNormalizer_image hNE)

theorem nielsenHalfPlaneChart_core_image {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hNE : DiscreteGroups.IsNonElementary H) :
    nielsenHalfPlaneChart P hNE '' fuchsianNielsenCore P hNE=
      Hyperbolic.nielsenRealArcRegion (Hyperbolic.nielsenHalfPlaneRealSet
        (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate (P.asFuchsianDisc.nielsenArcNormalizer hNE) H))) := by
  let q:=P.asFuchsianDisc.nielsenArcNormalizer hNE
  let Λ:=DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H)
  have hq : q.val '' P.asFuchsianDisc.carrier=Hyperbolic.openHalfPlaneSet :=
    P.asFuchsianDisc.nielsenArcNormalizer_image hNE
  have he (x:P.domain.carrier) : Hyperbolic.extendedHalfPlanePoint (nielsenHalfPlaneChart P hNE x)=q.val x.val :=
    geometricHalfPlaneChart_extended P.asFuchsianDisc q hq x
  have hArc : Hyperbolic.nielsenHalfPlaneArcRegion Λ=Hyperbolic.nielsenRealArcRegion (Hyperbolic.nielsenHalfPlaneRealSet
    Λ) :=
    Hyperbolic.nielsenHalfPlaneArcRegion_eq_realArcRegion Λ (P.asFuchsianDisc.nielsenArcNormalizer_limit hNE)
  rw [←hArc]
  apply subset_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change x.val∈nielsenModelSet q (Hyperbolic.nielsenHalfPlaneArcRegion Λ) at hx
    obtain ⟨p,⟨w,hw,rfl⟩,hp⟩:=hx
    have hwe : nielsenHalfPlaneChart P hNE x=w := by
      apply nielsen_halfPlanePoint_isOpenEmbedding.injective
      rw [he,←hp]
      exact q.val.apply_symm_apply _
    exact hwe.symm ▸ hw
  · intro w hw
    let x: P.domain.carrier:=(nielsenHalfPlaneChart P hNE).symm w
    refine ⟨x,?_,(nielsenHalfPlaneChart P hNE).apply_symm_apply w⟩
    change x.val∈nielsenModelSet q (Hyperbolic.nielsenHalfPlaneArcRegion Λ)
    refine ⟨Hyperbolic.extendedHalfPlanePoint w,⟨w,hw,rfl⟩,?_⟩
    apply q.val.injective
    change q.val (q.val.symm (Hyperbolic.extendedHalfPlanePoint w))=q.val x.val
    rw [q.val.apply_symm_apply]
    exact ((congrArg Hyperbolic.extendedHalfPlanePoint
      ((nielsenHalfPlaneChart P hNE).apply_symm_apply w)).symm.trans (he x))

theorem nielsenHalfPlaneChart_frontier_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hNE : DiscreteGroups.IsNonElementary H) :
    nielsenHalfPlaneChart P hNE '' frontier (fuchsianNielsenCore P hNE)=
      frontier (Hyperbolic.nielsenRealArcRegion (Hyperbolic.nielsenHalfPlaneRealSet
        (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate (P.asFuchsianDisc.nielsenArcNormalizer hNE) H)))) := by
  rw [(nielsenHalfPlaneChart P hNE).image_frontier,nielsenHalfPlaneChart_core_image]

def nielsenDiscChart {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) : 𝔻≃ₜ𝔻 :=
  (P.finiteCoordinate.symm.trans (nielsenHalfPlaneChart P hNE)).trans Hyperbolic.cayleyHomeomorph

theorem nielsenDiscChart_extended {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (x:𝔻) :
    Hyperbolic.extendedDiscPoint (nielsenDiscChart P hNE x)=
      (Hyperbolic.cayleyMobius*P.asFuchsianDisc.nielsenArcNormalizer hNE).val (Hyperbolic.extendedDiscPoint x) := by
  let q:=P.asFuchsianDisc.nielsenArcNormalizer hNE
  have he := geometricHalfPlaneChart_extended P.asFuchsianDisc q
    (P.asFuchsianDisc.nielsenArcNormalizer_image hNE) (P.finiteCoordinate.symm x)
  change Hyperbolic.extendedHalfPlanePoint (nielsenHalfPlaneChart P hNE (P.finiteCoordinate.symm x))=
    q.val (P.finiteCoordinate.symm x).val at he
  have hx : (P.finiteCoordinate.symm x).val=Hyperbolic.extendedDiscPoint x := by
    rw [←P.finiteCoordinate_extended (P.finiteCoordinate.symm x),P.finiteCoordinate.apply_symm_apply]
    rfl
  rw [hx] at he
  change Hyperbolic.extendedDiscPoint (Hyperbolic.halfPlaneToDisc (nielsenHalfPlaneChart P hNE (P.finiteCoordinate.symm
    x)))=_
  change (((Hyperbolic.halfPlaneToDisc (nielsenHalfPlaneChart P hNE (P.finiteCoordinate.symm
    x)):𝔻):ℂ):Mobius.ExtendedComplex)=_
  rw [←Hyperbolic.extendedCayley_halfPlane]
  change Hyperbolic.extendedCayley (Hyperbolic.extendedHalfPlanePoint (nielsenHalfPlaneChart P hNE
    (P.finiteCoordinate.symm x)))=_
  rw [he]
  rfl

theorem nielsenDiscChart_isometry {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hNE : DiscreteGroups.IsNonElementary H) :
    letI:=Hyperbolic.discHyperbolicMetric;Isometry (nielsenDiscChart P hNE) := by
  let q:=P.asFuchsianDisc.nielsenArcNormalizer hNE
  have hpres : (Hyperbolic.cayleyMobius*q).val '' Hyperbolic.extendedUnitDisc=Hyperbolic.extendedUnitDisc := by
    have hq : q.val '' Hyperbolic.extendedUnitDisc=Hyperbolic.openHalfPlaneSet:=P.asFuchsianDisc.nielsenArcNormalizer_image hNE
    rw [nielsen_mobius_image_mul,hq,cayleyMobius_image_openHalfPlane]
  obtain ⟨φ,hφ,hact⟩:=nielsen_discPreserver_exists_nativeHomeomorph (Hyperbolic.cayleyMobius*q) hpres
  have he : nielsenDiscChart P hNE=φ := by
    ext x
    apply OnePoint.coe_injective
    exact (nielsenDiscChart_extended P hNE x).trans (hact x)
  rw [he]
  exact hφ

theorem nielsenGap_original_native_line {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (G:Hyperbolic.NielsenHalfPlaneGap) :
    ∃L:Hyperbolic.DiscLine,P.finiteCoordinate '' ((nielsenHalfPlaneChart P hNE).symm '' G.line.carrier)=L.carrier := by
  let :=Hyperbolic.discHyperbolicMetric
  let φ:=nielsenDiscChart P hNE
  have hi : Isometry φ.symm := (⟨φ.toEquiv,nielsenDiscChart_isometry P hNE⟩:𝔻≃ᵢ𝔻).symm.isometry
  obtain ⟨L,hL⟩:=Hyperbolic.discPathIsometry_image_discLine φ.symm (fun x y=>by simpa only [Hyperbolic.discHyperbolicMetric_distance] using hi.dist_eq x y) G.line.toDiscLine
  refine ⟨L,?_⟩
  rw [G.line.toDiscLine_carrier,G.line.discCarrier_eq_cayley_image,image_image] at hL
  rw [image_image]
  have he : (fun x:ℍ=>P.finiteCoordinate ((nielsenHalfPlaneChart P hNE).symm x))=
      (fun x=>φ.symm (Hyperbolic.halfPlaneToDisc x)) := by
    funext x
    change P.finiteCoordinate ((nielsenHalfPlaneChart P hNE).symm x)=
      P.finiteCoordinate ((nielsenHalfPlaneChart P hNE).symm (Hyperbolic.discToHalfPlane (Hyperbolic.halfPlaneToDisc
        x)))
    rw [Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  rw [he]
  exact hL

end LowDimensionalTopology.Geometry.Fuchsian
