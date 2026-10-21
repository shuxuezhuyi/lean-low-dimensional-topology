module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.EllipticSidePairing
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.DiscPolygonConjugation
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology OnePoint Pointwise Complex.UnitDisc

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
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
/-- Every primitive elliptic in the original actual unit-disc group pairs sides of a genuine convex locally finite fundamental polygon. -/
theorem primitive_elliptic_side_pairing {G : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (f : Mobius.complexMobiusGroup)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (hp : IsPrimitive G f) :
    ∃ D : Set P.domain.carrier, ∃ hD : IsConvexFuchsianPolygon P D,
      ∃ s : FuchsianPolygonSides P D, (fuchsianSideElement hD s).val = f := by
  obtain ⟨w,hw,_⟩ := elliptic_unitDisc_existsUnique_fixed f hf (P.image_eq ⟨f,hp.mem⟩)
  obtain ⟨q,hq,hqw⟩ := P.point_normalizer_exists w
  let Q := P.conjugateData q hq
  let e := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q G
  let k := q*f*q⁻¹
  have hkE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic k := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation f q).mpr hf
  have hkP : IsPrimitive (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) k :=
    (isPrimitive_conjugation_iff G f q).mpr hp
  have hk0 : k.val (0:ℂ) = (0:ℂ) := by
    have h := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_conjugate_fixedpoint f q w.val hw
    have hq0 : q.val w.val = ((0:ℂ):Mobius.ExtendedComplex) := hqw
    rwa [hq0] at h
  obtain ⟨D,hD,s,hs⟩ := primitive_elliptic_zero_side_pairing Q k hkE hkP hk0
  obtain ⟨hP,t,ht⟩ := equivariant_fuchsian_side_element_preimage P Q e (P.conjugateCoordinate q hq)
    (P.conjugateCoordinate_equivariant q hq) (P.conjugateCoordinate_area_map q hq)
    (P.conjugateCoordinate_isometry q hq) hD s
  have hse : fuchsianSideElement hD s = e ⟨f,hp.mem⟩ := Subtype.ext hs
  rw [hse,e.symm_apply_apply] at ht
  exact ⟨_,hP,t,congrArg (fun a : G => a.val) ht⟩
end LowDimensionalTopology.Geometry.Fuchsian
