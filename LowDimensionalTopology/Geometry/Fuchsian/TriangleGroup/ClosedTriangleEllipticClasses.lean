/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleEllipticGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleMobiusQuotients
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.FuchsianSignatureOrders
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
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

/-- A nonidentity original disc-preserving map fixing an actual interior point is elliptic. -/
theorem fuchsianDisc_nonidentity_fixed_elliptic
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:Mobius.complexMobiusGroup) (hf:f∈H) (hfn:f≠1)
    (p:Mobius.ExtendedComplex)
    (hp:p∈D.carrier)
    (hfix:f.val p=p) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f := by
  have hnf:p∉frontier D.carrier:=fun h=>h.2 (D.isDisc.isOpen.interior_eq.symm ▸ hp)
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy f hfn with hpar|hlox|hell
  · exact False.elim (hnf (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_fixed_mem_disc_frontier f hpar D.isDisc (D.image_eq ⟨f,hf⟩) hfix))
  · exact False.elim (hnf (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier f
      ⟨hlox,D.carrier,D.isDisc,D.image_eq ⟨f,hf⟩⟩ D.isDisc (D.image_eq ⟨f,hf⟩) hfix))
  · exact hell

theorem closedTriangle_finite_vertex_is_elliptic_point
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) :
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (closedTriangleFiniteVertexPoint T i).val∈
      fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic := by
  obtain ⟨g,hgn,hfix⟩:=closedTriangle_finite_vertex_nontrivial_stabilizer T ha hb hc i
  let f:=closedTriangleMobiusEquiv T g
  have hfn:f.val≠1:=by
    intro he
    apply hgn
    apply (closedTriangleMobiusEquiv T).injective
    rw [map_one]
    exact Subtype.ext he
  have hFix:f.val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (closedTriangleFiniteVertexPoint T i).val)=
      _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (closedTriangleFiniteVertexPoint T i).val:=
    (closedTriangleMobiusEquiv_action T g _).trans (congrArg _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint hfix)
  have hp:_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (closedTriangleFiniteVertexPoint T i).val∈P.asFuchsianDisc.carrier:=
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_mem _
  exact ⟨fun _=>hp,f.val,f.property,
    fuchsianDisc_nonidentity_fixed_elliptic P.asFuchsianDisc f.val f.property hfn _ hp hFix,hFix⟩

def closedTriangleEllipticVertexPoint (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) : fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic:=
  ⟨_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (closedTriangleFiniteVertexPoint T i).val,
    closedTriangle_finite_vertex_is_elliptic_point T ha hb hc P i⟩

/-- Every actual elliptic fixed point of the original whole Mobius group is in an original finite vertex orbit. -/
theorem closedTriangle_elliptic_point_vertex_orbit (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (p:fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic) :
    ∃i:{i:Fin 3|0<closedTriangleCornerAngle T i},∃g:closedTriangleMobiusGroup T,
      g • p=closedTriangleEllipticVertexPoint T ha hb hc P i := by
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneOpenModelHomeomorph.symm ⟨p.val,p.property.1 rfl⟩
  have hz:_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z=p.val:=congrArg Subtype.val
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneOpenModelHomeomorph.apply_symm_apply ⟨p.val,p.property.1 rfl⟩)
  obtain ⟨f,hfH,hf,hfix⟩:=p.property.2
  let g₀:triangleConformalGroup T:=(closedTriangleMobiusEquiv T).symm ⟨f,hfH⟩
  have he:(closedTriangleMobiusEquiv T g₀).val=f:=congrArg Subtype.val
    ((closedTriangleMobiusEquiv T).apply_symm_apply ⟨f,hfH⟩)
  have hgfix:g₀.val z=z:=by
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (g₀ • z)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z
    rw [←closedTriangleMobiusEquiv_action T g₀ z,he,hz,hfix]
  have hgn:g₀.val≠1:=by
    intro h
    have hg:g₀=1:=Subtype.ext h
    rw [hg,map_one] at he
    exact hf.1 he.symm
  obtain ⟨i,x,hv,k,hk⟩:=closedTriangle_conformal_fixed_point_vertex_orbit T ha hb hc z g₀.val g₀.property hgn hgfix
  let j:{i:Fin 3|0<closedTriangleCornerAngle T i}:=⟨i,closedTriangle_finite_vertex_angle_pos T x i hv⟩
  have hx:(closedTriangleFiniteVertexPoint T j).val=x.val:=by
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    exact congrArg Subtype.val ((closedTriangleFiniteVertexPoint_vertex T j).symm.trans hv)
  refine ⟨j,closedTriangleMobiusEquiv T k,Subtype.ext ?_⟩
  change (closedTriangleMobiusEquiv T k).val.val p.val=
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (closedTriangleFiniteVertexPoint T j).val
  rw [←hz,closedTriangleMobiusEquiv_action T k z,hk,hx]

/-- The original finite vertices give distinct actual elliptic fixed-point orbits. -/
theorem closedTriangle_elliptic_vertex_orbits_distinct
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (i j:{i:Fin 3|0<closedTriangleCornerAngle T i}) (g:closedTriangleMobiusGroup T)
    (h:g • closedTriangleEllipticVertexPoint T ha hb hc P i=
      closedTriangleEllipticVertexPoint T ha hb hc P j) : i=j := by
  let k:triangleConformalGroup T:=(closedTriangleMobiusEquiv T).symm g
  apply closedTriangle_finite_vertex_orbits_distinct T ha hb hc i j k
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  have hval:=congrArg (fun p:fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic=>p.val) h
  have he:=closedTriangleMobiusEquiv_action T k (closedTriangleFiniteVertexPoint T i).val
  rw [(closedTriangleMobiusEquiv T).apply_symm_apply] at he
  exact he.symm.trans hval

def closedTriangleEllipticVertexClass (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) :
    MulAction.orbitRel.Quotient (closedTriangleMobiusGroup T) (fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic):=
  Quotient.mk'' (closedTriangleEllipticVertexPoint T ha hb hc P i)

theorem closedTriangleEllipticVertexClass_bijective
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    Function.Bijective (closedTriangleEllipticVertexClass T ha hb hc P) := by
  constructor
  · intro i j he
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp (Quotient.exact he)
    exact closedTriangle_elliptic_vertex_orbits_distinct T ha hb hc P j i g hg |>.symm
  · intro q
    induction q using Quotient.inductionOn' with
    | h p=>
      obtain ⟨i,g,hg⟩:=closedTriangle_elliptic_point_vertex_orbit T ha hb hc P p
      refine ⟨i,Quotient.sound ?_⟩
      exact MulAction.mem_orbit_iff.mpr ⟨g,hg⟩

/-- The genuine original finite vertex labels enumerate the actual maximal elliptic subgroup conjugacy classes. -/
def closedTriangleEllipticClassVertexEquiv (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    {i:Fin 3|0<closedTriangleCornerAngle T i}≃FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic :=
  (Equiv.ofBijective (closedTriangleEllipticVertexClass T ha hb hc P)
    (closedTriangleEllipticVertexClass_bijective T ha hb hc P)).trans
      (fuchsianCyclicConjugacyClassesEquiv P.asFuchsianDisc .elliptic).symm

theorem closedTriangle_elliptic_class_card (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic)=
      Nat.card {i:Fin 3|0<closedTriangleCornerAngle T i} :=
  Nat.card_congr (closedTriangleEllipticClassVertexEquiv T ha hb hc P).symm



/-- Faithfulness and exact action compatibility identify the two genuine ambient stabilizer cardinalities. -/
theorem closedTriangle_mobius_stabilizer_card
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (z:ℍ) :
    Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer (closedTriangleMobiusGroup T) (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z))=
      Nat.card ↥(triangleConformalGroup T ⊓ MulAction.stabilizer (ℍ≃ᵢℍ) z) := by
  let S:=triangleConformalGroup T ⊓ MulAction.stabilizer (ℍ≃ᵢℍ) z
  let H:=closedTriangleMobiusGroup T
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)
  let F:S→K:=fun f=>⟨(closedTriangleMobiusEquiv T ⟨f.val,f.property.1⟩).val,
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H _ _).mpr
      ⟨(closedTriangleMobiusEquiv T ⟨f.val,f.property.1⟩).property,
        (closedTriangleMobiusEquiv_action T ⟨f.val,f.property.1⟩ z).trans
          (congrArg _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint f.property.2)⟩⟩
  have hFi:Function.Injective F:=by
    intro f g he
    have heH:closedTriangleMobiusEquiv T ⟨f.val,f.property.1⟩=
        closedTriangleMobiusEquiv T ⟨g.val,g.property.1⟩:=Subtype.ext (congrArg (fun u:K=>u.val) he)
    exact Subtype.ext (congrArg (fun u:triangleConformalGroup T=>u.val) ((closedTriangleMobiusEquiv T).injective heH))
  have hFs:Function.Surjective F:=by
    intro f
    obtain ⟨hfH,hfix⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H _ f.val).mp f.property
    let g:triangleConformalGroup T:=(closedTriangleMobiusEquiv T).symm ⟨f.val,hfH⟩
    have he:(closedTriangleMobiusEquiv T g).val=f.val:=congrArg Subtype.val
      ((closedTriangleMobiusEquiv T).apply_symm_apply ⟨f.val,hfH⟩)
    have hgfix:g.val z=z:=by
      apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
      change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (g • z)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z
      rw [←closedTriangleMobiusEquiv_action T g z,he,hfix]
    refine ⟨⟨g.val,g.property,hgfix⟩,Subtype.ext ?_⟩
    exact he
  exact Nat.card_congr (Equiv.ofBijective F ⟨hFi,hFs⟩).symm

theorem closedTriangleEllipticClassVertexEquiv_apply
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) :
    closedTriangleEllipticClassVertexEquiv T ha hb hc P i=
      Quotient.mk _ (fuchsianCyclicPointStabilizer P.asFuchsianDisc .elliptic
        (closedTriangleEllipticVertexPoint T ha hb hc P i)) := by
  rfl

/-- Each enumerated actual maximal elliptic subgroup has exactly its original reciprocal-angle order. -/
theorem closedTriangle_elliptic_class_order (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) (n:ℕ) (hn:2≤n)
    (hθ:closedTriangleCornerAngle T i.val=Real.pi/(n:ℝ)) :
    fuchsianEllipticClassOrder P.asFuchsianDisc (closedTriangleEllipticClassVertexEquiv T ha hb hc P i)=n := by
  rw [closedTriangleEllipticClassVertexEquiv_apply,fuchsianEllipticClassOrder_mk]
  change Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer (closedTriangleMobiusGroup T)
    (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (closedTriangleFiniteVertexPoint T i).val))=n
  rw [closedTriangle_mobius_stabilizer_card]
  exact closedTriangle_vertex_conformal_stabilizer_card T ha hb hc _ i.val
    (closedTriangleFiniteVertexPoint_vertex T i) n hn hθ

theorem closedTriangle_actual_elliptic_classes_finite
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic) :=
  Finite.of_equiv _ (closedTriangleEllipticClassVertexEquiv T ha hb hc P)

end LowDimensionalTopology.Geometry.Fuchsian
