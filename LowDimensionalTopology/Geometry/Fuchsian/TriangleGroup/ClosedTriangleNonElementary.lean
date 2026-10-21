module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleSignatures
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianElementary
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.ElementaryCyclicClasses
public import Mathlib.GroupTheory.Exponent
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
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
  Set
  Filter
  Topology
open scoped UpperHalfPlane OnePoint

/-- An elementary square law forces each genuine maximal elliptic cyclic subgroup to have actual order two. -/
theorem fuchsianEllipticClassOrder_eq_two_of_square_law
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hSquare:∀f∈H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f→f^2=1)
    (c:FuchsianCyclicConjugacyClasses D .elliptic) : fuchsianEllipticClassOrder D c=2 := by
  induction c using Quotient.inductionOn with
  | _ K=>
    rw [fuchsianEllipticClassOrder_mk]
    let :Finite K.val:=fuchsianMaximalElliptic_finite D K
    let :IsCyclic K.val:=K.property.1.2.1
    have hpow:∀g:K.val,g^2=1:=by
      intro g
      apply Subtype.ext
      by_cases hg:g.val=1
      · change g.val^2=1
        rw [hg,one_pow]
      · exact hSquare g.val (K.property.1.1 g.property)
          (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic g.val hg
            (K.val.subtype.isOfFinOrder (isOfFinOrder_of_finite g)))
    have hd:Nat.card K.val∣2:=by
      rw [←IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one hpow
    exact le_antisymm (Nat.le_of_dvd (by norm_num) hd) (fuchsianMaximalElliptic_card_two_le D K)

/-- An actual ideal vertex, together with the proved genuine finite covolume, forces the original triangle group to be non-elementary. -/
theorem closedTriangle_nonElementary_of_ideal (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (hi:∃i:Fin 3,closedTriangleCornerAngle T i=0) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (closedTriangleMobiusGroup T) := by
  obtain ⟨i,hi⟩:=hi
  obtain ⟨f,hf,hpar,_hfix⟩:=(closedTriangle_ideal_vertex_is_cusp_at T i hi P).2
  obtain ⟨F,hF,harea⟩:=closedTriangle_geometric_finite_domain T ha hb hc P
  exact parabolic_finite_area_nonElementary P.asFuchsianDisc f hf hpar F hF harea

/-- Every corner is genuinely finite when the original triangle has no zero angle. -/
theorem closedTriangle_corner_positive_of_no_zero (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hn:¬∃i:Fin 3,closedTriangleCornerAngle T i=0) (i:Fin 3) :
    0<closedTriangleCornerAngle T i := by
  have hnonneg:0≤closedTriangleCornerAngle T i:=by
    rw [←closedTriangleCornerCycle_angle]
    exact (closedTriangleCornerCycle T i).toDiscTriangle.alpha_mem_Ico.1
  exact lt_of_le_of_ne hnonneg (fun h=>hn ⟨i,h.symm⟩)

/-- A genuine all-finite hyperbolic triangle has a reciprocal-angle corner of order greater than two. -/
theorem closedTriangle_finite_corner_order_gt_two (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma)
    (hp:∀i:Fin 3,0<closedTriangleCornerAngle T i) :
    ∃i:{i:Fin 3|0<closedTriangleCornerAngle T i},3≤closedTriangleFiniteCornerOrder T ha hb hc i := by
  by_contra hn
  push Not at hn
  have htwo:∀i:{i:Fin 3|0<closedTriangleCornerAngle T i},closedTriangleFiniteCornerOrder T ha hb hc i=2:=by
    intro i
    have hl:=(closedTriangleFiniteCornerOrder_spec T ha hb hc i).1
    have hu:=hn i
    omega
  have hangle:∀i:Fin 3,closedTriangleCornerAngle T i=Real.pi/2:=by
    intro i
    have h:=(closedTriangleFiniteCornerOrder_spec T ha hb hc ⟨i,hp i⟩).2
    rw [htwo] at h
    exact h
  have hα:=hangle 0
  have hβ:=hangle 1
  have hγ:=hangle 2
  change T.alpha=Real.pi/2 at hα
  change T.beta=Real.pi/2 at hβ
  change T.gamma=Real.pi/2 at hγ
  have hsum:=T.angle_sum_lt_pi
  rw [hα,hβ,hγ] at hsum
  linarith [Real.pi_pos]


/-- Distinct actual finite corners give distinct original elliptic maximal cyclic classes. -/
theorem closedTriangle_finite_elliptic_classes_nontrivial
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (hp:∀i:Fin 3,0<closedTriangleCornerAngle T i) :
    Nontrivial (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic) := by
  let E:=closedTriangleEllipticClassVertexEquiv T ha hb hc P
  let i0:{i:Fin 3|0<closedTriangleCornerAngle T i}:=⟨0,hp 0⟩
  let i1:{i:Fin 3|0<closedTriangleCornerAngle T i}:=⟨1,hp 1⟩
  refine ⟨⟨E i0,E i1,?_⟩⟩
  intro he
  have hv: (0:Fin 3)=1:=congrArg Subtype.val (E.injective he)
  exact (by decide : (0:Fin 3)≠1) hv

/-- Every original integral finite/ideal hyperbolic triangle has a non-elementary full conformal Mobius image. -/
theorem closedTriangle_nonElementary (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (closedTriangleMobiusGroup T) := by
  classical
  by_cases hi:∃i:Fin 3,closedTriangleCornerAngle T i=0
  · exact closedTriangle_nonElementary_of_ideal T ha hb hc P hi
  · have hp:=closedTriangle_corner_positive_of_no_zero T hi
    intro he
    rcases elementary_fuchsian_cyclic_or_elliptic_square_eq_one P.asFuchsianDisc he with hCyclic|hSquare
    · let :=cyclic_cyclic_classes_subsingleton P.asFuchsianDisc hCyclic .elliptic
      obtain ⟨c,d,hcd⟩:=(closedTriangle_finite_elliptic_classes_nontrivial T ha hb hc P hp).exists_pair_ne
      exact hcd (Subsingleton.elim c d)
    · obtain ⟨i,hbig⟩:=closedTriangle_finite_corner_order_gt_two T ha hb hc hp
      have htwo:=fuchsianEllipticClassOrder_eq_two_of_square_law P.asFuchsianDisc hSquare
        (closedTriangleEllipticClassVertexEquiv T ha hb hc P i)
      rw [closedTriangleFiniteCornerOrder_actual] at htwo
      omega

/-- Every original integral finite/ideal triangle is of the first kind in its actual invariant half-plane. -/
theorem closedTriangle_firstKind (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    P.asFuchsianDisc.IsFirstKind := by
  let triangleFirstKindNativeAction:=P.nativeAction
  obtain ⟨S,hS,harea⟩:=triangleConformalMobius_finite_measureDomain T ha hb hc P
  exact native_finite_aeArea_firstKind P (closedTriangle_nonElementary T ha hb hc P) hS harea

/-- The complete forward signature statement for the actual full triangle group, with the first-kind assertion proved geometrically. -/
theorem closedTriangle_firstKind_and_actual_signature
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    P.asFuchsianDisc.IsFirstKind ∧
      HasCofiniteFuchsianSignature P.asFuchsianDisc 0 (closedTriangleFiniteCornerOrderList T ha hb hc)
        (Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}) :=
  ⟨closedTriangle_firstKind T ha hb hc P,closedTriangle_actual_cofinite_signature T ha hb hc P⟩

end LowDimensionalTopology.Geometry.Fuchsian
