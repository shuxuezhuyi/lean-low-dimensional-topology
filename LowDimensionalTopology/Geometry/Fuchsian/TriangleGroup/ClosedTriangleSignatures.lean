module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleCuspSphere
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleEllipticClasses
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofiniteSignatures
public import Mathlib.Data.List.FinRange
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
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set
  Filter
  Topology
open scoped UpperHalfPlane

theorem closedTriangle_corner_isIntegral (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (i:Fin 3) : IsIntegralTriangleAngle (closedTriangleCornerAngle T i) := by
  fin_cases i <;> assumption

theorem closedTriangle_finite_corner_order_exists (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) :
    ∃n:ℕ,2≤n ∧ closedTriangleCornerAngle T i.val=Real.pi/(n:ℝ) :=
  (closedTriangle_corner_isIntegral T ha hb hc i.val).resolve_left (ne_of_gt i.property)

/-- The original reciprocal-angle denominator at an actual finite corner, chosen from its proved integral-angle data. -/
def closedTriangleFiniteCornerOrder (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) : ℕ :=
  (closedTriangle_finite_corner_order_exists T ha hb hc i).choose

theorem closedTriangleFiniteCornerOrder_spec (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) :
    2≤closedTriangleFiniteCornerOrder T ha hb hc i ∧
      closedTriangleCornerAngle T i.val=Real.pi/(closedTriangleFiniteCornerOrder T ha hb hc i:ℝ) :=
  (closedTriangle_finite_corner_order_exists T ha hb hc i).choose_spec

/-- All actual finite corners are enumerated, including repeated orders at distinct corners. -/
def closedTriangleFiniteCornerOrderList (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) : List ℕ := by
  classical
  exact List.ofFn (fun j=>closedTriangleFiniteCornerOrder T ha hb hc
    ((Fintype.equivFin {i:Fin 3|0<closedTriangleCornerAngle T i}).symm j))

theorem closedTriangleFiniteCornerOrder_actual (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (i:{i:Fin 3|0<closedTriangleCornerAngle T i}) :
    fuchsianEllipticClassOrder P.asFuchsianDisc (closedTriangleEllipticClassVertexEquiv T ha hb hc P i)=
      closedTriangleFiniteCornerOrder T ha hb hc i :=
  closedTriangle_elliptic_class_order T ha hb hc P i _
    (closedTriangleFiniteCornerOrder_spec T ha hb hc i).1
    (closedTriangleFiniteCornerOrder_spec T ha hb hc i).2

/-- The original corner order list and the actual maximal elliptic subgroup class list agree as full multisets, not merely as sets. -/
theorem closedTriangleFiniteCornerOrderList_perm (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    letI:=closedTriangle_actual_elliptic_classes_finite T ha hb hc P
    (closedTriangleFiniteCornerOrderList T ha hb hc).Perm (fuchsianEllipticOrderList P.asFuchsianDisc) := by
  classical
  let :Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    closedTriangle_actual_elliptic_classes_finite T ha hb hc P
  let :=Fintype.ofFinite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic)
  let V:={i:Fin 3|0<closedTriangleCornerAngle T i}
  let C:=FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic
  let E:=closedTriangleEllipticClassVertexEquiv T ha hb hc P
  let eV:Fin (Fintype.card V)≃V:=(Fintype.equivFin V).symm
  let eC:Fin (Fintype.card C)≃C:=(Fintype.equivFin C).symm
  have hP:(List.ofFn (fun j=>E (eV j))).Perm (List.ofFn (fun j=>eC j)):=by
    apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr (E.injective.comp eV.injective))
      (List.nodup_ofFn.mpr eC.injective)).mpr
    intro c
    simp only [List.mem_ofFn]
    constructor
    · intro _h
      exact ⟨eC.symm c,eC.apply_symm_apply c⟩
    · intro _h
      exact ⟨eV.symm (E.symm c),by
        change E (eV (eV.symm (E.symm c)))=c
        rw [eV.apply_symm_apply,E.apply_symm_apply]⟩
  have h:=hP.map (fuchsianEllipticClassOrder P.asFuchsianDisc)
  change (List.ofFn (fun j=>closedTriangleFiniteCornerOrder T ha hb hc (eV j))).Perm
    (List.ofFn (fun j=>fuchsianEllipticClassOrder P.asFuchsianDisc (eC j)))
  simpa only [List.map_ofFn,Function.comp_def,E,closedTriangleFiniteCornerOrder_actual] using h

/-- Every genuine integral triangle has the original cofinite signature: actual sphere genus, the complete reciprocal-angle order multiset, and exactly its zero-angle cusp count. -/
theorem closedTriangle_actual_cofinite_signature (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    HasCofiniteFuchsianSignature P.asFuchsianDisc 0 (closedTriangleFiniteCornerOrderList T ha hb hc)
      (Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}) where
  ellipticClassesFinite:=closedTriangle_actual_elliptic_classes_finite T ha hb hc P
  parabolicClassesFinite:=closedTriangle_cyclic_classes_finite T ha hb hc P .parabolic
  compact:=closedTriangle_cusp_completion_compact T ha hb hc P
  topologicalGenus:=closedTriangle_cusp_completion_genus_zero T ha hb hc P
  ellipticOrders:=closedTriangleFiniteCornerOrderList_perm T ha hb hc P
  cuspCount:=(closedTriangle_actual_cusp_count T ha hb hc P).symm


/-- The denominator construction returns the specified original reciprocal-angle order exactly. -/
theorem closedTriangleFiniteCornerOrder_eq_of_angle
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (i:{i:Fin 3|0<closedTriangleCornerAngle T i})
    (n:ℕ) (hn:2≤n) (hθ:closedTriangleCornerAngle T i.val=Real.pi/(n:ℝ)) :
    closedTriangleFiniteCornerOrder T ha hb hc i=n := by
  let P:=closedTriangleMobiusData T ha hb hc
  exact (closedTriangleFiniteCornerOrder_actual T ha hb hc P i).symm.trans
    (closedTriangle_elliptic_class_order T ha hb hc P i n hn hθ)

/-- Every prescribed actual finite-corner order appears once per corner in the original signature list. -/
theorem closedTriangleFiniteCornerOrderList_eq_of_angles
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma)
    (n:{i:Fin 3|0<closedTriangleCornerAngle T i}→ℕ) (hn:∀i,2≤n i)
    (hθ:∀i,closedTriangleCornerAngle T i.val=Real.pi/(n i:ℝ)) :
    closedTriangleFiniteCornerOrderList T ha hb hc=
      List.ofFn (fun j=>n ((Fintype.equivFin {i:Fin 3|0<closedTriangleCornerAngle T i}).symm j)) := by
  classical
  unfold closedTriangleFiniteCornerOrderList
  apply congrArg List.ofFn
  funext j
  exact closedTriangleFiniteCornerOrder_eq_of_angle T ha hb hc _ _ (hn _) (hθ _)

end LowDimensionalTopology.Geometry.Fuchsian
