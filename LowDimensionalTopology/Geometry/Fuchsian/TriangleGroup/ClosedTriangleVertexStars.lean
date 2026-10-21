/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleSideStars
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set
  Topology
open scoped UpperHalfPlane

def closedTriangleVertex (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : Fin 3→_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel:=![T.a,T.b,T.c]
def closedTriangleCornerCycle (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : Fin 3→_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle:=![T,T.cycle,T.cycle.cycle]
def closedTriangleCornerAngle
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : Fin 3→ℝ:=![T.alpha,T.beta,T.gamma]
def closedTriangleAdjacentSides (i : Fin 3) : Fin 2→Fin 3:=![(2:Fin 3),1] |> fun a=>
  ![a,![(0:Fin 3),2],![(1:Fin 3),0]] i

theorem closedTriangleAdjacentSides_iff (i j : Fin 3) :
    j≠i ↔ j=closedTriangleAdjacentSides i 0 ∨j=closedTriangleAdjacentSides i 1 := by
  fin_cases i <;> fin_cases j <;> decide

theorem closedTriangleCornerCycle_vertex
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i : Fin 3) :
    (closedTriangleCornerCycle T i).a=closedTriangleVertex T i := by fin_cases i <;> rfl

theorem closedTriangleCornerCycle_interior
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i : Fin 3) :
    (closedTriangleCornerCycle T i).interior=T.interior := by
  fin_cases i
  · rfl
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.cycle_interior T
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.cycle_interior T.cycle).trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.cycle_interior T)

theorem closedTriangleCornerCycle_angle
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i : Fin 3) :
    (closedTriangleCornerCycle T i).alpha=closedTriangleCornerAngle T i := by
  fin_cases i <;> rfl

theorem closedTriangleCornerCycle_first_support
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i : Fin 3) :
    (closedTriangleCornerCycle T i).toDiscTriangle.sideLineC.toHalfPlane=
      T.nativeLine (closedTriangleAdjacentSides i 0) := by fin_cases i <;> rfl

theorem closedTriangleCornerCycle_second_support
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i : Fin 3) :
    (closedTriangleCornerCycle T i).toDiscTriangle.sideLineB.toHalfPlane=
      T.nativeLine (closedTriangleAdjacentSides i 1) := by fin_cases i <;> rfl

theorem closedTriangle_vertex_coordinate
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i : Fin 3)
    (x : ℍ)
    (hv : closedTriangleVertex T i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x) :
    T.nativeCoordinate x=![(0:ℝ×ℝ),(1,0),(0,1)] i := by
  fin_cases i
  · have hD : T.toDiscTriangle.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x):=by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph T.a=_
      rw [show T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x from hv,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior]
    change T.toDiscTriangle.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x))=(0,0)
    rw [←hD,T.toDiscTriangle.coordinate_a]
  · have hD : T.toDiscTriangle.b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x):=by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph T.b=_
      rw [show T.b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x from hv,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior]
    change T.toDiscTriangle.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x))=(1,0)
    rw [←hD,T.toDiscTriangle.coordinate_b]
  · have hD : T.toDiscTriangle.c=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x):=by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph T.c=_
      rw [show T.c=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x from hv,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior]
    change T.toDiscTriangle.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x))=(0,1)
    rw [←hD,T.toDiscTriangle.coordinate_c]

theorem closedTriangle_vertex_side_iff
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i j : Fin 3)
    (x : (closedTrianglePoincarePolygon T).Point)
    (hv : closedTriangleVertex T i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x.val) : x.val∈T.nativeSide j ↔j≠i := by
  rw [closedTriangle_nativeSide_iff,and_iff_right x.property]
  dsimp only [closedTriangleCut]
  rw [closedTriangle_vertex_coordinate T i x.val hv]
  fin_cases i <;> fin_cases j <;> norm_num

theorem closedTrianglePoincare_native_reflection_sides
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    ∀s:(closedTrianglePoincarePolygon T).Side,∃L:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s.val⊆L.carrier ∧
      (closedTrianglePoincarePairing T).element s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L := by
  intro s
  let j:=(closedTrianglePoincareSideEquiv T).symm s
  refine ⟨T.nativeLine j,?_,rfl⟩
  intro x hx
  have hx' : x∈T.nativeSide j:=by rwa [closedTrianglePoincareSideEquiv_symm]
  rw [T.nativeSide_eq_carrier_inter_line] at hx'
  exact hx'.2

/-- Every finite genuine corner of an arbitrary ideal or finite triangle has the entire actual local tessellation star. -/
theorem closedTriangle_integral_vertex_local_condition
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (x : (closedTrianglePoincarePolygon T).Point) (i : Fin 3)
    (hv : closedTriangleVertex T i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x.val)
    (hIa : IsIntegralTriangleAngle (closedTriangleCornerAngle T i)) :
    ((closedTrianglePoincarePairing T).project ⁻¹' {(closedTrianglePoincarePairing T).project (1,x)}).Finite ∧
      ∃r₀ : ℝ,0<r₀ ∧ ∀r : ℝ,0<r → r≤r₀ → (closedTrianglePoincarePairing T).LocalTessellation (1,x) r := by
  let S:=closedTrianglePoincarePairing T
  let U:=closedTriangleCornerCycle T i
  have hUa : U.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x.val:=(closedTriangleCornerCycle_vertex T i).trans hv
  let C:=U.finiteCornerAtA x.val hUa
  let R:=C.rayAB
  let Q:=C.rayAC
  let s:=closedTrianglePoincareSideEquiv T (closedTriangleAdjacentSides i 0)
  let t:=closedTrianglePoincareSideEquiv T (closedTriangleAdjacentSides i 1)
  have hRline : R.supportLine=T.nativeLine (closedTriangleAdjacentSides i 0):=
    C.supportAB.trans (closedTriangleCornerCycle_first_support T i)
  have hQline : Q.supportLine=T.nativeLine (closedTriangleAdjacentSides i 1):=
    C.supportAC.trans (closedTriangleCornerCycle_second_support T i)
  have hR : S.element s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine:=by
    change closedTrianglePoincareElement T (closedTrianglePoincareSideEquiv T _)=_
    simp only [closedTrianglePoincareElement,Equiv.symm_apply_apply]
    rw [hRline]
    rfl
  have hQ : S.element t=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry Q.supportLine:=by
    change closedTrianglePoincareElement T (closedTrianglePoincareSideEquiv T _)=_
    simp only [closedTrianglePoincareElement,Equiv.symm_apply_apply]
    rw [hQline]
    rfl
  have hS : s.val=(closedTrianglePoincarePolygon T).carrier∩R.supportLine.carrier:=by
    change T.nativeSide _=_
    exact (T.nativeSide_eq_carrier_inter_line _).trans
      (congrArg₂ (fun A B:Set ℍ=>A∩B) (closedTrianglePoincarePolygon_carrier T).symm
        (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier hRline.symm))
  have hT : t.val=(closedTrianglePoincarePolygon T).carrier∩Q.supportLine.carrier:=by
    change T.nativeSide _=_
    exact (T.nativeSide_eq_carrier_inter_line _).trans
      (congrArg₂ (fun A B:Set ℍ=>A∩B) (closedTrianglePoincarePolygon_carrier T).symm
        (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier hQline.symm))
  have hxs : x.val∈s.val:=by rw [hS];exact ⟨x.property,R.start_mem_support⟩
  have hxt : x.val∈t.val:=by rw [hT];exact ⟨x.property,Q.start_mem_support⟩
  have hAll (u:(closedTrianglePoincarePolygon T).Side) (hu:x.val∈u.val) : u=s ∨u=t:=by
    obtain ⟨j,rfl⟩:=(closedTrianglePoincareSideEquiv T).surjective u
    have hji : j≠i:=(closedTriangle_vertex_side_iff T i j x hv).mp hu
    rcases (closedTriangleAdjacentSides_iff i j).mp hji with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hGerm : ∃r : ℝ,0<r ∧∀z : ℍ,dist z x.val<r →
      (z∈(closedTrianglePoincarePolygon T).carrier ↔z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R Q)) := by
    obtain ⟨r,hr,hG⟩:=closedTriangle_finiteCorner_closure_germ U x.val hUa
    refine ⟨r,hr,fun z hz=>?_⟩
    have hC : z∈(closedTrianglePoincarePolygon T).carrier ↔z∈(closedTrianglePoincarePolygon U).carrier:=by
      rw [closedTrianglePoincarePolygon_carrier,closedTrianglePoincarePolygon_carrier,
        closedTriangleCornerCycle_interior]
    exact hC.trans (hG z hz)
  have hAngle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R Q=U.alpha:=closedTriangle_finiteCorner_angle U x.val hUa
  have hPos : 0<U.alpha:=hAngle ▸ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_pos R Q C.proper
  have hI : IsIntegralTriangleAngle U.alpha:=by rwa [closedTriangleCornerCycle_angle]
  rcases hI with hzero|⟨n,hn,hnAngle⟩
  · rw [hzero] at hPos
    exact False.elim (lt_irrefl 0 hPos)
  · have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R Q=Real.pi/(n:ℝ):=hAngle.trans hnAngle
    exact ⟨S.native_integral_reflection_vertex_fiber_finite (closedTrianglePoincare_native_reflection_sides T)
      x s t hxs hxt hAll R Q hR hQ n hn hA,
      S.native_integral_reflection_vertex_local_radius (closedTrianglePoincare_native_reflection_sides T)
        (closedTrianglePoincareSide_locallyFinite T) (closedTrianglePoincareSide_isClosed T)
        x s t R Q hAll hR hQ hS hT C.proper hGerm n hn hA⟩

theorem closedTriangle_coordinate_vertex
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i : Fin 3)
    (x : ℍ)
    (hF : T.nativeCoordinate x=![(0:ℝ×ℝ),(1,0),(0,1)] i) :
    closedTriangleVertex T i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior]
  fin_cases i
  · change T.toDiscTriangle.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)
    apply T.toDiscTriangle.coordinate_injective
    rw [T.toDiscTriangle.coordinate_a]
    exact hF.symm
  · change T.toDiscTriangle.b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)
    apply T.toDiscTriangle.coordinate_injective
    rw [T.toDiscTriangle.coordinate_b]
    exact hF.symm
  · change T.toDiscTriangle.c=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)
    apply T.toDiscTriangle.coordinate_injective
    rw [T.toDiscTriangle.coordinate_c]
    exact hF.symm

/-- A genuine intersection of two original side slices is one actual finite vertex, never an unrecorded ideal point. -/
theorem closedTriangle_multiple_side_point_is_vertex
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (x : (closedTrianglePoincarePolygon T).Point) (i j : Fin 3) (hne:i≠j)
    (hi:x.val∈T.nativeSide i) (hj:x.val∈T.nativeSide j) :
    ∃k:Fin 3,closedTriangleVertex T k=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x.val := by
  have hI:=((closedTriangle_nativeSide_iff T i x.val).mp hi).2
  have hJ:=((closedTriangle_nativeSide_iff T j x.val).mp hj).2
  fin_cases i <;> fin_cases j
  all_goals first
    | exact False.elim (hne rfl)
    | (norm_num [closedTriangleCut] at hI hJ
       first
       | (refine ⟨0,closedTriangle_coordinate_vertex T 0 x.val ?_⟩
          change T.nativeCoordinate x.val=(0,0)
          apply Prod.ext <;> dsimp <;> linarith)
       | (refine ⟨1,closedTriangle_coordinate_vertex T 1 x.val ?_⟩
          change T.nativeCoordinate x.val=(1,0)
          apply Prod.ext <;> dsimp <;> linarith)
       | (refine ⟨2,closedTriangle_coordinate_vertex T 2 x.val ?_⟩
          change T.nativeCoordinate x.val=(0,1)
          apply Prod.ext <;> dsimp <;> linarith))

/--
All original native points of every integral-angle triangle, including all ideal configurations,
have a finite entire gluing class and every sufficiently small actual local tessellation ball.
-/
theorem closedTriangle_integral_all_local_conditions
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (x:(closedTrianglePoincarePolygon T).Point) :
    ((closedTrianglePoincarePairing T).project ⁻¹' {(closedTrianglePoincarePairing T).project (1,x)}).Finite ∧
      ∃r₀ : ℝ,0<r₀ ∧ ∀r : ℝ,0<r → r≤r₀ → (closedTrianglePoincarePairing T).LocalTessellation (1,x) r := by
  let S:=closedTrianglePoincarePairing T
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  by_cases hI:x.val∈T.interior
  · exact ⟨by rw [S.project_fiber_eq_singleton_of_interior (1,x) hI];exact Set.finite_singleton _,
      S.interior_local_radius T.interior_isOpen x hI⟩
  · have hp:=x.property
    change x.val∈T.interior ∨x.val∈⋃₀(range T.nativeSide) at hp
    have hB:=hp.resolve_left hI
    obtain ⟨s,⟨i,rfl⟩,hxi⟩:=hB
    by_cases hUnique:∀j:Fin 3,x.val∈T.nativeSide j→j=i
    · exact closedTriangle_nonvertex_local_condition T x i hxi hUnique
    · push Not at hUnique
      obtain ⟨j,hxj,hji⟩:=hUnique
      obtain ⟨k,hk⟩:=closedTriangle_multiple_side_point_is_vertex T x i j (Ne.symm hji) hxi hxj
      have hIa:IsIntegralTriangleAngle (closedTriangleCornerAngle T k):=by
        fin_cases k <;> assumption
      exact closedTriangle_integral_vertex_local_condition T x k hk hIa

/-- The complete original local tessellation condition is proved for every finite or ideal
integral-angle triangle, with no compactness, whole-fiber, uniform-radius or FD premise. -/
theorem closedTriangle_integral_local_tessellation
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    (closedTrianglePoincarePairing T).FiniteFiberLocalTessellationCondition :=
  ⟨fun x=>(closedTriangle_integral_all_local_conditions T ha hb hc x).1,
    fun x=>(closedTriangle_integral_all_local_conditions T ha hb hc x).2⟩

end LowDimensionalTopology.Geometry.Fuchsian
