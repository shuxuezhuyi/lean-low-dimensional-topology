module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.ComplexJordanParametrization
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.CircleNoTriod
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeSideArms
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.JordanSideIncidences
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

theorem complex_segment_real_parameter_injOn {a b : ℂ} (hab : a≠b) :
    InjOn (fun z : ℂ=>((z-a)/(b-a)).re) (segment ℝ a b) := by
  intro z hz w hw he
  have hz' := (polygonComplex_mem_segment_iff hab).mp hz
  have hw' := (polygonComplex_mem_segment_iff hab).mp hw
  have hcomplex : (z-a)/(b-a)=(w-a)/(b-a) := Complex.ext he (hz'.1.trans hw'.1.symm)
  have hs : z-a=w-a := (div_left_inj' (sub_ne_zero.mpr hab.symm)).mp hcomplex
  linear_combination hs

/-- A genuine Jordan curve cannot locally be contained in a single closed segment at
one of its endpoints, even after a genuine ambient homeomorphism. -/
theorem complexJordan_not_segment_endpoint {C : Set ℂ} (hC : IsComplexJordanCurve C)
    {x : ℂ} (hx : x∈C) (g : ℂ≃ₜℂ) (a b : ℂ) (hab : a≠b) (hxa : g x=a)
    (hNear : ∀ᶠz in 𝓝 x,z∈C →g z∈segment ℝ a b) : False := by
  let e := complexJordanCircleHomeomorph hC
  let E : Circle→ℂ:=fun v=>(e v).val
  have hEc : Continuous E:=continuous_subtype_val.comp e.continuous
  have hEi : Function.Injective E:=Subtype.val_injective.comp e.injective
  let u:=e.symm ⟨x,hx⟩
  have hEu : E u=x:=congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
  have hG : ∀ᶠv in 𝓝 u,g (E v)∈segment ℝ a b := by
    have hT : Tendsto E (𝓝 u) (𝓝 x) := hEu ▸ hEc.continuousAt
    filter_upwards [hT.eventually hNear] with v hv
    exact hv (e v).property
  obtain ⟨A,B,hA,hB,hd,hAs,hBs,huA,huB⟩:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.circle_exists_two_preconnected_approaches u hG
  let τ : Circle→ℝ:=fun v=>((g (E v)-a)/(b-a)).re
  have hτ : Continuous τ:=by fun_prop
  have hτu : τ u=0 := by simp only [τ,hEu,hxa,sub_self,zero_div,Complex.zero_re]
  have hPositive (v : Circle) (hv : g (E v)∈segment ℝ a b) (hvu : v≠u) : 0<τ v := by
    have hn : 0≤τ v := ((polygonComplex_mem_segment_iff hab).mp hv).2.1
    apply lt_of_le_of_ne hn
    intro he
    have ha : ((a-a)/(b-a)).re=0 := by simp
    have hvEq : g (E v)=a:=complex_segment_real_parameter_injOn hab hv
      (left_mem_segment ℝ a b) (by exact he.symm.trans ha.symm)
    apply hvu
    apply hEi
    apply g.injective
    rw [hvEq,hEu,hxa]
  have hApos : τ '' A⊆Ioi (0 : ℝ) := by
    rintro z ⟨v,hv,rfl⟩
    exact hPositive v (hAs hv).1 (hAs hv).2
  have hBpos : τ '' B⊆Ioi (0 : ℝ) := by
    rintro z ⟨v,hv,rfl⟩
    exact hPositive v (hBs hv).1 (hBs hv).2
  have hAcl : 0∈closure (τ '' A) := by
    rw [←hτu]
    exact hτ.continuousOn.image_closure ⟨u,huA,rfl⟩
  have hBcl : 0∈closure (τ '' B) := by
    rw [←hτu]
    exact hτ.continuousOn.image_closure ⟨u,huB,rfl⟩
  obtain ⟨t,⟨v,hv,htv⟩,⟨w,hw,htw⟩⟩:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.real_preconnected_common_lower_endpoint_inter
    (hA.image τ hτ.continuousOn) hApos hBpos hAcl hBcl
  have hvw : v=w := by
    apply hEi
    apply g.injective
    exact complex_segment_real_parameter_injOn hab (hAs hv).1 (hBs hw).1 (htv.trans htw.symm)
  exact Set.disjoint_left.mp hd hv (hvw ▸ hw)


/-- A genuine native original vertex cannot be the endpoint of only one original side.
Local finiteness and the original Jordan boundary exclude a local one-sided segment. -/
theorem NativeGeodesicSideIntervals.endpoint_has_second_incident_side
    {P : PoincarePolygon ℍ} (D : NativeGeodesicSideIntervals P)
    (C : Set ℂ) (hC : IsComplexJordanCurve C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (x : ℍ) (s : P.Side) (hx : x∈D.endpoints s) :
    ∃t : P.Side,t≠s ∧x∈t.val := by
  by_contra hn
  have hUnique (t : P.Side) (ht : x∈t.val) : t=s := by
    by_contra hne
    exact hn ⟨t,hne,ht⟩
  have hxs : x∈s.val:=D.endpoints_subset_side s hx
  let xP : P.Point:=⟨x,P.side_subset_carrier s hxs⟩
  obtain ⟨r,hr,hAvoid⟩:=PoincareSidePairing.exists_ball_incident_sides
    D.locallyFinite D.side_geometry.side_closed xP
  have hNear (y : ℍ) (hy : y∈Metric.ball x r) (hB : y∈P.boundary) : y∈s.val := by
    obtain ⟨t,ht,hyt⟩:=mem_sUnion.mp hB
    let t' : P.Side:=⟨t,ht⟩
    have hxt : x∈t'.val:=hAvoid y hy t' hyt
    exact hUnique t' hxt ▸ hyt
  let f : ℍ→ℂ:=fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)
  have hCo : IsOpenMap ((↑) : 𝔻→ℂ) := by
    change IsOpenMap (Subtype.val : Metric.ball (0 : ℂ) 1→ℂ)
    exact Metric.isOpen_ball.isOpenMap_subtype_val
  have hfo : IsOpenMap f:=hCo.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap
  have hxC : f x∈C := by
    have hB : x∈P.boundary:=mem_sUnion.mpr ⟨s.val,s.property,hxs⟩
    rw [hBoundary] at hB
    exact hB
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (D.startPoint s)
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (D.endPoint s)
  have hab : a≠b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (D.endpoint_ne s)
  have hLocal : ∀ᶠz in 𝓝 (f x),z∈C →_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph z∈segment ℝ a b := by
    filter_upwards [(hfo _ Metric.isOpen_ball).mem_nhds ⟨x,Metric.mem_ball_self hr,rfl⟩] with z hz hzC
    obtain ⟨y,hy,rfl⟩:=hz
    have hyB : y∈P.boundary := by rw [hBoundary];exact hzC
    have hys : y∈nativeCompactifiedSide (D.startPoint s) (D.endPoint s):=
      D.side_eq s ▸ hNear y hy hyB
    have hSeg := (nativeCompactifiedSide_iff_klein_segment _ _ y).mp hys
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y) : ℂ)∈segment ℝ a b
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed]
    exact hSeg
  have hClosed : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph (f x)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)) :=
    by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) : ℂ)=_
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed _
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈({D.startPoint s,D.endPoint s} : Set 𝕔𝔻) at hx
  simp only [mem_insert_iff,mem_singleton_iff] at hx
  rcases hx with hx | hx
  · apply complexJordan_not_segment_endpoint hC hxC _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph a b hab
      (hClosed.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hx)) hLocal
  · apply complexJordan_not_segment_endpoint hC hxC _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph b a hab.symm
      (hClosed.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hx))
    filter_upwards [hLocal] with z hz hzC
    rw [segment_symm]
    exact hz hzC



/-- Every actual native original vertex has exactly its two distinct original side
labels. Both existence and exhaustion follow from the literal original Jordan geometry. -/
theorem NativeGeodesicSideIntervals.vertex_exactly_two_incident_sides
    {P : PoincarePolygon ℍ} (D : NativeGeodesicSideIntervals P)
    (C : Set ℂ) (hC : IsComplexJordanCurve C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (x : ℍ) (hx : x∈D.vertices) :
    ∃s t : P.Side,s≠t ∧x∈s.val ∧x∈t.val ∧
      ∀v : P.Side,x∈v.val →v=s ∨v=t := by
  obtain ⟨s,hs⟩:=mem_iUnion.mp hx
  have hxs : x∈s.val:=D.endpoints_subset_side s hs
  obtain ⟨t,htne,hxt⟩:=D.endpoint_has_second_incident_side C hC hBoundary x s hs
  refine ⟨s,t,htne.symm,hxs,hxt,?_⟩
  intro v hxv
  by_cases hvs : v=s
  · exact Or.inl hvs
  by_cases hvt : v=t
  · exact Or.inr hvt
  let S : Fin 3→P.Side:=![s,t,v]
  have hInj : Function.Injective S := by
    intro i j hij
    fin_cases i <;>fin_cases j <;>simp_all [S]
  have hInc : ∀i,x∈(S i).val := by
    intro i
    fin_cases i
    · exact hxs
    · exact hxt
    · exact hxv
  exact (D.no_three_incident_sides C hC hBoundary x S hInj hInc).elim

end LowDimensionalTopology.Geometry.Polygon
