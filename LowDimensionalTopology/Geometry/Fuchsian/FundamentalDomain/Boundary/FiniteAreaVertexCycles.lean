/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.StraightConvexAngles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaPolygonBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSelfPairedSides
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Complex.UnitDisc Topology UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance finiteCycleSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance finiteCycleSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Positive integral stabilizer and cycle sizes with at least three incident tiles have a uniformly positive true vertex weight. -/
theorem integral_vertex_cycle_weight_lower (p m : ℕ) (hp : 0 < p) (hm : 0 < m)
    (hinc : 3 ≤ p*m) : (1:ℝ)/3 ≤ (m:ℝ)-2/(p:ℝ) := by
  by_cases hp1 : p=1
  · rw [hp1] at hinc ⊢
    norm_num at hinc ⊢
    have hm3 : (3:ℝ) ≤ (m:ℝ):=by exact_mod_cast hinc
    linarith
  by_cases hp2 : p=2
  · have hm2 : 2 ≤ m:=by rw [hp2] at hinc;omega
    have hm2R : (2:ℝ) ≤ (m:ℝ):=by exact_mod_cast hm2
    norm_num [hp2]
    linarith
  · have hp3 : 3 ≤ p:=by omega
    have hp3R : (3:ℝ) ≤ (p:ℝ):=by exact_mod_cast hp3
    have hmR : (1:ℝ) ≤ (m:ℝ):=by exact_mod_cast hm
    have hdiv : (2:ℝ)/(p:ℝ) ≤ 2/3:=div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3R
    linarith

/-- Every actual finite vertex cycle carries at least pi/3 of genuine corner deficit, using its exact original stabilizer and actual angle sum. -/
theorem finite_vertex_cycle_angle_deficit_lower {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier)
    (hx : IsFuchsianPolygonVertex P D x) :
    Real.pi/3 ≤ (fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x):ℝ)*Real.pi-
      ∑y∈(hD.locallyFinite.cycle_finite x).toFinset,fuchsianPolygonAngle P D y := by
  have hinc:=hD.vertex_incident_card_ge_three hx
  rw [hD.locallyFinite.incident_card_eq_order_mul_cycleLength x] at hinc
  have hw:=integral_vertex_cycle_weight_lower (fuchsianPointOrder P x)
    (fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x)) (P.pointOrder_pos x)
    (hD.locallyFinite.cycleLength_pos x) hinc
  rw [sum_cycle_angles_eq_two_pi_div_pointOrder hD x]
  have hm:=mul_le_mul_of_nonneg_right hw Real.pi_pos.le
  convert hm using 1 <;> ring

/-- A finite real-ordered list of actual closed-polygon points and its genuine ideal infinity endpoint gives a true original fundamental-polygon area/angle budget. -/
theorem finite_area_polygon_ordered_fan_budget {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) {n : ℕ}
    (x : Fin (n+1)→P.domain.carrier)
    (hx : ∀i,x i∈closure D) (horder : StrictMono (fun i=>(P.halfPlaneCoordinate (x i)).re))
    (hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈
      closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel '' (P.finiteCoordinate '' D))) :
    (n:ℝ)*Real.pi ≤ (P.area D).toReal+∑i,fuchsianPolygonAngle P D (x i) := by
  have ho:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hn:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  let v (i : Fin (n+1)):=P.halfPlaneCoordinate (x i)
  let S:=P.finiteCoordinate '' D
  have hoS : IsOpen S:=P.finiteCoordinate.isOpenMap D ho
  have hnS : S.Nonempty:=hn.image P.finiteCoordinate
  have haS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea S≠⊤:=by rwa [←P.area_apply D ho.measurableSet]
  have hmem (i : Fin (n+1)) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (v i))∈
      closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel '' S) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate (x i)))∈_
    rw [P.halfPlaneCoordinate_cayley]
    apply mem_closure_image _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.continuous.continuousAt
    rw [←P.finiteCoordinate.image_closure]
    exact mem_image_of_mem _ (hx i)
  have he : (n:ℝ)*Real.pi ≤ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea S).toReal+
      ∑i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure
        S) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (v i)):=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteHPointFan_area_angle_budget v horder hD.convex hoS hnS haS hmem hi
  have hang (i : Fin (n+1)) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure
    S) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (v i))=
      fuchsianPolygonAngle P D (x i) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure (P.finiteCoordinate '' D))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate (x i)))=_
    rw [P.halfPlaneCoordinate_cayley,←P.finiteCoordinate.image_closure]
    rfl
  simp_rw [hang] at he
  rwa [←P.area_apply D ho.measurableSet] at he

/-- Every actual finite polygon boundary angle is at most a straight angle. -/
theorem finite_polygon_boundary_angle_le_pi {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {x : P.domain.carrier} (hx : x∈frontier D) :
    fuchsianPolygonAngle P D x ≤ Real.pi := by
  rcases hD.boundary_geometric_angle x hx with ⟨q,N,hq,hN,h0,he,ha⟩ |
    ⟨u,v,N,hu,hv,hpos,hlt,hN,h0,he,ha⟩
  · exact ha.le
  · exact ha ▸ hlt.le

/-- Actual polygon cycles are unchanged on actual orbit mates. -/
theorem finite_polygon_cycle_eq_of_mem {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) {x y : P.domain.carrier}
    (hy : y∈fuchsianPolygonCycle P D x) :
    fuchsianPolygonCycle P D y=fuchsianPolygonCycle P D x := by
  unfold fuchsianPolygonCycle
  rw [(MulAction.orbit_eq_iff).mpr hy.2]

/-- Every point in the actual cycle of a boundary point is again on the actual boundary. -/
theorem finite_polygon_boundary_cycle_subset_frontier {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) {x : P.domain.carrier} (hx : x∈frontier D) :
    fuchsianPolygonCycle P D x⊆frontier D := by
  have ho:=((isFuchsianFundamentalDomain_iff P D).mp hD).1
  intro y hy
  rw [ho.frontier_eq]
  refine ⟨hy.1,?_⟩
  intro hyD
  have he:=finite_polygon_cycle_eq_of_mem P D hy
  have hxC : x∈fuchsianPolygonCycle P D y:=by
    rw [he]
    exact ⟨frontier_subset_closure hx,MulAction.mem_orbit_self x⟩
  rw [hD.interior_cycle_eq_singleton hyD] at hxC
  have hxy : x=y:=mem_singleton_iff.mp hxC
  exact (ho.frontier_eq ▸ hx).2 (hxy ▸ hyD)

/-- Every finite set of true boundary points of the original polygon has bounded total genuine corner deficit, provided its actual ideal boundary is nonempty. -/
theorem finite_polygon_corner_deficit_bound {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤)
    (p : 𝕔𝔻) (hp : p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' D))
    (X : Finset P.domain.carrier) (hX : ∀x∈X,x∈frontier D) :
    ∑x∈X,(Real.pi-fuchsianPolygonAngle P D x) ≤ (P.area D).toReal+Real.pi := by
  classical
  have ho:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hn:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  let S:=P.finiteCoordinate '' D
  have hoS : IsOpen S:=P.finiteCoordinate.isOpenMap D ho
  have hnS : S.Nonempty:=hn.image P.finiteCoordinate
  have haS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea S≠⊤:=by rwa [←P.area_apply D ho.measurableSet]
  have hang (x : P.domain.carrier) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure S)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate x))=fuchsianPolygonAngle P D x := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure (P.finiteCoordinate '' D))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate x))=_
    rw [P.halfPlaneCoordinate_cayley,←P.finiteCoordinate.image_closure]
    rfl
  let f : P.domain.carrier↪ℍ:=P.halfPlaneCoordinate.toEquiv.toEmbedding
  let Y:=X.map f
  have hY (z : ℍ) (hz : z∈Y) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈
      closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ''
        S) ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure S)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)≤Real.pi := by
    obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp hz
    constructor
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate x))∈_
      rw [P.halfPlaneCoordinate_cayley]
      apply mem_closure_image _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.continuous.continuousAt
      rw [←P.finiteCoordinate.image_closure]
      exact mem_image_of_mem _ (frontier_subset_closure (hX x hx))
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure S)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate x))≤_
      rw [hang]
      exact finite_polygon_boundary_angle_le_pi hD (hX x hx)
  have hb:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_corner_angle_deficit_bound_of_ideal hD.convex hoS hnS haS p hp Y hY
  rw [Finset.sum_map] at hb
  change (∑x∈X,(Real.pi-_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure S)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate x))))≤_ at hb
  simp_rw [hang] at hb
  rwa [←P.area_apply D ho.measurableSet] at hb

/-- Exact actual cycle angle sums give a uniform positive lower bound for the sum of its genuine corner deficits. -/
theorem finite_vertex_cycle_deficit_sum_lower {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier)
    (hx : IsFuchsianPolygonVertex P D x) :
    Real.pi/3 ≤ ∑y∈(hD.locallyFinite.cycle_finite x).toFinset,
      (Real.pi-fuchsianPolygonAngle P D y) := by
  have hb:=finite_vertex_cycle_angle_deficit_lower hD x hx
  rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
  have hc : fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x)=
      (hD.locallyFinite.cycle_finite x).toFinset.card:=Set.ncard_eq_toFinset_card _ _
  rwa [←hc]

/-- Different actual polygon cycles have no common point. -/
theorem finite_polygon_cycles_disjoint {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (x y : P.domain.carrier)
    (hne : fuchsianPolygonCycle P D x≠fuchsianPolygonCycle P D y) :
    Disjoint (fuchsianPolygonCycle P D x) (fuchsianPolygonCycle P D y) := by
  apply disjoint_left.mpr
  intro z hzX hzY
  exact hne ((finite_polygon_cycle_eq_of_mem P D hzX).symm.trans
    (finite_polygon_cycle_eq_of_mem P D hzY))

/-- Any finite family of distinct actual vertex cycles has cardinality controlled by the actual area, without finite-sidedness or a supplied ordering. -/
theorem finite_vertex_cycle_family_budget {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤)
    (p : 𝕔𝔻) (hp : p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' D))
    {ι : Type*} [Fintype ι] (x : ι→P.domain.carrier)
    (hx : ∀i,IsFuchsianPolygonVertex P D (x i))
    (hinj : Function.Injective (fun i=>fuchsianPolygonCycle P D (x i))) :
    (Fintype.card ι:ℝ)*(Real.pi/3) ≤ (P.area D).toReal+Real.pi := by
  classical
  let C (i : ι):=(hD.locallyFinite.cycle_finite (x i)).toFinset
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) C := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    exact disjoint_left.mp (finite_polygon_cycles_disjoint P D (x i) (x j)
      (fun he=>hij (hinj he))) ((Set.Finite.mem_toFinset _).mp hzi)
      ((Set.Finite.mem_toFinset _).mp hzj)
  let X:=Finset.univ.biUnion C
  have hX (z : P.domain.carrier) (hz : z∈X) : z∈frontier D := by
    obtain ⟨i,hi,hzi⟩:=Finset.mem_biUnion.mp hz
    exact finite_polygon_boundary_cycle_subset_frontier hD.locallyFinite.fundamental
      ((hx i).mem_frontier hD.locallyFinite.fundamental) ((Set.Finite.mem_toFinset _).mp hzi)
  have hb:=finite_polygon_corner_deficit_bound hD harea p hp X hX
  have he : (∑z∈X,(Real.pi-fuchsianPolygonAngle P D z))=
      ∑i,∑z∈C i,(Real.pi-fuchsianPolygonAngle P D z):=Finset.sum_biUnion hdis
  have hl : ∑i,(Real.pi/3) ≤ ∑i,∑z∈C i,(Real.pi-fuchsianPolygonAngle P D z):=
    Finset.sum_le_sum (fun i hi=>finite_vertex_cycle_deficit_sum_lower hD (x i) (hx i))
  rw [he] at hb
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hl.trans hb

/-- The set of literal cycles represented by true finite vertices is finite when an actual ideal endpoint is present and the actual area is finite. -/
theorem finite_area_vertex_cycles_finite_of_ideal {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤)
    (p : 𝕔𝔻) (hp : p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discIdealClosureTrace (P.finiteCoordinate ''
      D)) :
    {C : Set P.domain.carrier | ∃x,IsFuchsianPolygonVertex P D x ∧
      C=fuchsianPolygonCycle P D x}.Finite := by
  classical
  by_contra hn
  obtain ⟨n,hnR⟩:=exists_nat_gt (((P.area D).toReal+Real.pi)/(Real.pi/3))
  obtain ⟨F,hF,hcard⟩:=Set.Infinite.exists_subset_card_eq hn n
  have hrep (C : F) : ∃x,IsFuchsianPolygonVertex P D x ∧
      C.val=fuchsianPolygonCycle P D x:=hF C.property
  choose x hx he using hrep
  have hinj : Function.Injective (fun C : F=>fuchsianPolygonCycle P D (x C)) := by
    intro C E hCE
    apply Subtype.ext
    exact (he C).trans (hCE.trans (he E).symm)
  have hb:=finite_vertex_cycle_family_budget hD harea p hp x hx hinj
  have hc : Fintype.card F=n:=by simpa only [Fintype.card_coe] using hcard
  rw [hc] at hb
  have hπ : 0 < Real.pi/3:=by positivity
  have hgt : (P.area D).toReal+Real.pi<(n:ℝ)*(Real.pi/3):=(div_lt_iff₀ hπ).mp hnR
  exact (not_lt_of_ge hb) hgt

/-- Finitely many genuine finite cycles yield finitely many actual vertices; every original vertex belongs to its own actual cycle. -/
theorem finite_area_polygon_vertices_finite_of_ideal {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤)
    (p : 𝕔𝔻) (hp : p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discIdealClosureTrace (P.finiteCoordinate ''
      D)) :
    {x | IsFuchsianPolygonVertex P D x}.Finite := by
  have hC:=finite_area_vertex_cycles_finite_of_ideal hD harea p hp
  have hU : (⋃C∈{C : Set P.domain.carrier | ∃x,IsFuchsianPolygonVertex P D x ∧
      C=fuchsianPolygonCycle P D x},C).Finite := by
    apply hC.biUnion
    rintro C ⟨x,hx,rfl⟩
    exact hD.locallyFinite.cycle_finite x
  apply hU.subset
  intro x hx
  exact mem_iUnion₂.mpr ⟨fuchsianPolygonCycle P D x,⟨x,hx,rfl⟩,
    ⟨frontier_subset_closure (hx.mem_frontier hD.locallyFinite.fundamental),
      MulAction.mem_orbit_self x⟩⟩

/-- If the true compactified closure has no ideal point, the actual native closure is compact. -/
theorem native_closure_compact_of_idealTrace_empty (S : Set 𝔻)
    (hS : ¬(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discIdealClosureTrace S).Nonempty) : IsCompact (closure S) := by
  have hK : IsCompact (closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ''
    S)):=isClosed_closure.isCompact
  have hr : closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel '' S)⊆range _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel := by
    intro p hp
    have hne : ‖(p:ℂ)‖≠1:=by
      intro he
      exact hS ⟨p,hp,he⟩
    have hlt : ‖(p:ℂ)‖<1:=lt_of_le_of_ne p.norm_le_one hne
    refine ⟨Complex.UnitDisc.mk (p:ℂ) hlt,?_⟩
    exact Complex.UnitClosedDisc.coe_injective rfl
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.closure_eq_preimage_closure_image
    S]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.isInducing.isCompact_preimage' hK hr

/-- A genuine finite-area locally finite convex fundamental polygon has only finitely many actual finite vertices. The ideal-boundary and compact-closure cases are both proved. -/
theorem finite_area_polygon_vertices_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    {x | IsFuchsianPolygonVertex P D x}.Finite := by
  by_cases hi : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discIdealClosureTrace (P.finiteCoordinate ''
    D)).Nonempty
  · obtain ⟨p,hp⟩:=hi
    exact finite_area_polygon_vertices_finite_of_ideal hD harea p hp
  · have hc:=native_closure_compact_of_idealTrace_empty (P.finiteCoordinate '' D) hi
    rw [←P.finiteCoordinate.image_closure] at hc
    have hcD : IsCompact (closure D):=P.finiteCoordinate.isEmbedding.isCompact_iff.mpr hc
    apply (hD.locallyFinite.compact_vertices_finite (closure D) hcD).subset
    intro x hx
    exact ⟨hx,frontier_subset_closure (hx.mem_frontier hD.locallyFinite.fundamental)⟩

/-- The family of literal cycles represented by all true finite vertices is finite, without assuming an ideal endpoint or finite-sidedness. -/
theorem finite_area_polygon_vertex_cycles_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    {C : Set P.domain.carrier | ∃x,IsFuchsianPolygonVertex P D x ∧
      C=fuchsianPolygonCycle P D x}.Finite := by
  have hf:=(finite_area_polygon_vertices_finite hD harea).image (fuchsianPolygonCycle P D)
  convert hf using 1
  ext C
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,rfl⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨x,hx,he.symm⟩

end LowDimensionalTopology.Geometry.Fuchsian
