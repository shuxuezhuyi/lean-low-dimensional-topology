module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.FiniteNielsenCoreGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaVertexCycles
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped Topology OnePoint Complex.UnitDisc UpperHalfPlane
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
local instance coreVertexSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance coreVertexSphereBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- The genuine angular Haar measure is monotone under inclusion of the
actual native region. -/
theorem discSubtendedAngle_mono {S T : Set 𝔻} (hST : S⊆T) (z : 𝔻) :
    Hyperbolic.discSubtendedAngle S z≤Hyperbolic.discSubtendedAngle T z := by
  unfold Hyperbolic.discSubtendedAngle Hyperbolic.discSubtendedAngularFraction
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Hyperbolic.discRadialDirections_mono (image_mono hST)))

/-- Whole original finite polygon cycles remain in the source Nielsen core
as soon as one representative lies there. -/
theorem nielsenCore_cycle_subset
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (D : Set P.domain.carrier)
    (x : P.domain.carrier)
    (hx : x∈fuchsianNielsenCore P hNE) :
    fuchsianPolygonCycle P D x⊆fuchsianNielsenCore P hNE := by
  rintro y ⟨_hy,hyO⟩
  obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hyO
  exact fuchsianNielsenCore_invariant P hNE g x hx

/-- Finite genuine Nielsen area controls the corner deficits of any finite
collection of original polygon boundary points that lie inside the core.
No full-polygon finite-area hypothesis is used. -/
theorem nielsenCore_finite_corner_deficit_bound
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE)
    (p : 𝕔𝔻) (hp : p∈Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)))
    (X : Finset P.domain.carrier)
    (hX : ∀x∈X,x∈frontier D ∧ x∈fuchsianNielsenCore P hNE) :
    ∑x∈X,(Real.pi-fuchsianPolygonAngle P D x)≤
      (fuchsianNielsenCoreArea P hNE D).toReal+Real.pi := by
  classical
  let Q := D∩fuchsianNielsenCore P hNE
  let S := P.finiteCoordinate '' Q
  have hoQ : IsOpen Q := hD.locallyFinite.fundamental.isOpen.inter (fuchsianNielsenCore_isOpen P hNE)
  have hoS : IsOpen S := P.finiteCoordinate.isOpenMap Q hoQ
  have hnS : S.Nonempty := ⟨P.finiteCoordinate w,mem_image_of_mem _ ⟨hwD,hwN⟩⟩
  have haS : Hyperbolic.discHyperbolicArea S≠⊤ := by rwa [←P.area_apply Q hoQ.measurableSet]
  have hm (x : P.domain.carrier) :
      Hyperbolic.discSubtendedAngle (closure S) (P.finiteCoordinate x)≤fuchsianPolygonAngle P D x := by
    change Hyperbolic.discSubtendedAngle (closure S) _≤
      Hyperbolic.discSubtendedAngle (P.finiteCoordinate '' closure D) _
    rw [P.finiteCoordinate.image_closure]
    exact discSubtendedAngle_mono (closure_mono (image_mono inter_subset_left)) _
  let Y := X.map P.halfPlaneCoordinate.toEquiv.toEmbedding
  have hY (z : ℍ) (hz : z∈Y) :
      Hyperbolic.discToClosedModel (Hyperbolic.halfPlaneToDisc z)∈closure (Hyperbolic.discToClosedModel '' S) ∧
      Hyperbolic.discSubtendedAngle (closure S) (Hyperbolic.halfPlaneToDisc z)≤Real.pi := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hz
    change Hyperbolic.discToClosedModel (Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate
      x))∈closure (Hyperbolic.discToClosedModel '' S) ∧
      Hyperbolic.discSubtendedAngle (closure S) (Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate x))≤Real.pi
    rw [P.halfPlaneCoordinate_cayley]
    constructor
    · apply mem_closure_image Hyperbolic.isEmbedding_discToClosedModel.continuous.continuousAt
      rw [←P.finiteCoordinate.image_closure]
      apply mem_image_of_mem
      exact (fuchsianNielsenCore_isOpen P hNE).closure_inter
        ⟨frontier_subset_closure (hX x hx).1,(hX x hx).2⟩
    · exact (hm x).trans (finite_polygon_boundary_angle_le_pi hD (hX x hx).1)
  have hb := Hyperbolic.finite_corner_angle_deficit_bound_of_ideal (nielsenCore_inter_native_convex hD hNE)
    hoS hnS haS p hp Y hY
  rw [Finset.sum_map] at hb
  change (∑x∈X,(Real.pi-Hyperbolic.discSubtendedAngle (closure S)
    (Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate x))))≤_ at hb
  simp_rw [P.halfPlaneCoordinate_cayley] at hb
  have hl : (∑x∈X,(Real.pi-fuchsianPolygonAngle P D x))≤
      ∑x∈X,(Real.pi-Hyperbolic.discSubtendedAngle (closure S) (P.finiteCoordinate x)) := by
    apply Finset.sum_le_sum
    intro x _hx
    exact sub_le_sub_left (hm x) _
  have hb' := hl.trans hb
  rwa [←P.area_apply Q hoQ.measurableSet] at hb'

/-- Any finite family of distinct actual original vertex cycles inside the
Nielsen core has its cardinality controlled by genuine core area. -/
theorem nielsenCore_vertex_cycle_family_budget
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE)
    (p : 𝕔𝔻) (hp : p∈Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)))
    {ι : Type*} [Fintype ι] (x : ι→P.domain.carrier)
    (hx : ∀i,IsFuchsianPolygonVertex P D (x i))
    (hxN : ∀i,x i∈fuchsianNielsenCore P hNE)
    (hinj : Function.Injective (fun i=>fuchsianPolygonCycle P D (x i))) :
    (Fintype.card ι:ℝ)*(Real.pi/3)≤(fuchsianNielsenCoreArea P hNE D).toReal+Real.pi := by
  classical
  let C (i : ι) := (hD.locallyFinite.cycle_finite (x i)).toFinset
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) C := by
    intro i _hi j _hj hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    exact disjoint_left.mp (finite_polygon_cycles_disjoint P D (x i) (x j)
      (fun he=>hij (hinj he))) ((Set.Finite.mem_toFinset _).mp hzi)
      ((Set.Finite.mem_toFinset _).mp hzj)
  let X := Finset.univ.biUnion C
  have hX (z : P.domain.carrier) (hz : z∈X) : z∈frontier D ∧ z∈fuchsianNielsenCore P hNE := by
    obtain ⟨i,_hi,hzi⟩ := Finset.mem_biUnion.mp hz
    have hzC := (Set.Finite.mem_toFinset _).mp hzi
    exact ⟨finite_polygon_boundary_cycle_subset_frontier hD.locallyFinite.fundamental
      ((hx i).mem_frontier hD.locallyFinite.fundamental) hzC,
      nielsenCore_cycle_subset P hNE D (x i) (hxN i) hzC⟩
  have hb := nielsenCore_finite_corner_deficit_bound hD hNE harea w hwD hwN p hp X hX
  have he : (∑z∈X,(Real.pi-fuchsianPolygonAngle P D z))=
      ∑i,∑z∈C i,(Real.pi-fuchsianPolygonAngle P D z) := Finset.sum_biUnion hdis
  have hl : ∑i,(Real.pi/3)≤∑i,∑z∈C i,(Real.pi-fuchsianPolygonAngle P D z) :=
    Finset.sum_le_sum (fun i _hi=>finite_vertex_cycle_deficit_sum_lower hD (x i) (hx i))
  rw [he] at hb
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hl.trans hb

/-- A genuine ideal core-closure point and finite core area force only
finitely many actual original vertex cycles lying in that core. -/
theorem finite_nielsenCore_vertex_cycles_of_ideal
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE)
    (p : 𝕔𝔻) (hp : p∈Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))) :
    {C : Set P.domain.carrier | ∃x,IsFuchsianPolygonVertex P D x ∧
      x∈fuchsianNielsenCore P hNE ∧ C=fuchsianPolygonCycle P D x}.Finite := by
  classical
  by_contra hn
  obtain ⟨n,hnR⟩ := exists_nat_gt (((fuchsianNielsenCoreArea P hNE D).toReal+Real.pi)/(Real.pi/3))
  obtain ⟨F,hF,hcard⟩ := Set.Infinite.exists_subset_card_eq hn n
  have hrep (C : F) : ∃x,IsFuchsianPolygonVertex P D x ∧
      x∈fuchsianNielsenCore P hNE ∧ C.val=fuchsianPolygonCycle P D x := hF C.property
  choose x hx hxN he using hrep
  have hinj : Function.Injective (fun C : F=>fuchsianPolygonCycle P D (x C)) := by
    intro C E hCE
    apply Subtype.ext
    exact (he C).trans (hCE.trans (he E).symm)
  have hb := nielsenCore_vertex_cycle_family_budget hD hNE harea w hwD hwN p hp x hx hxN hinj
  have hc : Fintype.card F=n := by simpa only [Fintype.card_coe] using hcard
  rw [hc] at hb
  have hπ : 0<Real.pi/3 := by positivity
  exact (not_lt_of_ge hb) ((div_lt_iff₀ hπ).mp hnR)

/-- Finite actual Nielsen-core area forces finitely many genuine original
finite vertices in that core, whether or not the core part has ideal points. -/
theorem finite_nielsenCore_vertices
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE) :
    {x | IsFuchsianPolygonVertex P D x ∧ x∈fuchsianNielsenCore P hNE}.Finite := by
  by_cases hi : (Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))).Nonempty
  · obtain ⟨p,hp⟩ := hi
    have hC := finite_nielsenCore_vertex_cycles_of_ideal hD hNE harea w hwD hwN p hp
    have hU : (⋃C∈{C : Set P.domain.carrier | ∃x,IsFuchsianPolygonVertex P D x ∧
        x∈fuchsianNielsenCore P hNE ∧ C=fuchsianPolygonCycle P D x},C).Finite := by
      apply hC.biUnion
      rintro C ⟨x,_hx,_hxN,rfl⟩
      exact hD.locallyFinite.cycle_finite x
    apply hU.subset
    rintro x ⟨hx,hxN⟩
    exact mem_iUnion₂.mpr ⟨fuchsianPolygonCycle P D x,⟨x,hx,hxN,rfl⟩,
      ⟨frontier_subset_closure (hx.mem_frontier hD.locallyFinite.fundamental),MulAction.mem_orbit_self x⟩⟩
  · have hc := native_closure_compact_of_idealTrace_empty
      (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)) hi
    rw [←P.finiteCoordinate.image_closure] at hc
    have hcQ := P.finiteCoordinate.isEmbedding.isCompact_iff.mpr hc
    apply (hD.locallyFinite.compact_vertices_finite _ hcQ).subset
    rintro x ⟨hx,hxN⟩
    exact ⟨hx,(fuchsianNielsenCore_isOpen P hNE).closure_inter
      ⟨frontier_subset_closure (hx.mem_frontier hD.locallyFinite.fundamental),hxN⟩⟩

/-- The whole family of actual original vertex cycles represented inside the
Nielsen core is finite, without a full-polygon finite-area assumption. -/
theorem finite_nielsenCore_vertex_cycles
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE) :
    {C : Set P.domain.carrier | ∃x,IsFuchsianPolygonVertex P D x ∧
      x∈fuchsianNielsenCore P hNE ∧ C=fuchsianPolygonCycle P D x}.Finite := by
  have hf := (finite_nielsenCore_vertices hD hNE harea w hwD hwN).image (fuchsianPolygonCycle P D)
  convert hf using 1
  ext C
  constructor
  · rintro ⟨x,hx,hxN,rfl⟩
    exact ⟨x,⟨hx,hxN⟩,rfl⟩
  · rintro ⟨x,⟨hx,hxN⟩,rfl⟩
    exact ⟨x,hx,hxN,rfl⟩

/-- Only finitely many genuine original sides contain an original vertex
inside the source Nielsen core. This does not assert that all sides meeting
the core have such a vertex. -/
theorem finite_nielsenCore_vertex_incident_sides
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧
      ∃x∈S,IsFuchsianPolygonVertex P D x ∧ x∈fuchsianNielsenCore P hNE}.Finite := by
  have hV := finite_nielsenCore_vertices hD hNE harea w hwD hwN
  have hU : (⋃x∈{x | IsFuchsianPolygonVertex P D x ∧ x∈fuchsianNielsenCore P hNE},
      {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧ x∈S}).Finite := by
    apply hV.biUnion
    intro x _hx
    apply (hD.locallyFinite.compact_sides_finite {x} isCompact_singleton).subset
    rintro S ⟨hS,hxS⟩
    exact ⟨hS,x,hxS,mem_singleton x⟩
  apply hU.subset
  rintro S ⟨hS,x,hxS,hx,hxN⟩
  exact mem_iUnion₂.mpr ⟨x,⟨hx,hxN⟩,hS,hxS⟩

end LowDimensionalTopology.Geometry.Fuchsian
