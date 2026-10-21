/- actual Nielsen area and its equality case. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSignature
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology MeasureTheory
open scoped OnePoint Complex.UnitDisc
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

/-- A genuine finite-generation Nielsen polygon has positive actual area. -/
theorem finitelyGenerated_nielsenCoreArea_pos
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    {D:Set P.domain.carrier} (hD:IsFuchsianFundamentalDomain P D) :
    0<fuchsianNielsenCoreArea P hNE D := by
  obtain ⟨w,hw,hwN⟩:=exists_dirichlet_center_in_nielsenCore P hNE
  let hE:=dirichletDomain_isConvexFuchsianPolygon P w hw
  let hfin:=finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  let hwD:=dirichletDomain_center_mem P w hw
  obtain ⟨J,hc,hv⟩:=nielsenCore_actual_marked_cyclic_boundary hE hNE hFG hfin w hwD hwN
  rw [fuchsianNielsenCoreArea_independent P hNE hD hE.locallyFinite.fundamental,
    ←nielsenCyclicDiscPolygon_area hE hNE hFG hfin w hwD hwN J hc hv]
  exact Polygon.DiscPolygon.area_pos _

/-- Ordering the actual elliptic classes does not change an actual signature. -/
theorem HasNielsenFuchsianSignature.perm_orders
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {hNE:DiscreteGroups.IsNonElementary H} {hFG:H.FG}
    {g:ℕ} {orders orders':List ℕ} {cusps boundaryEnds:ℕ}
    (h:HasNielsenFuchsianSignature P hNE hFG g orders cusps boundaryEnds)
    (hperm:orders.Perm orders') :
    HasNielsenFuchsianSignature P hNE hFG g orders' cusps boundaryEnds := by
  obtain ⟨w,hw,hwN,J,hc,hv,n,S,hr,hg,ho,hp,ht⟩:=h
  exact ⟨w,hw,hwN,J,hc,hv,n,S,hr,hg,hperm.symm.trans ho,hp,ht⟩

/-- No actual boundary end forces the genuine Nielsen region to fill the disc. -/
theorem HasNielsenFuchsianSignature.core_eq_univ_of_boundaryEnds_eq_zero
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {hNE:DiscreteGroups.IsNonElementary H} {hFG:H.FG}
    {g:ℕ} {orders:List ℕ} {cusps boundaryEnds:ℕ}
    (h:HasNielsenFuchsianSignature P hNE hFG g orders cusps boundaryEnds)
    (hz:boundaryEnds=0) : fuchsianNielsenCore P hNE=univ := by
  obtain ⟨_w,_hw,_hwN,_J,_hc,_hv,_n,_S,_hr,_hg,_ho,_hp,ht⟩:=h
  let:Finite (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc):=
    finitelyGenerated_boundary_cyclic_classes_finite P hFG
  have hzero:Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc)=0:=
    ht.symm.trans hz
  have hfront:frontier (fuchsianNielsenCore P hNE)=∅:=by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hi:P.finiteCoordinate x∈P.finiteCoordinate '' frontier (fuchsianNielsenCore P hNE):=
      mem_image_of_mem _ hx
    rw [nielsenBoundaryDiscLineFamily_frontier_cover] at hi
    obtain ⟨L,hLx⟩:=mem_iUnion.mp hi
    obtain ⟨hL,_hxL⟩:=mem_iUnion.mp hLx
    have hpos:0<Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc):=
      Nat.card_pos_iff.mpr ⟨⟨nielsenBoundaryLineCyclicClass P hNE hFG L hL⟩,inferInstance⟩
    omega
  exact (isClopen_iff_frontier_eq_empty.mpr hfront).eq_univ
    (fuchsianNielsenCore_isConnected P hNE).nonempty

/-- The exact actual Nielsen area has the sharp numerical signature bound. -/
theorem HasNielsenFuchsianSignature.area_sharp
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {hNE:DiscreteGroups.IsNonElementary H} {hFG:H.FG}
    {g:ℕ} {orders:List ℕ} {cusps boundaryEnds:ℕ}
    (h:HasNielsenFuchsianSignature P hNE hFG g orders cusps boundaryEnds)
    {D:Set P.domain.carrier} (hD:IsFuchsianFundamentalDomain P D) :
    Real.pi/21≤(fuchsianNielsenCoreArea P hNE D).toReal ∧
      ((fuchsianNielsenCoreArea P hNE D).toReal=Real.pi/21 ↔
        g=0 ∧ cusps=0 ∧ boundaryEnds=0 ∧ orders.Perm [2,3,7]) := by
  let s:FuchsianSignature:=⟨g,orders,h.orders_two_le,cusps,boundaryEnds⟩
  have hA:(fuchsianNielsenCoreArea P hNE D).toReal=s.areaFormulaValue:=by
    rw [h.area hD]
    dsimp only [Fuchsian.FuchsianSignature.areaFormulaValue,Fuchsian.FuchsianSignature.deficit,s]
    ring
  have hpos:0<s.deficit:=by
    have hp:=ENNReal.toReal_pos (ne_of_gt (finitelyGenerated_nielsenCoreArea_pos P hNE hFG hD))
      (finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD)
    rw [hA,Fuchsian.FuchsianSignature.areaFormulaValue] at hp
    exact (mul_pos_iff_of_pos_left (show 0<2*Real.pi by positivity)).mp hp
  simpa only [←hA,s] using s.areaFormulaValue_sharp hpos

/-- The actual Nielsen quotient bound holds without a finite-generation hypothesis. -/
theorem nielsenCoreArea_pi_div_21_le {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H)
    {D:Set P.domain.carrier} (hD:IsFuchsianFundamentalDomain P D) :
    ENNReal.ofReal (Real.pi/21)≤fuchsianNielsenCoreArea P hNE D := by
  by_cases ha:fuchsianNielsenCoreArea P hNE D=⊤
  · rw [ha]
    exact le_top
  have hFG:=finite_nielsenCoreArea_finitelyGenerated P hNE hD ha
  obtain ⟨g,orders,cusps,boundaryEnds,h⟩:=finitelyGenerated_hasNielsenFuchsianSignature P hNE hFG
  exact (ENNReal.ofReal_le_iff_le_toReal ha).mpr (h.area_sharp hD).1

/-- Equality characterizes the actual whole-group signature, including all genuine ends. -/
theorem nielsenCoreArea_eq_pi_div_21_iff {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H)
    {D:Set P.domain.carrier} (hD:IsFuchsianFundamentalDomain P D) :
    fuchsianNielsenCoreArea P hNE D=ENNReal.ofReal (Real.pi/21) ↔
      ∃hFG:H.FG,HasNielsenFuchsianSignature P hNE hFG 0 [2,3,7] 0 0 := by
  constructor
  · intro he
    have ha:fuchsianNielsenCoreArea P hNE D≠⊤:=by
      rw [he]
      exact ENNReal.ofReal_ne_top
    have hFG:=finite_nielsenCoreArea_finitelyGenerated P hNE hD ha
    obtain ⟨g,orders,cusps,boundaryEnds,h⟩:=finitelyGenerated_hasNielsenFuchsianSignature P hNE hFG
    have hreal:(fuchsianNielsenCoreArea P hNE D).toReal=Real.pi/21:=by
      rw [he,ENNReal.toReal_ofReal (by positivity)]
    obtain ⟨rfl,rfl,rfl,hperm⟩:=(h.area_sharp hD).2.mp hreal
    exact ⟨hFG,h.perm_orders hperm⟩
  · rintro ⟨hFG,h⟩
    rw [h.area_ennreal hD]
    congr 1
    norm_num
    ring

/-- At the minimum, the genuine Nielsen region is the original full invariant disc. -/
theorem nielsenCore_eq_univ_of_area_eq_pi_div_21
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H)
    {D:Set P.domain.carrier} (hD:IsFuchsianFundamentalDomain P D)
    (he:fuchsianNielsenCoreArea P hNE D=ENNReal.ofReal (Real.pi/21)) :
    fuchsianNielsenCore P hNE=univ := by
  obtain ⟨hFG,h⟩:=(nielsenCoreArea_eq_pi_div_21_iff P hNE hD).mp he
  exact h.core_eq_univ_of_boundaryEnds_eq_zero rfl

/-- The equality conclusion as a literal equality of the original geometric subsets. -/
theorem nielsenRegion_eq_disc_of_area_eq_pi_div_21
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H)
    {D:Set P.domain.carrier} (hD:IsFuchsianFundamentalDomain P D)
    (he:fuchsianNielsenCoreArea P hNE D=ENNReal.ofReal (Real.pi/21)) :
    P.asFuchsianDisc.nielsenRegion hNE=P.domain.carrier := by
  have hcore:=nielsenCore_eq_univ_of_area_eq_pi_div_21 P hNE hD he
  apply subset_antisymm
  · exact (P.asFuchsianDisc.nielsenRegion_properties hNE).1
  · intro z hz
    have hmem:(⟨z,hz⟩:P.domain.carrier)∈fuchsianNielsenCore P hNE:=by
      rw [hcore]
      exact mem_univ _
    exact hmem

/-- The sharp Nielsen-core area bound, including infinite actual Nielsen area and the full equality case. -/
theorem nielsenCoreArea_ge_pi_div_twentyOne_eq_iff_signature_two_three_seven_and_full_region
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H)
    {D:Set P.domain.carrier} (hD:IsFuchsianFundamentalDomain P D) :
    ENNReal.ofReal (Real.pi/21)≤fuchsianNielsenCoreArea P hNE D ∧
      (fuchsianNielsenCoreArea P hNE D=ENNReal.ofReal (Real.pi/21) ↔
        ∃hFG:H.FG,HasNielsenFuchsianSignature P hNE hFG 0 [2,3,7] 0 0) ∧
      (fuchsianNielsenCoreArea P hNE D=ENNReal.ofReal (Real.pi/21) →
        P.asFuchsianDisc.nielsenRegion hNE=P.domain.carrier) :=
  ⟨nielsenCoreArea_pi_div_21_le P hNE hD,nielsenCoreArea_eq_pi_div_21_iff P hNE hD,
    nielsenRegion_eq_disc_of_area_eq_pi_div_21 P hNE hD⟩

end LowDimensionalTopology.Geometry.Fuchsian
