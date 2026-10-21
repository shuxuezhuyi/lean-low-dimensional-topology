module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonLocalGeometry
public import Mathlib.Tactic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology
open scoped Complex.UnitDisc Pointwise OnePoint ENNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The source's accidental condition excludes actual nonidentity elliptic stabilizers. -/
def IsAccidentalFuchsianPoint {H : Subgroup Mobius.complexMobiusGroup}
    (_P : UnitDiscFuchsianGroup H) (x : _P.domain.carrier) : Prop :=
  ¬ ∃ g : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val ∧ g • x = x

theorem UnitDiscFuchsianGroup.fixing_nonidentity_elliptic
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) (g : H)
    (hg : g • x = x) (hne : g ≠ 1) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val := by
  let : Finite (MulAction.stabilizer H x) := P.stabilizer_finite x
  let t : MulAction.stabilizer H x := ⟨g,hg⟩
  obtain ⟨n,hn,he⟩ := (isOfFinOrder_of_finite t).exists_pow_eq_one
  have hfin : IsOfFinOrder g.val := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n,hn,congrArg (fun a : MulAction.stabilizer H x => a.val.val) he⟩
  apply _root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic _ ?_ hfin
  intro heq
  apply hne
  exact Subtype.ext heq

theorem isAccidentalFuchsianPoint_iff_no_stabilizer
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) :
    IsAccidentalFuchsianPoint P x ↔ ∀ g : H, g • x = x → g = 1 := by
  constructor
  · intro h g hg
    by_contra hne
    exact h ⟨g,P.fixing_nonidentity_elliptic x g hg hne,hg⟩
  · intro h
    rintro ⟨g,hg,hgx⟩
    exact hg.1 (congrArg Subtype.val (h g hgx))

theorem isAccidentalFuchsianPoint_iff_pointOrder_one
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) :
    IsAccidentalFuchsianPoint P x ↔ fuchsianPointOrder P x = 1 := by
  rw [isAccidentalFuchsianPoint_iff_no_stabilizer]
  constructor
  · intro h
    let : Subsingleton (MulAction.stabilizer H x) := ⟨by
      intro a b
      apply Subtype.ext
      exact (h a.val a.property).trans (h b.val b.property).symm⟩
    exact Nat.card_unique
  · intro h
    let : Subsingleton (MulAction.stabilizer H x) := (Nat.card_eq_one_iff_unique.mp h).1
    intro g hg
    exact congrArg (fun a : MulAction.stabilizer H x => a.val)
      (Subsingleton.elim (⟨g,hg⟩ : MulAction.stabilizer H x) 1)

theorem isAccidentalFuchsianPoint_cycle_invariant
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (x y : P.domain.carrier)
    (hy : y ∈ fuchsianPolygonCycle P D x) :
    IsAccidentalFuchsianPoint P y ↔ IsAccidentalFuchsianPoint P x := by
  rw [isAccidentalFuchsianPoint_iff_pointOrder_one,isAccidentalFuchsianPoint_iff_pointOrder_one,
    fuchsianPointOrder_eq_of_mem_cycle P D x y hy]

theorem IsLocallyFiniteFuchsianDomain.incident_card_eq_order_mul_cycleLength
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (x : P.domain.carrier) :
    (hD.incident_finite x).toFinset.card =
      fuchsianPointOrder P x * fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) := by
  have he := hD.incident_weight_sum x (fun _ => 1)
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at he
  have hn : fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) =
      (hD.cycle_finite x).toFinset.card := Set.ncard_eq_toFinset_card _ _
  rw [hn]
  exact_mod_cast he

/-- A genuine accidental vertex has at least three points in its actual polygon cycle. -/
theorem IsConvexFuchsianPolygon.accidental_vertex_cycle_length_ge_three
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier)
    (hx : IsFuchsianPolygonVertex P D x) (ha : IsAccidentalFuchsianPoint P x) :
    3 ≤ fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) := by
  classical
  obtain ⟨g,h,hg,hh,hgh,he⟩ := hx
  have hmem : x ∈ closure D ∩ fuchsianDomainTile P D g ∩ fuchsianDomainTile P D h :=
    he.symm ▸ mem_singleton x
  let s := (hD.locallyFinite.incident_finite x).toFinset
  have h1 : (1 : H) ∈ s := by
    apply (Set.Finite.mem_toFinset _).mpr
    change x ∈ (1 : H) • closure D
    simpa only [one_smul] using hmem.1.1
  have hgS : g ∈ s := (Set.Finite.mem_toFinset _).mpr hmem.1.2
  have hhS : h ∈ s := (Set.Finite.mem_toFinset _).mpr hmem.2
  have hsub : ({1,g,h} : Finset H) ⊆ s := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  have hthree : 3 ≤ s.card := by simpa [hg,hh,hgh,Ne.symm hg,Ne.symm hh] using hc
  have hec := hD.locallyFinite.incident_card_eq_order_mul_cycleLength x
  rw [(isAccidentalFuchsianPoint_iff_pointOrder_one P x).mp ha,one_mul] at hec
  exact hec ▸ hthree

end LowDimensionalTopology.Geometry.Fuchsian
