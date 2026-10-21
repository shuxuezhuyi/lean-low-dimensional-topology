module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSides
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Set Topology
open scoped Pointwise OnePoint Complex.UnitDisc
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

/-- The actual original-disc Fuchsian data as the previously established arbitrary-disc structure. -/
def UnitDiscFuchsianGroup.asFuchsianDisc {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : FuchsianDisc H where
  carrier := _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
  isDisc := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc
  invariant := P.invariant
  discontinuous := P.discontinuous

/-- The literal intersection of an original group orbit with the closed polygon. -/
def fuchsianPolygonCycle
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (x : P.domain.carrier) : Set P.domain.carrier :=
  closure D ∩ MulAction.orbit H x

/-- An actual cycle is an orbit intersection with the original closed polygon. -/
def IsFuchsianPolygonCycle
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D C : Set P.domain.carrier) : Prop := ∃ x, C = fuchsianPolygonCycle P D x

/-- Every original orbit has a representative in the closed fundamental domain. -/
theorem IsFuchsianFundamentalDomain.cycle_nonempty
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D)
    (x : P.domain.carrier) : (fuchsianPolygonCycle P D x).Nonempty := by
  have hc : (⋃ g : H, fuchsianDomainTile P D g) = univ := hD.closure_cover
  have hx : x ∈ ⋃ g : H, fuchsianDomainTile P D g := by rw [hc]; trivial
  obtain ⟨g, y, hy, hgy⟩ := mem_iUnion.mp hx
  change g • y = x at hgy
  refine ⟨y, hy, ?_⟩
  exact MulAction.mem_orbit_iff.mpr ⟨g⁻¹, by rw [← hgy, inv_smul_smul]⟩

/-- Local finiteness proves the original orbit intersection finite; no compactness of the polygon is assumed. -/
theorem IsLocallyFiniteFuchsianDomain.cycle_finite
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D)
    (x : P.domain.carrier) : (fuchsianPolygonCycle P D x).Finite := by
  apply ((hD.incident_finite x).image (fun g : H => g⁻¹ • x)).subset
  rintro y ⟨hy, hg⟩
  obtain ⟨g, hgy⟩ := MulAction.mem_orbit_iff.mp hg
  have hi : x ∈ fuchsianDomainTile P D g⁻¹ := by
    refine ⟨y, hy, ?_⟩
    change g⁻¹ • y = x
    rw [← hgy, inv_smul_smul]
  exact ⟨g⁻¹, hi, by simpa only [inv_inv] using hgy⟩

/-- The literal finite-cycle length. -/
def fuchsianPolygonCycleLength
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (C : Set P.domain.carrier) : ℕ := C.ncard

/-- The original stabilizer order at a genuine interior-disc point. -/
def fuchsianPointOrder
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (x : P.domain.carrier) : ℕ := Nat.card (MulAction.stabilizer H x)

/-- The internal point stabilizer is exactly the previously defined original Mobius stabilizer. -/
def UnitDiscFuchsianGroup.stabilizerEquivBoundary
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) :
    MulAction.stabilizer H x ≃* _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H x.val where
  toFun f := ⟨f.val.val, (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H x.val f.val.val).mpr
    ⟨f.val.property, congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp f.property)⟩⟩
  invFun f := by
    obtain ⟨hfH, hfix⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H x.val f.val).mp f.property
    exact ⟨⟨f.val, hfH⟩, MulAction.mem_stabilizer_iff.mpr (Subtype.ext hfix)⟩
  left_inv f := rfl
  right_inv f := rfl
  map_mul' f g := rfl

/-- Every actual finite-disc point has a finite stabilizer for the original group action. -/
theorem UnitDiscFuchsianGroup.stabilizer_finite
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) : Finite (MulAction.stabilizer H x) := by
  let : ProperlyDiscontinuousSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_properlyDiscontinuous P.domain P.discontinuous
  let : Fintype (MulAction.stabilizer H x) := (ProperlyDiscontinuousSMul.finite_stabilizer (Γ := H) x).fintype
  infer_instance

/-- Every actual point stabilizer in the polygon is cyclic, including the trivial stabilizer. -/
theorem UnitDiscFuchsianGroup.stabilizer_isCyclic
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) : IsCyclic (MulAction.stabilizer H x) := by
  let : IsCyclic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H x.val) := P.asFuchsianDisc.stabilizer_isCyclic x.val
  exact isCyclic_of_injective (P.stabilizerEquivBoundary x).toMonoidHom (P.stabilizerEquivBoundary x).injective

/-- Stabilizers of actual orbit mates are conjugate via the original group element. -/
def fuchsianCycleStabilizerEquiv
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {x y : P.domain.carrier} (hy : y ∈ MulAction.orbit H x) :
    MulAction.stabilizer H x ≃* MulAction.stabilizer H y :=
  MulAction.stabilizerEquivStabilizer (MulAction.mem_orbit_iff.mp hy).choose_spec.symm

/-- The finite stabilizer order is constant on each original cycle. -/
theorem fuchsianPointOrder_eq_of_mem_cycle
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (x y : P.domain.carrier)
    (hy : y ∈ fuchsianPolygonCycle P D x) : fuchsianPointOrder P y = fuchsianPointOrder P x :=
  (Nat.card_congr (fuchsianCycleStabilizerEquiv hy.2).toEquiv).symm

/-- Every genuine finite polygon cycle has positive finite length. -/
theorem IsLocallyFiniteFuchsianDomain.cycleLength_pos
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D)
    (x : P.domain.carrier) : 0 < fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) :=
  (Set.ncard_pos (hD.cycle_finite x)).mpr (hD.fundamental.cycle_nonempty x)

/-- The actual finite point-stabilizer order is positive. -/
theorem UnitDiscFuchsianGroup.pointOrder_pos
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) : 0 < fuchsianPointOrder P x := by
  let : Finite (MulAction.stabilizer H x) := P.stabilizer_finite x
  exact Nat.card_pos

/-- The common actual stabilizer order of a genuine orbit-intersection cycle. -/
def fuchsianPolygonCycleOrder
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D C : Set P.domain.carrier) (hC : IsFuchsianPolygonCycle P D C) : ℕ :=
  fuchsianPointOrder P hC.choose

/-- The cycle order equals the actual stabilizer order of every point of the cycle. -/
theorem fuchsianPolygonCycleOrder_eq_pointOrder
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D C : Set P.domain.carrier) (hC : IsFuchsianPolygonCycle P D C)
    {y : P.domain.carrier} (hy : y ∈ C) : fuchsianPolygonCycleOrder P D C hC = fuchsianPointOrder P y := by
  change fuchsianPointOrder P hC.choose = _
  symm
  apply fuchsianPointOrder_eq_of_mem_cycle P D hC.choose y
  rw [← hC.choose_spec]
  exact hy

end LowDimensionalTopology.Geometry.Fuchsian
