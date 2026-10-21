/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureConeClosure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane Pointwise OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
  (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
  (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "H₀" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "G₀" => generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb
local notation "P₀" => generalCoreTargetMobiusData g orders s t ho hdef d hd hb
local notation "K₀" => _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius G₀
local notation "f₀" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "D₀" => _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.asFuchsianDisc (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.cayleyData P₀)
local notation "E₀" => generalCoreTargetCayleyEquiv g orders s t ho hdef d hd hb
local notation "c₀" => generalCoreConePoint g orders s t ho hdef d hd hb

/-- The actual original target elliptic point of each original occurrence. -/
def generalCoreEllipticPoint (j : Fin orders.length) : fuchsianCyclicFixedPoints D₀ .elliptic :=
  ⟨(f₀ (c₀ j)).val, generalCoreConePoint_elliptic g orders s t ho hdef d hd hb j⟩

/-- Every elliptic center of the entire actual target lies in the orbit of
an original occurrence. This exhausts all group elements and all centers. -/
theorem generalCoreEllipticPoint_orbit (ht : 0 < t)
    (p : fuchsianCyclicFixedPoints D₀ .elliptic) :
    ∃ (j : Fin orders.length) (b : K₀), b • p = generalCoreEllipticPoint g orders s t ho hdef d hd hb j := by
  let z : (P₀).cayleyData.domain.carrier := ⟨p.val, p.property.1 rfl⟩
  let x := (f₀).symm z
  have hfx : f₀ x = z := (f₀).apply_symm_apply z
  have hpx : (f₀ x).val = p.val := congrArg Subtype.val hfx
  obtain ⟨q, hqK, hqE, hqfix⟩ := p.property.2
  let qK : K₀ := ⟨q, hqK⟩
  let a : H₀ := (E₀).symm qK
  have hEa : E₀ a = qK := (E₀).apply_symm_apply qK
  have han : a ≠ 1 := by
    intro he
    apply hqE.1
    have hm := congrArg E₀ he
    rw [hEa, map_one] at hm
    exact congrArg Subtype.val hm
  have hax : a.val x = x := by
    apply (f₀).injective
    rw [generalCoreTargetCayleyEquiv_action, hEa]
    apply Subtype.ext
    change q.val (f₀ x).val = (f₀ x).val
    rw [hpx]
    exact hqfix
  obtain ⟨j, b, hbj⟩ := generalCoreTarget_fixed_cone_orbit g orders s t ho hdef d hd hb
    (generalCoreTargetMobius_nonElementary g orders s t ho hdef d hd hb ht) x a han hax
  refine ⟨j, E₀ b, Subtype.ext ?_⟩
  have hAct := congrArg Subtype.val
    (generalCoreTargetCayleyEquiv_action g orders s t ho hdef d hd hb b x)
  rw [hbj] at hAct
  change (E₀ b).val.val p.val = (f₀ (c₀ j)).val
  change (f₀ (c₀ j)).val = (E₀ b).val.val (f₀ x).val at hAct
  rw [hpx] at hAct
  exact hAct.symm

/-- Whole original projective group orbits preserve every original cone
occurrence label, including repeated occurrences of the same order. -/
theorem generalCoreEllipticPoint_orbit_injective (j k : Fin orders.length)
    (a : K₀) (ha : a • generalCoreEllipticPoint g orders s t ho hdef d hd hb j =
      generalCoreEllipticPoint g orders s t ho hdef d hd hb k) : j = k := by
  have hv := congrArg (fun p : fuchsianCyclicFixedPoints D₀ .elliptic => p.val) ha
  apply generalCoreConePoint_orbit_injective g orders s t ho hdef d hd hb j k ((E₀).symm a)
  apply (f₀).injective
  rw [generalCoreTargetCayleyEquiv_action, (E₀).apply_symm_apply]
  exact Subtype.ext hv

/-- The literal actual elliptic-point orbit class. -/
def generalCoreEllipticPointClass (j : Fin orders.length) :
    MulAction.orbitRel.Quotient K₀ (fuchsianCyclicFixedPoints D₀ .elliptic) :=
  Quotient.mk'' (generalCoreEllipticPoint g orders s t ho hdef d hd hb j)

/-- Both injectivity and surjectivity refer to every actual target orbit. -/
theorem generalCoreEllipticPointClass_bijective (ht : 0 < t) :
    Function.Bijective (generalCoreEllipticPointClass g orders s t ho hdef d hd hb) := by
  constructor
  · intro j k he
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he)
    exact (generalCoreEllipticPoint_orbit_injective g orders s t ho hdef d hd hb k j a ha).symm
  · intro q
    induction q using Quotient.inductionOn' with
    | h p =>
      obtain ⟨j, a, ha⟩ := generalCoreEllipticPoint_orbit g orders s t ho hdef d hd hb ht p
      exact ⟨j, Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨a, ha⟩)⟩

/-- All actual maximal elliptic cyclic subgroup conjugacy classes are
exactly the original occurrence set. No selected subset is enumerated. -/
def generalCoreEllipticClassEquiv (ht : 0 < t) :
    Fin orders.length ≃ FuchsianCyclicConjugacyClasses D₀ .elliptic :=
  (Equiv.ofBijective (generalCoreEllipticPointClass g orders s t ho hdef d hd hb)
    (generalCoreEllipticPointClass_bijective g orders s t ho hdef d hd hb ht)).trans
      (fuchsianCyclicConjugacyClassesEquiv D₀ .elliptic).symm

/-- Each full actual elliptic class has exactly its original order. -/
theorem generalCoreEllipticClassEquiv_order (ht : 0 < t) (j : Fin orders.length) :
    fuchsianEllipticClassOrder D₀ (generalCoreEllipticClassEquiv g orders s t ho hdef d hd hb ht j) =
      orders[j] := by
  change fuchsianEllipticClassOrder D₀
    (Quotient.mk _ (fuchsianCyclicPointStabilizer D₀ .elliptic
      (generalCoreEllipticPoint g orders s t ho hdef d hd hb j))) = _
  rw [fuchsianEllipticClassOrder_mk]
  change Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer K₀ (f₀ (c₀ j)).val) = _
  rw [← Nat.card_congr ((P₀).cayleyData.stabilizerEquivBoundary (f₀ (c₀ j))).toEquiv]
  calc
    Nat.card (MulAction.stabilizer K₀ (f₀ (c₀ j))) = Nat.card (MulAction.stabilizer H₀ (c₀ j)) :=
      (Nat.card_congr (generalCoreTargetCayley_stabilizerEquiv g orders s t ho hdef d hd hb (c₀ j)).toEquiv).symm
    _ = _ := generalCoreConePoint_stabilizer_card g orders s t ho hdef d hd hb j

/-- Finiteness is a consequence of complete actual class exhaustion. -/
theorem generalCoreEllipticClasses_finite (ht : 0 < t) :
    Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic) :=
  Finite.of_equiv (Fin orders.length) (generalCoreEllipticClassEquiv g orders s t ho hdef d hd hb ht)

/-- The actual entire elliptic order list is precisely the prescribed
original list, retaining all occurrence multiplicities. -/
theorem generalCore_elliptic_orders_perm (ht : 0 < t)
    [Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic)] :
    orders.Perm (fuchsianEllipticOrderList D₀) := by
  classical
  let actualEllipticFintype := Fintype.ofFinite (FuchsianCyclicConjugacyClasses D₀ .elliptic)
  let e := (generalCoreEllipticClassEquiv g orders s t ho hdef d hd hb ht).trans
    (Fintype.equivFin (FuchsianCyclicConjugacyClasses D₀ .elliptic))
  conv_lhs => rw [← List.ofFn_getElem (xs := orders)]
  apply signature_orderList_perm_of_equiv e
  intro j
  change fuchsianEllipticClassOrder D₀
    ((Fintype.equivFin (FuchsianCyclicConjugacyClasses D₀ .elliptic)).symm
      ((Fintype.equivFin (FuchsianCyclicConjugacyClasses D₀ .elliptic))
        (generalCoreEllipticClassEquiv g orders s t ho hdef d hd hb ht j))) = orders[j]
  rw [Equiv.symm_apply_apply]
  exact generalCoreEllipticClassEquiv_order g orders s t ho hdef d hd hb ht j

end LowDimensionalTopology.Geometry.Fuchsian
