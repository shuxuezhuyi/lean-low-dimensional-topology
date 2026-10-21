/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.Assembly
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureCofiniteExistenceConsumer
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetArea
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureEllipticClasses
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetCuspCensus
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureBoundaryCensus
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
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

section ActualPositiveBoundaryGroup
variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "P₀" => generalCoreTargetMobiusData g orders s t ho hdef d hd hb
local notation "K₀" => generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb
local notation "D₀" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.asFuchsianDisc P₀
local notation "Pdisc" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.cayleyData P₀

/-- The actual entire Cayley target has exactly the original cusp count. -/
theorem generalCoreTarget_cayley_parabolic_class_card
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    Nat.card (FuchsianCyclicConjugacyClasses (Pdisc).asFuchsianDisc .parabolic) = s := by
  have hdisc : (Pdisc).asFuchsianDisc = (D₀).nielsenConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius := by
    apply _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.eq_of_carrier_eq
    exact cayleyMobius_image_openHalfPlane.symm
  rw [hdisc]
  exact (Nat.card_congr (fuchsianCyclicClassConjugacyEquiv (D₀) .parabolic _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)).symm.trans
    (generalCoreTarget_parabolic_classes_card g orders s t ho hdef d hd hb hNE)

/-- The original construction realizes its complete genuine signature.
Every whole-group class and the physical core area are derived, and its
genus is the genus of the actual filled whole quotient. -/
theorem generalCoreTarget_actual_signature (ht : 0 < t) :
    HasNielsenFuchsianSignature Pdisc
      ((generalCoreTargetMobius_nonElementary g orders s t ho hdef d hd hb ht).conjugation
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
      (generalCoreTargetCayley_fg g orders s t ho hdef d hd hb) g orders s t := by
  let hNE := generalCoreTargetMobius_nonElementary g orders s t ho hdef d hd hb ht
  let hFG := generalCoreTargetCayley_fg g orders s t ho hdef d hd hb
  let actualEllipticFinite := generalCoreEllipticClasses_finite g orders s t ho hdef d hd hb ht
  obtain ⟨w, hw, _⟩ := exists_dirichlet_center_in_nielsenCore Pdisc (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
  let F := dirichletDomain Pdisc w
  have hF := dirichletDomain_fundamental Pdisc w hw
  apply hasNielsenSignature_of_actual_census_and_area Pdisc (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) hFG
    g orders s t
    (generalCore_elliptic_orders_perm g orders s t ho hdef d hd hb ht)
    (generalCoreTarget_cayley_parabolic_class_card g orders s t ho hdef d hd hb hNE).symm
    (generalCoreTarget_boundary_class_card g orders s t ho hdef d hd hb hNE).symm F hF
  rw [generalCoreTarget_cayley_nielsen_area g orders s t ho hdef d hd hb hNE F hF]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.pi*generalCoreDeficit g orders s t)]
  rfl

end ActualPositiveBoundaryGroup

/-- Every admissible positive deficit is realized by an actual finitely
generated non-elementary Fuchsian group with its full prescribed signature.
The zero-boundary and positive-boundary constructions exhaust all cases. -/
theorem generalSignature_realization_exists (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t) :
    ∃ H : Subgroup Mobius.complexMobiusGroup, ∃ P : UnitDiscFuchsianGroup H,
      ∃ hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H, ∃ hFG : H.FG,
        HasNielsenFuchsianSignature P hNE hFG g orders s t := by
  by_cases ht : t = 0
  · subst t
    obtain ⟨H, P, hFG, hfirst, hsignature, _⟩ :=
      generalSignature_cofinite_realization_exists g orders s ho
        (by simpa only [generalCoreDeficit, Nat.cast_zero, add_zero] using hdef)
    exact ⟨H, P, P.asFuchsianDisc.firstKind_nonElementary hfirst, hFG, hsignature⟩
  · obtain ⟨d, hd, hb, _⟩ := generalCore_polygon_exists g orders s t ho hdef
    let P := generalCoreTargetMobiusData g orders s t ho hdef d hd hb
    exact ⟨_, P.cayleyData,
      (generalCoreTargetMobius_nonElementary g orders s t ho hdef d hd hb (by omega)).conjugation
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius,
      generalCoreTargetCayley_fg g orders s t ho hdef d hd hb,
      generalCoreTarget_actual_signature g orders s t ho hdef d hd hb (by omega)⟩

/--
The exact realizability criterion, with genuine group
signatures and no extra geometric, census, area or genus hypotheses.
-/
theorem generalSignature_realization_iff (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) :
    (∃ H : Subgroup Mobius.complexMobiusGroup, ∃ P : UnitDiscFuchsianGroup H,
      ∃ hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H, ∃ hFG : H.FG,
        HasNielsenFuchsianSignature P hNE hFG g orders s t) ↔
      0 < generalCoreDeficit g orders s t := by
  constructor
  · rintro ⟨H, P, hNE, hFG, hsignature⟩
    exact hsignature.deficit_pos
  · exact generalSignature_realization_exists g orders s t ho

/-- The same exact criterion in the original numerical-signature interface. -/
theorem FuchsianSignature.realization_iff_deficit_pos (σ : FuchsianSignature) :
    (∃ H : Subgroup Mobius.complexMobiusGroup, ∃ P : UnitDiscFuchsianGroup H,
      ∃ hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H, ∃ hFG : H.FG,
        HasNielsenFuchsianSignature P hNE hFG σ.genus σ.ellipticOrders
          σ.parabolicEnds σ.boundaryHyperbolicEnds) ↔ 0 < σ.deficit :=
  generalSignature_realization_iff σ.genus σ.ellipticOrders σ.parabolicEnds
    σ.boundaryHyperbolicEnds σ.ellipticOrders_two_le

end LowDimensionalTopology.Geometry.Fuchsian
