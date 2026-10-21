/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.ThreeCuspRigidity
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteRotationSectors
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Actual regular values and elliptic peripheral lifts

The regular locus removes the literal elliptic values and their full preimage.
The restricted original quotient projection is a genuine covering. Centered
physical quotient charts have degree equal to the full stabilizer order.
Their literal peripheral lifts close exactly for integer multiples of that
actual order, and every point along each lift is regular for the whole group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open Set
  Topology
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
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

/-- The elliptic mark determined by a physical center is its actual quotient projection. -/
theorem fuchsianEllipticClassQuotientPoint_of_fixed_point
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (p : fuchsianCyclicFixedPoints D .elliptic) :
    fuchsianEllipticClassQuotientPoint D
      (Quotient.mk _ (fuchsianCyclicPointStabilizer D .elliptic p)) =
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain (fuchsianEllipticFixedPointInDisc D p) := by
  change Quotient.mk _ (fuchsianEllipticFixedPointInDisc D
    ((fuchsianCyclicPointStabilizerEquiv D .elliptic).symm
      ((fuchsianCyclicPointStabilizerEquiv D .elliptic) p))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The actual marked elliptic values are exactly the fibers containing a point
with nontrivial original whole-group stabilizer. -/
theorem original_projection_mem_elliptic_marks_iff
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (z : D.domain.carrier) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z ∈ range (fuchsianEllipticClassQuotientPoint D) ↔
      ∃ g : H, g ≠ 1 ∧ g • z = z := by
  constructor
  · rintro ⟨c, hc⟩
    induction c using Quotient.inductionOn with
    | _ K =>
      let p := (fuchsianCyclicPointStabilizerEquiv D .elliptic).symm K
      have hp : fuchsianEllipticClassQuotientPoint D (Quotient.mk _ K) =
          _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain (fuchsianEllipticFixedPointInDisc D p) := by
        have h := fuchsianEllipticClassQuotientPoint_of_fixed_point D p
        change fuchsianEllipticClassQuotientPoint D
          (Quotient.mk _ ((fuchsianCyclicPointStabilizerEquiv D .elliptic)
            ((fuchsianCyclicPointStabilizerEquiv D .elliptic).symm K))) = _ at h
        simpa only [Equiv.apply_symm_apply] using h
      obtain ⟨k, hk⟩ := Quotient.exact (hp.symm.trans hc)
      change k • z = fuchsianEllipticFixedPointInDisc D p at hk
      obtain ⟨f, hfH, hf, hfix⟩ := p.property.2
      let g : H := ⟨f, hfH⟩
      have hgn : g ≠ 1 := fun h => hf.1 (congrArg Subtype.val h)
      have hgfix : g • fuchsianEllipticFixedPointInDisc D p =
          fuchsianEllipticFixedPointInDisc D p := Subtype.ext hfix
      refine ⟨k⁻¹ * g * k, ?_, ?_⟩
      · intro h
        apply hgn
        calc
          g = k * (k⁻¹ * g * k) * k⁻¹ := by group
          _ = 1 := by rw [h]; group
      · rw [mul_smul, mul_smul, hk, hgfix, ← hk, inv_smul_smul]
  · rintro ⟨g, hgn, hfix⟩
    have hfn : g.val ≠ 1 := fun h => hgn (Subtype.ext h)
    have hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val := fuchsianDisc_nonidentity_fixed_elliptic D
      g.val g.property hfn z.val z.property (congrArg Subtype.val hfix)
    let p : fuchsianCyclicFixedPoints D .elliptic :=
      ⟨z.val, (fun _ => z.property), g.val, g.property, hg, congrArg Subtype.val hfix⟩
    exact ⟨Quotient.mk _ (fuchsianCyclicPointStabilizer D .elliptic p),
      fuchsianEllipticClassQuotientPoint_of_fixed_point D p⟩

/-- The regular values of the original quotient are obtained by deleting exactly
the actual elliptic marked points, retaining all other old quotient points. -/
def fuchsianRegularQuotientSet
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) :
    Set (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain) :=
  (range (fuchsianEllipticClassQuotientPoint D))ᶜ

/-- No point of a regular fiber has a nontrivial actual stabilizer. -/
theorem original_regular_value_iff_stabilizer_bot
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (z : D.domain.carrier) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z ∈ fuchsianRegularQuotientSet D ↔
      MulAction.stabilizer H z = ⊥ := by
  change (¬_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z ∈ range (fuchsianEllipticClassQuotientPoint D)) ↔ _
  rw [original_projection_mem_elliptic_marks_iff]
  constructor
  · intro h
    apply le_antisymm
    · intro g hg
      change g = 1
      by_contra hgn
      exact h ⟨g, hgn, hg⟩
    · exact bot_le
  · intro h ⟨g, hgn, hfix⟩
    have hg : g ∈ MulAction.stabilizer H z := hfix
    rw [h] at hg
    exact hgn hg

/-- Regular-value deletion is exactly the image of the actual free locus. -/
theorem fuchsianRegularQuotientSet_eq_free_image
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H) :
    fuchsianRegularQuotientSet D = _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain ''
      {z : D.domain.carrier | MulAction.stabilizer H z = ⊥} := by
  ext q
  constructor
  · intro hq
    obtain ⟨z, rfl⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_surjective D.domain q
    exact ⟨z, (original_regular_value_iff_stabilizer_bot D z).mp hq, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact (original_regular_value_iff_stabilizer_bot D z).mpr hz

/-- After removing all actual elliptic values and their full preimages, the
original quotient projection is a genuine unramified topological covering. -/
theorem fuchsian_regular_projection_covering
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H) :
    IsCoveringMap ((fuchsianRegularQuotientSet D).restrictPreimage (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain)) := by
  let : ProperlyDiscontinuousSMul H D.domain.carrier :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.isDiscontinuous_iff_properlyDiscontinuousSMul H D.domain.carrier).mp
      ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_iff_subtype H D.carrier D.invariant).mp D.discontinuous)
  have h : IsCoveringMapOn (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain) (fuchsianRegularQuotientSet D) := by
    rw [fuchsianRegularQuotientSet_eq_free_image]
    exact isCoveringMapOn_quotientMk_of_properlyDiscontinuousSMul
  exact h.isCoveringMap_restrictPreimage

/-- The regular old quotient is open whenever the actual elliptic class space is finite. -/
theorem fuchsianRegularQuotientSet_isOpen
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    [Finite (FuchsianCyclicConjugacyClasses D .elliptic)] : IsOpen (fuchsianRegularQuotientSet D) := by
  let := (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).t2Space
  exact (Set.finite_range (fuchsianEllipticClassQuotientPoint D)).isClosed.isOpen_compl

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set
  Topology
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
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

/-- Every original physical point admits a true quotient power chart centered
at that point, whose local group is the actual full point stabilizer. -/
theorem fuchsian_centered_quotient_branch_chart
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (z : D.domain.carrier) :
    ∃ C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D.domain,
      C.normalizer.val z.val = (0 : ℂ) ∧ C.stabilizer = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z.val ∧
      z.val ∈ C.disc ∧ C.degree = Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z.val) := by
  obtain ⟨q, r, hr, hqz, _hd, hzN, hcl, hrot, hsep⟩ :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_discontinuous_roundDisc H D.carrier D.isDisc.isOpen D.invariant
      D.discontinuous z.val z.property
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z.val
  have hfin : Finite K := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer_finite H D.discontinuous z.val z.property).to_subtype
  have hi : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer := by
    intro f hf
    obtain ⟨a, _, rfl⟩ := hrot f hf
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty a
  have hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K, f.val (0 : ℂ) = (0 : ℂ) := by
    intro f hf
    obtain ⟨a, _, rfl⟩ := hrot f hf
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero a
  have hND : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r ⊆ D.carrier := subset_closure.trans hcl
  have hKH : K ≤ H := fun f hf => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H z.val f).mp hf).1
  have hseparated : ∀ g ∈ H, g ∉ K →
      Disjoint (g.val '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) := by
    intro g hg hn
    apply (hsep ⟨g, hg⟩).2
    intro hfix
    exact hn ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H z.val g).mpr ⟨hg, hfix⟩)
  let C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D.domain := ⟨K, hfin, q, hi, hz, r, hr, hND, hKH, hseparated⟩
  exact ⟨C, hqz, rfl, hzN, subgroupConjugate_natCard q K⟩

/-- The actual branch degree at an elliptic center is its actual maximal cyclic
class order, with no separately supplied ramification index. -/
theorem fuchsian_elliptic_center_branch_degree
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (p : fuchsianCyclicFixedPoints D .elliptic) :
    ∃ C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D.domain,
      C.normalizer.val p.val = (0 : ℂ) ∧ C.stabilizer = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val ∧
      p.val ∈ C.disc ∧ C.degree = fuchsianEllipticClassOrder D
        (Quotient.mk _ (fuchsianCyclicPointStabilizer D .elliptic p)) := by
  obtain ⟨C, h0, hK, hp, hn⟩ := fuchsian_centered_quotient_branch_chart D
    (fuchsianEllipticFixedPointInDisc D p)
  exact ⟨C, h0, hK, hp, hn⟩

/-- The centered local chart has no other physical elliptic center: every
nonzero local coordinate is an actual regular point for the whole original group. -/
theorem centered_branch_punctured_point_free
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (z : D.domain.carrier) (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D.domain)
    (h0 : C.normalizer.val z.val = (0 : ℂ))
    (hK : C.stabilizer = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z.val)
    (w : C.disc) (hw : (C.coordinate w).val ≠ 0) :
    ∀ g : H, g • (⟨w.val, C.disc_subset w.property⟩ : D.domain.carrier) =
      (⟨w.val, C.disc_subset w.property⟩ : D.domain.carrier) → g = 1 := by
  intro g hg
  have hfix : g.val.val w.val = w.val := congrArg Subtype.val hg
  have hgK : g.val ∈ C.stabilizer := by
    by_contra hn
    have hdisj := C.separated g.val g.property hn
    exact disjoint_left.mp hdisj ⟨w.val, w.property, hfix⟩ w.property
  have hgz : g.val.val z.val = z.val :=
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H z.val g.val).mp (hK ▸ hgK)).2
  by_contra hgn
  have hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val := fuchsianDisc_nonidentity_fixed_elliptic D
    g.val g.property (fun h => hgn (Subtype.ext h)) z.val z.property hgz
  obtain ⟨p, hp, hu⟩ := elliptic_disc_existsUnique_fixed g.val hf D.isDisc (D.image_eq g)
  have hzEq : z = p := hu z hgz
  have hwEq : (⟨w.val, C.disc_subset w.property⟩ : D.domain.carrier) = p :=
    hu ⟨w.val, C.disc_subset w.property⟩ hfix
  have hwz : w.val = z.val := congrArg Subtype.val (hwEq.trans hzEq.symm)
  have he := C.coordinate_coe w
  rw [hwz, h0] at he
  exact hw (OnePoint.coe_injective he.symm)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- The actual circular lift of an integer-turn peripheral loop through a degree-n power chart. -/
def _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift (n : ℕ) (ρ : ℝ) (k : ℤ) (t : ℝ) : ℂ :=
  circleMap 0 ρ (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n * (k : ℝ) * t)

theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_continuous (n : ℕ) (ρ : ℝ) (k : ℤ) :
    Continuous (_root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift n ρ k) := by
  unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift
  simp only [circleMap_zero]
  fun_prop

theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_norm (n : ℕ) (ρ : ℝ) (k : ℤ) (t : ℝ) :
    ‖_root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift n ρ k t‖ = |ρ| := norm_circleMap_zero _ _

/-- The physical lift projects to exactly k turns around the branch value. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_pow
    (n : ℕ)
    (hn : n ≠ 0)
    (ρ : ℝ)
    (k : ℤ)
    (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift n ρ k t ^ n = circleMap 0 (ρ ^ n) (2 * Real.pi * (k : ℝ) * t) := by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift, circleMap_zero_pow]
  congr 1
  calc
    (n : ℝ) * (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n * (k : ℝ) * t) =
        ((n : ℝ) * _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n) * (k : ℝ) * t := by ring
    _ = 2 * Real.pi * (k : ℝ) * t := by rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod_mul n hn]

theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_zero (n : ℕ) (ρ : ℝ) (k : ℤ) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift n ρ k 0 = (ρ : ℂ) := by
  simp [_root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift, circleMap_zero]

/-- The endpoint is the genuine primitive degree-n rotation raised to k. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_one (n : ℕ) (ρ : ℝ) (k : ℤ) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift n ρ k 1 =
      (ρ : ℂ) * ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ k : Circle) : ℂ) := by
  have h : Circle.exp (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n * (k : ℝ)) = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ k := by
    rw [mul_comm, Circle.exp_intCast_mul]
    rfl
  have hc := congrArg (fun u : Circle => (u : ℂ)) h
  simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift, mul_one, circleMap_zero,
    Circle.coe_exp] using
    congrArg (fun z : ℂ => (ρ : ℂ) * z) hc

/-- The lifted peripheral path closes exactly for multiples of the actual local degree.
The statement retains signed integer turns and the literal two endpoints. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_closed_iff (n : ℕ) (hn : n ≠ 0)
    (ρ : ℝ) (hρ : ρ ≠ 0) (k : ℤ) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift n ρ k 1 = _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift n ρ k 0 ↔ (n : ℤ) ∣ k := by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_one,
    _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_zero]
  have hcancel : ((ρ : ℂ) * ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ k : Circle) : ℂ) = (ρ : ℂ)) ↔
      ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ k : Circle) : ℂ) = 1 := by
    constructor
    · intro h
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hρ) (h.trans (mul_one _).symm)
    · intro h
      rw [h, mul_one]
  rw [hcancel]
  change ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ k : Circle) : ℂ) = ((1 : Circle) : ℂ) ↔ (n : ℤ) ∣ k
  constructor
  · intro h
    have he : (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ k : Circle) = 1 := Circle.coe_injective h
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr he
    rwa [← (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot n hn).eq_orderOf] at hd
  · intro hd
    have he : (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ^ k : Circle) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rwa [← (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot n hn).eq_orderOf])
    exact congrArg (fun u : Circle => (u : ℂ)) he

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open Set Topology

namespace MobiusQuotientChartData

variable {G : Subgroup Mobius.complexMobiusGroup} {D : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain G}

/-- The physical lift of a signed peripheral loop in an actual quotient chart. -/
def peripheralLiftPoint (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D) (ρ : ℝ)
    (hρ : 0 < ρ) (hρr : ρ < C.radius) (k : ℤ) (t : ℝ) : C.disc :=
  C.coordinate.symm ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift C.degree ρ k t, by
    rw [Metric.mem_ball, dist_zero_right, _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_norm,
      abs_of_pos hρ]
    exact hρr⟩

theorem peripheralLiftPoint_continuous
    (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D)
    (ρ : ℝ)
    (hρ : 0 < ρ) (hρr : ρ < C.radius) (k : ℤ) :
    Continuous (C.peripheralLiftPoint ρ hρ hρr k) := by
  exact C.coordinate.symm.continuous.comp
    ((_root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_continuous C.degree ρ k).subtype_mk _)

/-- The original quotient projection has exactly the literal integer-turn
circle as its value in the actual branch coordinate. -/
theorem peripheralLiftPoint_projection
    (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D)
    (ρ : ℝ)
    (hρ : 0 < ρ) (hρr : ρ < C.radius) (k : ℤ) (t : ℝ) :
    C.chart (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscDomainProjection D C.disc C.disc_subset
      (C.peripheralLiftPoint ρ hρ hρr k t)) =
      circleMap 0 (ρ ^ C.degree) (2 * Real.pi * (k : ℝ) * t) := by
  rw [C.chart_apply_projection]
  simp only [peripheralLiftPoint, Homeomorph.apply_symm_apply]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_pow C.degree C.degree_pos.ne' ρ k t

/-- In the actual physical invariant domain the lift closes if and only if
its signed winding is divisible by the actual full stabilizer order. -/
theorem peripheralLiftPoint_closed_iff
    (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D)
    (ρ : ℝ)
    (hρ : 0 < ρ) (hρr : ρ < C.radius) (k : ℤ) :
    C.peripheralLiftPoint ρ hρ hρr k 1 = C.peripheralLiftPoint ρ hρ hρr k 0 ↔
      (C.degree : ℤ) ∣ k := by
  rw [peripheralLiftPoint, peripheralLiftPoint, C.coordinate.symm.injective.eq_iff,
    Subtype.mk.injEq]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.powerPeripheralLift_closed_iff C.degree C.degree_pos.ne' ρ hρ.ne' k

end MobiusQuotientChartData

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- Each point of the actual peripheral lift is regular for the whole
original group, not merely for the selected finite local subgroup. -/
theorem centered_peripheralLiftPoint_free
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (z : D.domain.carrier) (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData D.domain)
    (h0 : C.normalizer.val z.val = (0 : ℂ))
    (hK : C.stabilizer = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z.val)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < C.radius) (k : ℤ) (t : ℝ) :
    ∀ g : H, g • (⟨(C.peripheralLiftPoint ρ hρ hρr k t).val,
        C.disc_subset (C.peripheralLiftPoint ρ hρ hρr k t).property⟩ : D.domain.carrier) =
      (⟨(C.peripheralLiftPoint ρ hρ hρr k t).val,
        C.disc_subset (C.peripheralLiftPoint ρ hρ hρr k t).property⟩ : D.domain.carrier) → g = 1 := by
  apply centered_branch_punctured_point_free D z C h0 hK
  have hn := powerPeripheralLift_norm C.degree ρ k t
  intro he
  simp only [_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusQuotientChartData.peripheralLiftPoint,
    Homeomorph.apply_symm_apply] at he
  rw [he, norm_zero, abs_of_pos hρ] at hn
  exact hρ.ne' hn.symm

end LowDimensionalTopology.Geometry.Fuchsian
