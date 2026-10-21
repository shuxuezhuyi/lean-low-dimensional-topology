/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic

public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.Algebra
public import LowDimensionalTopology.Geometry.Mobius.Trace.DiscTraces
public import LowDimensionalTopology.Geometry.Mobius.Trace.MobiusInvariants
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.UpperHalfSpace
public import LowDimensionalTopology.Geometry.Mobius.HyperbolicExtension
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HyperbolicExamples
public import LowDimensionalTopology.Geometry.Inversive.GeneralizedSpheres
public import Mathlib.Algebra.Group.Action.Sum
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareExtension
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.DensityMetric
public import LowDimensionalTopology.Geometry.Mobius.CrossRatio.MobiusTriples
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Elementary Möbius groups and finite orbits

The boundary and interior actions on the closed hyperbolic half-space define
elementarity through finite orbits. Common fixed points and invariant pairs
lead to affine and scaling/reciprocal normal forms. The multiplier quotient
records the translation kernel. Equivariant folding compares this convention
with finite orbits in the full compactification. Finally, the punctured-plane
density metric makes the invariant-pair normal forms act by isometries.
-/

@[expose] public section

open Set Function Filter Manifold
open scoped OnePoint ComplexConjugate Pointwise RealInnerProductSpace

namespace LowDimensionalTopology.Geometry.DiscreteGroups

open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius

noncomputable section


open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The genuine closed hyperbolic half-space, as a subset of compactified Euclidean three-space. -/
abbrev ClosedUpperHalfSpace := closure Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet

/-- The actual interior embedding identifies H3 with its compactified open image. -/
def upperHalfSpaceImageEquiv : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace ≃
    Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet :=
  Equiv.Set.image (OnePoint.some : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace → OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceSet OnePoint.coe_injective

/-- Boundary and interior are exactly the disjoint components of the closed half-space as a set. -/
def closedUpperHalfSpaceSumEquiv :
    Mobius.ExtendedComplex ⊕ Hyperbolic.QuaternionHalfSpace.UpperHalfSpace ≃ ClosedUpperHalfSpace := by
  classical
  let e₀ := Equiv.sumCongr Hyperbolic.QuaternionHalfSpace.extendedComplexUpperHalfSpaceBoundary.toEquiv
    upperHalfSpaceImageEquiv
  have hd : Disjoint (frontier Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet)
    Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet :=
    disjoint_frontier_iff_isOpen.mpr Hyperbolic.QuaternionHalfSpace.isOpen_extendedUpperHalfSpaceSet
  let e₁ := (Equiv.Set.union hd).symm
  let e₂ := Set.equivOfEq (show frontier Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet ∪
      Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet = closure
        Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet by
        rw [closure_eq_self_union_frontier]
        exact union_comm _ _)
  exact e₀.trans (e₁.trans e₂)

theorem closedUpperHalfSpaceSumEquiv_inl (z : Mobius.ExtendedComplex) :
    (closedUpperHalfSpaceSumEquiv (Sum.inl z) : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding z := by
  rfl

theorem closedUpperHalfSpaceSumEquiv_inr (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (closedUpperHalfSpaceSumEquiv (Sum.inr q) : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      (q.val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  rfl

/-- The boundary action is the actual evaluation action of the complex Möbius group. -/
def mobiusBoundaryOrbit (H : Subgroup Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex) :
    Set Mobius.ExtendedComplex := MulAction.orbit H z

/-- This property concerns boundary orbits only, and is not used as the definition of elementarity. -/
def MobiusBoundaryFiniteOrbit (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  DiscreteGroups.Action.HasFiniteOrbit H Mobius.ExtendedComplex

theorem mobiusBoundaryFiniteOrbit_of_finite (H : Subgroup Mobius.complexMobiusGroup) [Finite H] :
    MobiusBoundaryFiniteOrbit H := DiscreteGroups.Action.hasFiniteOrbit_of_finite

theorem mobiusBoundaryFiniteOrbit_of_fixed (H : Subgroup Mobius.complexMobiusGroup)
    (z : Mobius.ExtendedComplex) (hz : ∀ g : H, g • z = z) : MobiusBoundaryFiniteOrbit H :=
  DiscreteGroups.Action.hasFiniteOrbit_of_fixed z hz

/-- Every actual nonidentity complex Möbius map has only finitely many boundary fixed points. -/
theorem mobius_boundary_fixedPoints_finite (f : Mobius.complexMobiusGroup) (hf : f ≠ 1) :
    {z : Mobius.ExtendedComplex | (f : Equiv.Perm Mobius.ExtendedComplex) z = z}.Finite := by
  obtain h | h := Mobius.mobius_nonidentity_fixedPoint_dichotomy f hf
  · obtain ⟨a, ha⟩ := h
    have heq : {z : Mobius.ExtendedComplex | (f : Equiv.Perm Mobius.ExtendedComplex) z = z} = {a} := by
      ext z
      exact ha z
    rw [heq]
    exact Set.finite_singleton a
  · obtain ⟨a, b, hab, ha⟩ := h
    have heq : {z : Mobius.ExtendedComplex | (f : Equiv.Perm Mobius.ExtendedComplex) z = z} = {a, b} := by
      ext z
      exact ha z
    rw [heq]
    exact (Set.finite_singleton b).insert a

/-- A vertex is fixed by some nonidentity element of the finite Möbius group. -/
def mobiusVertices (H : Subgroup Mobius.complexMobiusGroup) : Set Mobius.ExtendedComplex :=
  {z | ∃ g : H, g ≠ 1 ∧ g • z = z}

theorem mem_mobiusVertices_iff (H : Subgroup Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex) :
    z ∈ mobiusVertices H ↔ ∃ g : H, g ≠ 1 ∧ g • z = z := Iff.rfl

theorem mobiusVertices_finite (H : Subgroup Mobius.complexMobiusGroup) [Finite H] :
    (mobiusVertices H).Finite := by
  have hU : (⋃ g : {g : H // g ≠ 1}, {z : Mobius.ExtendedComplex | g.val • z = z}).Finite := by
    apply Set.finite_iUnion
    intro g
    exact mobius_boundary_fixedPoints_finite (g.val : Mobius.complexMobiusGroup) (by
      intro he
      exact g.property (Subtype.ext he))
  apply hU.subset
  rintro z ⟨g, hg, hfix⟩
  exact Set.mem_iUnion.mpr ⟨⟨g, hg⟩, hfix⟩

theorem mobiusVertices_smul (H : Subgroup Mobius.complexMobiusGroup) (g : H)
    {z : Mobius.ExtendedComplex} (hz : z ∈ mobiusVertices H) : g • z ∈ mobiusVertices H := by
  obtain ⟨f, hf, hfix⟩ := hz
  refine ⟨g * f * g⁻¹, ?_, ?_⟩
  · intro he
    apply hf
    have h := congrArg (fun k : H => g⁻¹ * k * g) he
    simpa [mul_assoc] using h
  · simp only [mul_smul, inv_smul_smul, hfix]

theorem mobiusVertices_smul_iff (H : Subgroup Mobius.complexMobiusGroup) (g : H)
    (z : Mobius.ExtendedComplex) : g • z ∈ mobiusVertices H ↔ z ∈ mobiusVertices H := by
  constructor
  · intro hz
    simpa only [inv_smul_smul] using mobiusVertices_smul H g⁻¹ hz
  · exact mobiusVertices_smul H g

/-- The genuine boundary and Poincaré interior actions induce an action on the actual closed half-space. -/
instance mobiusClosedUpperHalfSpaceMulAction : MulAction Mobius.complexMobiusGroup ClosedUpperHalfSpace where
  smul f q := closedUpperHalfSpaceSumEquiv (f • closedUpperHalfSpaceSumEquiv.symm q)
  one_smul q := by
    change closedUpperHalfSpaceSumEquiv (1 • closedUpperHalfSpaceSumEquiv.symm q) = q
    rw [one_smul, closedUpperHalfSpaceSumEquiv.apply_symm_apply]
  mul_smul f g q := by
    change closedUpperHalfSpaceSumEquiv ((f * g) • closedUpperHalfSpaceSumEquiv.symm q) =
      closedUpperHalfSpaceSumEquiv (f • closedUpperHalfSpaceSumEquiv.symm
        (closedUpperHalfSpaceSumEquiv (g • closedUpperHalfSpaceSumEquiv.symm q)))
    rw [closedUpperHalfSpaceSumEquiv.symm_apply_apply, mul_smul]

instance closedUpperHalfSpaceInhabited : Inhabited ClosedUpperHalfSpace := ⟨closedUpperHalfSpaceSumEquiv (Sum.inl ∞)⟩

theorem closedUpperHalfSpaceSumEquiv_equivariant (H : Subgroup Mobius.complexMobiusGroup)
    (g : H) (q : Mobius.ExtendedComplex ⊕ Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    closedUpperHalfSpaceSumEquiv (g • q) = g • closedUpperHalfSpaceSumEquiv q := by
  change closedUpperHalfSpaceSumEquiv ((g : Mobius.complexMobiusGroup) • q) =
    closedUpperHalfSpaceSumEquiv ((g : Mobius.complexMobiusGroup) •
      closedUpperHalfSpaceSumEquiv.symm (closedUpperHalfSpaceSumEquiv q))
  rw [closedUpperHalfSpaceSumEquiv.symm_apply_apply]

/-- The transported action agrees exactly with the actual complex boundary permutation. -/
theorem closed_smul_boundary (f : Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex) :
    ((f • closedUpperHalfSpaceSumEquiv (Sum.inl z) : ClosedUpperHalfSpace) :
      OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding ((f : Equiv.Perm Mobius.ExtendedComplex) z) := by
  change (closedUpperHalfSpaceSumEquiv
    (f • closedUpperHalfSpaceSumEquiv.symm (closedUpperHalfSpaceSumEquiv (Sum.inl z))) :
      OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = _
  rw [closedUpperHalfSpaceSumEquiv.symm_apply_apply, Sum.smul_inl,
    closedUpperHalfSpaceSumEquiv_inl]
  rfl

/-- On actual interior points it agrees exactly with the proven Poincaré action. -/
theorem closed_smul_interior (f : Mobius.complexMobiusGroup) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    ((f • closedUpperHalfSpaceSumEquiv (Sum.inr q) : ClosedUpperHalfSpace) :
      OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      ((Mobius.mobiusPoincareHom f q).val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  change (closedUpperHalfSpaceSumEquiv
    (f • closedUpperHalfSpaceSumEquiv.symm (closedUpperHalfSpaceSumEquiv (Sum.inr q))) :
      OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = _
  rw [closedUpperHalfSpaceSumEquiv.symm_apply_apply, Sum.smul_inr,
    closedUpperHalfSpaceSumEquiv_inr, Mobius.mobiusUpperHalfSpace_smul]

/-- Using the closed-hyperbolic-space formulation. -/
def IsElementary (H : Subgroup Mobius.complexMobiusGroup) : Prop := DiscreteGroups.Action.HasFiniteOrbit H
    ClosedUpperHalfSpace

/-- A non-elementary subgroup has no finite orbit in the closed hyperbolic model. -/
def IsNonElementary (H : Subgroup Mobius.complexMobiusGroup) : Prop := ¬ IsElementary H

/-- Interior finite orbits are retained; boundary finite orbits alone are not the definition. -/
theorem isElementary_iff_boundary_or_interior (H : Subgroup Mobius.complexMobiusGroup) :
    IsElementary H ↔ MobiusBoundaryFiniteOrbit H ∨ DiscreteGroups.Action.HasFiniteOrbit H
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace := by
  unfold IsElementary MobiusBoundaryFiniteOrbit
  rw [DiscreteGroups.Action.hasFiniteOrbit_equivariant_iff closedUpperHalfSpaceSumEquiv
    (closedUpperHalfSpaceSumEquiv_equivariant H), DiscreteGroups.Action.hasFiniteOrbit_sum_iff]

theorem isElementary_of_finite (H : Subgroup Mobius.complexMobiusGroup) [Finite H] :
    IsElementary H := DiscreteGroups.Action.hasFiniteOrbit_of_finite

theorem isElementary_of_fixed (H : Subgroup Mobius.complexMobiusGroup)
    (q : ClosedUpperHalfSpace) (hq : ∀ g : H, g • q = q) : IsElementary H :=
  DiscreteGroups.Action.hasFiniteOrbit_of_fixed q hq

theorem isElementary_of_boundary_fixed (H : Subgroup Mobius.complexMobiusGroup)
    (z : Mobius.ExtendedComplex) (hz : ∀ g : H, g • z = z) : IsElementary H :=
  (isElementary_iff_boundary_or_interior H).mpr
    (Or.inl (mobiusBoundaryFiniteOrbit_of_fixed H z hz))

theorem isElementary_of_interior_fixed (H : Subgroup Mobius.complexMobiusGroup)
    (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (hq : ∀ g : H, g • q = q) : IsElementary H :=
  (isElementary_iff_boundary_or_interior H).mpr
    (Or.inr (DiscreteGroups.Action.hasFiniteOrbit_of_fixed q hq))

/-- A subgroup of an elementary group inherits an actual finite point orbit. -/
theorem IsElementary.mono {H K : Subgroup Mobius.complexMobiusGroup} (hK : IsElementary K)
    (hHK : H ≤ K) : IsElementary H := by
  obtain ⟨q, hq⟩ := hK
  refine ⟨q, hq.subset ?_⟩
  rintro y ⟨g, rfl⟩
  exact MulAction.mem_orbit q (⟨g.val, hHK g.property⟩ : K)

/-- The finite-orbit power assertion holds for the actual closed-space action. -/
theorem elementary_positive_power (H : Subgroup Mobius.complexMobiusGroup) (hH : IsElementary H)
    (g : H) : ∃ q : ClosedUpperHalfSpace, (MulAction.orbit H q).Finite ∧
      ∃ n : ℕ, 0 < n ∧ ∀ r ∈ MulAction.orbit H q, (g ^ n) • r = r := by
  obtain ⟨q, hq⟩ := hH
  obtain ⟨n, hn, hfix⟩ := DiscreteGroups.Action.exists_positive_power_fixing_finite_orbit q hq g
  exact ⟨q, hq, n, hn, hfix⟩

/-- Every specified finite orbit admits one positive power fixing all its points. -/
theorem mobius_finite_orbit_positive_power (H : Subgroup Mobius.complexMobiusGroup)
    (q : ClosedUpperHalfSpace) (hq : (MulAction.orbit H q).Finite) (g : H) :
    ∃ n : ℕ, 0 < n ∧ ∀ r ∈ MulAction.orbit H q, (g ^ n) • r = r :=
  DiscreteGroups.Action.exists_positive_power_fixing_finite_orbit q hq g

section InvariantDiscGroups

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias reflection_commutes_of_invariant_sphere := Mobius.reflection_commutes_of_invariant_sphere

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias reflection_fixed_of_invariant_sphere := Mobius.reflection_fixed_of_invariant_sphere

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias unique_fixed_mem_invariant_sphere := Mobius.unique_fixed_mem_invariant_sphere

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias inverse_pair_fixed_of_invariant_sphere := Mobius.inverse_pair_fixed_of_invariant_sphere

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias unique_fixed_mem_boundary_of_invariant_domain := Mobius.unique_fixed_mem_boundary_of_invariant_domain

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias inverse_pair_fixed_of_invariant_domain := Mobius.inverse_pair_fixed_of_invariant_domain

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias fractional_disc_preserver_squaredTrace := Mobius.fractional_disc_preserver_squaredTrace

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias mobius_disc_preserver_squaredTrace := Mobius.mobius_disc_preserver_squaredTrace

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias normalized_disc_fixed_equation := Mobius.normalized_disc_fixed_equation

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias normalized_disc_fixed_characteristic := Mobius.normalized_disc_fixed_characteristic

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias normalized_disc_circle_fixed_trace_ge_four := Mobius.normalized_disc_circle_fixed_trace_ge_four

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias normalized_disc_off_circle_fixed_trace_le_four := Mobius.normalized_disc_off_circle_fixed_trace_le_four

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias fractional_squaredTrace_of_normalized_disc := Mobius.fractional_squaredTrace_of_normalized_disc

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias fractional_disc_circle_fixed_trace_ge_four := Mobius.fractional_disc_circle_fixed_trace_ge_four

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias fractional_disc_trace_lt_four_not_fixed_circle := Mobius.fractional_disc_trace_lt_four_not_fixed_circle

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias fractional_disc_trace_gt_four_finite_fixed_circle := Mobius.fractional_disc_trace_gt_four_finite_fixed_circle

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias mobius_disc_trace_lt_four_not_fixed_circle := Mobius.mobius_disc_trace_lt_four_not_fixed_circle

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias mobius_disc_trace_gt_four_finite_fixed_circle := Mobius.mobius_disc_trace_gt_four_finite_fixed_circle

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias mobiusBoundaryParabolic_real_unique_fixed := Mobius.mobiusBoundaryParabolic_real_unique_fixed

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias mobiusBoundaryParabolic_fixed_mem_boundary := Mobius.mobiusBoundaryParabolic_fixed_mem_boundary

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias fixed_pair_inverse_of_invariant_sphere := Mobius.fixed_pair_inverse_of_invariant_sphere

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias fixed_pair_inverse_of_invariant_domain := Mobius.fixed_pair_inverse_of_invariant_domain

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias fractional_disc_trace_gt_four_fixed_circle := Mobius.fractional_disc_trace_gt_four_fixed_circle

/-- Compatibility alias for the independent invariant-domain foundation. -/
alias mobius_disc_trace_gt_four_fixed_circle := Mobius.mobius_disc_trace_gt_four_fixed_circle

end InvariantDiscGroups













/-- The multipliers form a genuine multiplicative subgroup of the nonzero complex numbers. -/
def mobiusMultiplierRange : Subgroup ℂˣ := Mobius.mobiusMultiplierHom.range

/-- Translation by a prescribed complex number, as an actual geometric Mobius map. -/
def mobiusTranslation (b : ℂ) : Mobius.complexMobiusGroup :=
  Mobius.mobiusMatrixProjection (Mobius.Classification.affineMatrix 1 b)

theorem mobiusTranslation_coe (b z : ℂ) :
    (mobiusTranslation b : Equiv.Perm Mobius.ExtendedComplex) z = (z + b : ℂ) := by
  rw [mobiusTranslation, Mobius.mobiusMatrixProjection_apply, Mobius.Classification.affineMatrix_coe]
  simp

theorem mobiusTranslation_infty (b : ℂ) :
    (mobiusTranslation b : Equiv.Perm Mobius.ExtendedComplex) ∞ = ∞ := by
  rw [mobiusTranslation, Mobius.mobiusMatrixProjection_apply, Mobius.Classification.affineMatrix_infty]

/-- Multiplier one is equivalent to being an actual translation. -/
theorem mobiusMultiplier_eq_one_iff_translation (f : Mobius.mobiusInftyStabilizer) :
    Mobius.mobiusMultiplier f = 1 ↔ ∃ b : ℂ, f.1 = mobiusTranslation b := by
  constructor
  · intro hf
    exact ⟨Mobius.mobiusAffineConstant f,
      by simpa only [hf, mobiusTranslation] using Mobius.mobius_affine_representation f⟩
  · rintro ⟨b, hb⟩
    exact (Mobius.mobius_affine_parameters_unique f
      (a := 1) (b := b) (fun z => by rw [hb, mobiusTranslation_coe]; simp)).1


/-- A translation is the identity exactly when its displacement is zero. -/
theorem mobiusTranslation_eq_one_iff (b : ℂ) : mobiusTranslation b = 1 ↔ b = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun f : Mobius.complexMobiusGroup => (f : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ)) h
    change (mobiusTranslation b : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ) = (0 : ℂ) at h0
    simpa only [mobiusTranslation_coe, zero_add, OnePoint.coe_eq_coe] using h0
  · rintro rfl
    apply Subtype.ext
    apply Equiv.ext
    intro z
    cases z using OnePoint.rec with
    | infty => exact mobiusTranslation_infty 0
    | coe z =>
      change (mobiusTranslation 0 : Equiv.Perm Mobius.ExtendedComplex) z = (z : Mobius.ExtendedComplex)
      simpa only [add_zero] using mobiusTranslation_coe 0 z

/-- Nonzero translations are exactly the parabolic translations in the genuine boundary definition. -/
theorem mobiusTranslation_parabolic_iff (b : ℂ) :
    Mobius.MobiusBoundaryParabolic (mobiusTranslation b) ↔ b ≠ 0 := by
  constructor
  · intro hp
    exact (mobiusTranslation_eq_one_iff b).not.mp hp.1
  · intro hb
    refine ⟨(mobiusTranslation_eq_one_iff b).not.mpr hb, ∞, ?_⟩
    intro z
    cases z using OnePoint.rec with
    | infty => simp only [mobiusTranslation_infty]
    | coe z => simp [mobiusTranslation_coe, hb]

/-- Multiplier one separates precisely the parabolic and identity cases. -/
theorem mobiusMultiplier_eq_one_iff_parabolic_or_identity (f : Mobius.mobiusInftyStabilizer) :
    Mobius.mobiusMultiplier f = 1 ↔ Mobius.MobiusBoundaryParabolic f.1 ∨ f.1 = 1 := by
  constructor
  · intro hm
    obtain ⟨b, hb⟩ := (mobiusMultiplier_eq_one_iff_translation f).mp hm
    by_cases hb0 : b = 0
    · right
      exact hb.trans ((mobiusTranslation_eq_one_iff b).mpr hb0)
    · left
      rw [hb]
      exact (mobiusTranslation_parabolic_iff b).mpr hb0
  · rintro (hp | hf)
    · obtain ⟨_, a, ha⟩ := hp
      have hinfty : (∞ : Mobius.ExtendedComplex) = a := (ha ∞).mp f.2
      by_contra hm
      have hmul : (Mobius.mobiusMultiplier f : ℂ) ≠ 1 := by
        intro h
        exact hm (Units.ext h)
      have hd : 1 - (Mobius.mobiusMultiplier f : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hmul)
      let z : ℂ := Mobius.mobiusAffineConstant f / (1 - (Mobius.mobiusMultiplier f : ℂ))
      have hfix : (f.1 : Equiv.Perm Mobius.ExtendedComplex) z = z := by
        rw [Mobius.mobius_affine_formula]
        congr 1
        dsimp [z]
        field_simp [hd]
        ring
      exact (OnePoint.coe_ne_infty z) (((ha z).mp hfix).trans hinfty.symm)
    · have hf' : f = 1 := Subtype.ext hf
      simpa only [hf'] using Mobius.mobius_affine_parameters_one.1

/-- The translation subgroup is defined by actual translation maps. -/
def mobiusTranslationSubgroup : Subgroup Mobius.mobiusInftyStabilizer where
  carrier := {f | ∃ b : ℂ, f.1 = mobiusTranslation b}
  one_mem' := (mobiusMultiplier_eq_one_iff_translation 1).mp Mobius.mobius_affine_parameters_one.1
  mul_mem' {f g} hf hg := (mobiusMultiplier_eq_one_iff_translation (f * g)).mp (by
    rw [(Mobius.mobius_affine_parameters_mul f g).1,
      (mobiusMultiplier_eq_one_iff_translation f).mpr hf,
      (mobiusMultiplier_eq_one_iff_translation g).mpr hg, one_mul])
  inv_mem' {f} hf := (mobiusMultiplier_eq_one_iff_translation f⁻¹).mp (by
    change Mobius.mobiusMultiplierHom f⁻¹ = 1
    rw [map_inv]
    change (Mobius.mobiusMultiplier f)⁻¹ = 1
    rw [(mobiusMultiplier_eq_one_iff_translation f).mpr hf, inv_one])

/-- The multiplier kernel is exactly the independently specified translation subgroup. -/
theorem mobiusMultiplier_kernel_eq_translations :
    Mobius.mobiusMultiplierHom.ker = mobiusTranslationSubgroup := by
  ext f
  exact mobiusMultiplier_eq_one_iff_translation f

instance mobiusTranslationSubgroup_normal : mobiusTranslationSubgroup.Normal := by
  rw [← mobiusMultiplier_kernel_eq_translations]
  infer_instance

/-- The full stabilizer modulo translations is its actual multiplier range. -/
def mobiusQuotientTranslationsEquivMultiplierRange :
    (Mobius.mobiusInftyStabilizer ⧸ mobiusTranslationSubgroup) ≃* mobiusMultiplierRange := by
  exact (QuotientGroup.quotientMulEquivOfEq
    mobiusMultiplier_kernel_eq_translations.symm).trans
      (QuotientGroup.quotientKerEquivRange Mobius.mobiusMultiplierHom)



/-- Translations in the subgroup are specified by their actual geometric action. -/
def subgroupTranslations (G : Subgroup Mobius.complexMobiusGroup) (hG : G ≤ Mobius.mobiusInftyStabilizer) :
    Subgroup G := mobiusTranslationSubgroup.comap (Subgroup.inclusion hG)

/-- The restricted multiplier kernel consists precisely of translations in the group. -/
theorem subgroupMultiplier_kernel_eq_translations
    (G : Subgroup Mobius.complexMobiusGroup) (hG : G ≤ Mobius.mobiusInftyStabilizer) :
    (Mobius.subgroupMultiplierHom G hG).ker = subgroupTranslations G hG := by
  rw [subgroupTranslations, ← mobiusMultiplier_kernel_eq_translations]
  rfl

/-- Membership in the translation subgroup is equality to an actual translation. -/
theorem mem_subgroupTranslations_iff (G : Subgroup Mobius.complexMobiusGroup)
    (hG : G ≤ Mobius.mobiusInftyStabilizer) (f : G) :
    f ∈ subgroupTranslations G hG ↔ ∃ b : ℂ, f.1 = mobiusTranslation b := Iff.rfl

instance subgroupTranslations_normal (G : Subgroup Mobius.complexMobiusGroup)
    (hG : G ≤ Mobius.mobiusInftyStabilizer) : (subgroupTranslations G hG).Normal := by
  rw [← subgroupMultiplier_kernel_eq_translations]
  infer_instance

/-- The quotient by translations is canonically the multiplier subgroup. -/
def subgroupQuotientTranslationsEquivMultiplierRange
    (G : Subgroup Mobius.complexMobiusGroup) (hG : G ≤ Mobius.mobiusInftyStabilizer) :
    (G ⧸ subgroupTranslations G hG) ≃* Mobius.subgroupMultiplierRange G hG := by
  exact (QuotientGroup.quotientMulEquivOfEq
    (subgroupMultiplier_kernel_eq_translations G hG).symm).trans
      (QuotientGroup.quotientKerEquivRange (Mobius.subgroupMultiplierHom G hG))

/-- The unit-modulus complex units form a multiplicative subgroup. -/
def unitModulusComplexUnits : Subgroup ℂˣ where
  carrier := {a | ‖(a : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change ‖(a : ℂ)‖ = 1 at ha
    change ‖(b : ℂ)‖ = 1 at hb
    change ‖((a * b : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, ha, hb, one_mul]
  inv_mem' {a} ha := by
    change ‖(a : ℂ)‖ = 1 at ha
    change ‖((a⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, ha, inv_one]

/-- For a group of affine Euclidean isometries the multiplier range lies on the unit circle. -/
theorem subgroupMultiplierRange_le_unitModulus (G : Subgroup Mobius.complexMobiusGroup)
    (hG : G ≤ Mobius.mobiusInftyStabilizer)
    (hunit : ∀ f : G, ‖((Mobius.subgroupMultiplierHom G hG f : ℂˣ) : ℂ)‖ = 1) :
    Mobius.subgroupMultiplierRange G hG ≤ unitModulusComplexUnits := by
  rintro a ⟨f, rfl⟩
  change ‖((Mobius.subgroupMultiplierHom G hG f : ℂˣ) : ℂ)‖ = 1
  exact hunit f



/-- Every actual nonidentity Mobius transformation has a boundary fixed point. -/
theorem mobius_nonidentity_boundary_fixed_exists (f : Mobius.complexMobiusGroup) (hf : f ≠ 1) :
    ∃ z : Mobius.ExtendedComplex, (f : Equiv.Perm Mobius.ExtendedComplex) z = z := by
  rcases Mobius.mobius_nonidentity_fixedPoint_dichotomy f hf with ⟨a, ha⟩ | ⟨a, b, _, ha⟩
  · exact ⟨a, (ha a).mpr rfl⟩
  · exact ⟨a, (ha a).mpr (Or.inl rfl)⟩

/-- Any subgroup commuting with one nonidentity actual Mobius map has a finite boundary orbit. -/
theorem mobiusBoundaryFiniteOrbit_of_commuting_nonidentity
    (H : Subgroup Mobius.complexMobiusGroup) (f : Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (hcomm : ∀ g : H, Commute f (g : Mobius.complexMobiusGroup)) :
    MobiusBoundaryFiniteOrbit H := by
  obtain ⟨z, hz⟩ := mobius_nonidentity_boundary_fixed_exists f hf
  refine ⟨z, (mobius_boundary_fixedPoints_finite f hf).subset ?_⟩
  rintro w ⟨g, rfl⟩
  change f • ((g : Mobius.complexMobiusGroup) • z) = (g : Mobius.complexMobiusGroup) • z
  rw [← mul_smul, (hcomm g).eq, mul_smul]
  exact congrArg (fun w => (g : Mobius.complexMobiusGroup) • w) hz

/-- This criterion gives a finite orbit for the genuine closed-hyperbolic-space action. -/
theorem isElementary_of_commuting_nonidentity (H : Subgroup Mobius.complexMobiusGroup)
    (f : Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (hcomm : ∀ g : H, Commute f (g : Mobius.complexMobiusGroup)) : IsElementary H :=
  (isElementary_iff_boundary_or_interior H).mpr
    (Or.inl (mobiusBoundaryFiniteOrbit_of_commuting_nonidentity H f hf hcomm))

/-- The centralizer of any nonidentity actual Mobius map is elementary. -/
theorem isElementary_centralizer_nonidentity (f : Mobius.complexMobiusGroup) (hf : f ≠ 1) :
    IsElementary (Subgroup.centralizer ({f} : Set Mobius.complexMobiusGroup)) := by
  apply isElementary_of_commuting_nonidentity _ f hf
  intro g
  exact (Subgroup.mem_centralizer_iff.mp g.property) f (Set.mem_singleton f)

/-- Every abelian subgroup has a finite boundary orbit, including groups of elliptic elements. -/
theorem mobiusBoundaryFiniteOrbit_of_abelian (H : Subgroup Mobius.complexMobiusGroup)
    (hH : ∀ f g : H, Commute f g) : MobiusBoundaryFiniteOrbit H := by
  classical
  by_cases htriv : ∀ f : H, f = 1
  · apply mobiusBoundaryFiniteOrbit_of_fixed H ∞
    intro f
    rw [htriv f, one_smul]
  · obtain ⟨f, hf⟩ := not_forall.mp htriv
    apply mobiusBoundaryFiniteOrbit_of_commuting_nonidentity H (f : Mobius.complexMobiusGroup)
      (fun he => hf (Subtype.ext he))
    intro g
    change (f : Mobius.complexMobiusGroup) * (g : Mobius.complexMobiusGroup) =
      (g : Mobius.complexMobiusGroup) * (f : Mobius.complexMobiusGroup)
    exact congrArg Subtype.val (hH f g).eq

/-- Every abelian subgroup is elementary for the actual closed-space action. -/
theorem isElementary_of_abelian (H : Subgroup Mobius.complexMobiusGroup)
    (hH : ∀ f g : H, Commute f g) : IsElementary H :=
  (isElementary_iff_boundary_or_interior H).mpr
    (Or.inl (mobiusBoundaryFiniteOrbit_of_abelian H hH))


/-- Nonidentity actual Mobius maps have at most two boundary fixed points, with no infinite-set convention. -/
theorem mobius_boundary_fixedPoints_encard_le_two (f : Mobius.complexMobiusGroup) (hf : f ≠ 1) :
    {z : Mobius.ExtendedComplex | (f : Equiv.Perm Mobius.ExtendedComplex) z = z}.encard ≤ 2 := by
  rcases Mobius.mobius_nonidentity_fixedPoint_dichotomy f hf with ⟨a, ha⟩ | ⟨a, b, hab, ha⟩
  · have heq : {z : Mobius.ExtendedComplex | (f : Equiv.Perm Mobius.ExtendedComplex) z = z} = {a} := by
      ext z
      exact ha z
    rw [heq, encard_singleton]
    norm_num
  · have heq : {z : Mobius.ExtendedComplex | (f : Equiv.Perm Mobius.ExtendedComplex) z = z} = {a, b} := by
      ext z
      exact ha z
    rw [heq, encard_pair hab]

/-- An actual Mobius subgroup with a finite invariant boundary set of size at least three is finite. -/
theorem mobius_finite_of_finite_invariant_boundary_set
    (H : Subgroup Mobius.complexMobiusGroup) (S : Set Mobius.ExtendedComplex) (hS : S.Finite)
    (hstable : ∀ g : H, MapsTo (g • ·) S S) (hcard : 2 < S.ncard) : Finite H := by
  apply DiscreteGroups.Action.finite_of_finite_invariant_set_fixed_encard_le_two _ S hS hstable hcard
  intro g hg
  exact mobius_boundary_fixedPoints_encard_le_two (g : Mobius.complexMobiusGroup)
    (fun he => hg (Subtype.ext he))

/-- In particular, three distinct points in a finite boundary orbit force the actual group to be finite. -/
theorem mobius_finite_of_finite_boundary_orbit (H : Subgroup Mobius.complexMobiusGroup)
    (z : Mobius.ExtendedComplex) (hz : (MulAction.orbit H z).Finite)
    (hcard : 2 < (MulAction.orbit H z).ncard) : Finite H :=
  mobius_finite_of_finite_invariant_boundary_set H (MulAction.orbit H z) hz
    (fun g => MulAction.mapsTo_smul_orbit g z) hcard

/-- Every finite boundary orbit of an infinite actual group has size at most two. -/
theorem mobius_infinite_finite_boundary_orbit_ncard_le_two
    (H : Subgroup Mobius.complexMobiusGroup) [Infinite H] (z : Mobius.ExtendedComplex)
    (hz : (MulAction.orbit H z).Finite) : (MulAction.orbit H z).ncard ≤ 2 := by
  apply DiscreteGroups.Action.infinite_finite_orbit_ncard_le_two _ z hz
  intro g hg
  exact mobius_boundary_fixedPoints_encard_le_two (g : Mobius.complexMobiusGroup)
    (fun he => hg (Subtype.ext he))

/-- The exact singleton-or-two-point-orbit alternatives for an infinite actual group. -/
theorem mobius_infinite_finite_boundary_orbit_dichotomy
    (H : Subgroup Mobius.complexMobiusGroup) [Infinite H] (z : Mobius.ExtendedComplex)
    (hz : (MulAction.orbit H z).Finite) :
    (MulAction.orbit H z = {z} ∧ ∀ g : H, g • z = z) ∨
      ∃ a b : Mobius.ExtendedComplex, a ≠ b ∧ MulAction.orbit H z = {a, b} ∧
        ∀ g : H, (g.1 : Equiv.Perm Mobius.ExtendedComplex) '' {a, b} = {a, b} :=
  DiscreteGroups.Action.finite_orbit_singleton_or_pair z hz
    (mobius_infinite_finite_boundary_orbit_ncard_le_two H z hz)

/-- A two-point invariant boundary set supplies an actual finite boundary orbit. -/
theorem mobiusBoundaryFiniteOrbit_of_invariant_pair (H : Subgroup Mobius.complexMobiusGroup)
    (a b : Mobius.ExtendedComplex)
    (hpair : ∀ g : H, (g.1 : Equiv.Perm Mobius.ExtendedComplex) '' {a, b} = {a, b}) :
    MobiusBoundaryFiniteOrbit H := by
  refine ⟨a, ((Set.finite_singleton b).insert a).subset ?_⟩
  rintro z ⟨g, rfl⟩
  rw [← hpair g]
  exact Set.mem_image_of_mem _ (by simp)

/-- A preserved boundary pair is sufficient for genuine closed-space elementarity. -/
theorem isElementary_of_invariant_pair (H : Subgroup Mobius.complexMobiusGroup)
    (a b : Mobius.ExtendedComplex)
    (hpair : ∀ g : H, (g.1 : Equiv.Perm Mobius.ExtendedComplex) '' {a, b} = {a, b}) :
    IsElementary H :=
  (isElementary_iff_boundary_or_interior H).mpr
    (Or.inl (mobiusBoundaryFiniteOrbit_of_invariant_pair H a b hpair))

/-- Finite boundary orbits in an infinite group are equivalent to a common fixed point or invariant pair. -/
theorem mobius_infinite_boundaryFiniteOrbit_iff_fixed_or_pair
    (H : Subgroup Mobius.complexMobiusGroup) [Infinite H] :
    MobiusBoundaryFiniteOrbit H ↔
      (∃ z : Mobius.ExtendedComplex, ∀ g : H, g • z = z) ∨
      ∃ a b : Mobius.ExtendedComplex, a ≠ b ∧
        ∀ g : H, (g.1 : Equiv.Perm Mobius.ExtendedComplex) '' {a, b} = {a, b} := by
  constructor
  · rintro ⟨z, hz⟩
    rcases mobius_infinite_finite_boundary_orbit_dichotomy H z hz with
      ⟨_, hfix⟩ | ⟨a, b, hab, _, hpair⟩
    · exact Or.inl ⟨z, hfix⟩
    · exact Or.inr ⟨a, b, hab, hpair⟩
  · rintro (⟨z, hfix⟩ | ⟨a, b, _, hpair⟩)
    · exact mobiusBoundaryFiniteOrbit_of_fixed H z hfix
    · exact mobiusBoundaryFiniteOrbit_of_invariant_pair H a b hpair

/-- The actual interior branch is retained when expressing infinite-group elementarity. -/
theorem infinite_isElementary_iff_interior_or_fixed_or_pair
    (H : Subgroup Mobius.complexMobiusGroup) [Infinite H] :
    IsElementary H ↔ DiscreteGroups.Action.HasFiniteOrbit H Hyperbolic.QuaternionHalfSpace.UpperHalfSpace ∨
      (∃ z : Mobius.ExtendedComplex, ∀ g : H, g • z = z) ∨
      ∃ a b : Mobius.ExtendedComplex, a ≠ b ∧
        ∀ g : H, (g.1 : Equiv.Perm Mobius.ExtendedComplex) '' {a, b} = {a, b} := by
  rw [isElementary_iff_boundary_or_interior,
    mobius_infinite_boundaryFiniteOrbit_iff_fixed_or_pair]
  constructor
  · rintro ((hfix | hpair) | hint)
    · exact Or.inr (Or.inl hfix)
    · exact Or.inr (Or.inr hpair)
    · exact Or.inl hint
  · rintro (hint | hfix | hpair)
    · exact Or.inr hint
    · exact Or.inl (Or.inl hfix)
    · exact Or.inl (Or.inr hpair)


/-- An actual geometric Mobius transformation sends any prescribed boundary point to infinity. -/
theorem mobius_exists_send_to_infty (z : Mobius.ExtendedComplex) :
    ∃ q : Mobius.complexMobiusGroup, (q : Equiv.Perm Mobius.ExtendedComplex) z = ∞ := by
  obtain ⟨q, hq⟩ := Mobius.Classification.exists_send_to_infty z
  refine ⟨Mobius.complexMobiusEquivFractionalLinear.symm q, ?_⟩
  rw [Mobius.complexMobiusEquivFractionalLinear_symm_apply]
  exact hq

/-- Two distinct actual boundary points can be sent simultaneously to zero and infinity. -/
theorem mobius_exists_send_pair_zero_infty (a b : Mobius.ExtendedComplex) (hab : a ≠ b) :
    ∃ q : Mobius.complexMobiusGroup, (q : Equiv.Perm Mobius.ExtendedComplex) a = (0 : ℂ) ∧
      (q : Equiv.Perm Mobius.ExtendedComplex) b = ∞ := by
  obtain ⟨q, hqb⟩ := mobius_exists_send_to_infty b
  have hqa : (q : Equiv.Perm Mobius.ExtendedComplex) a ≠ ∞ := by
    intro h
    exact hab ((q : Equiv.Perm Mobius.ExtendedComplex).injective (h.trans hqb.symm))
  obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hqa
  refine ⟨mobiusTranslation (-w) * q, ?_, ?_⟩
  · change (mobiusTranslation (-w) : Equiv.Perm Mobius.ExtendedComplex)
      ((q : Equiv.Perm Mobius.ExtendedComplex) a) = (0 : ℂ)
    rw [← hw, mobiusTranslation_coe]
    simp
  · change (mobiusTranslation (-w) : Equiv.Perm Mobius.ExtendedComplex)
      ((q : Equiv.Perm Mobius.ExtendedComplex) b) = ∞
    rw [hqb, mobiusTranslation_infty]

/-- Actual conjugation carries a fixed point to its actual image. -/
theorem mobius_conjugate_fixedpoint (f q : Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex)
    (hz : (f : Equiv.Perm Mobius.ExtendedComplex) z = z) :
    ((q * f * q⁻¹ : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex)
      ((q : Equiv.Perm Mobius.ExtendedComplex) z) = (q : Equiv.Perm Mobius.ExtendedComplex) z := by
  change (q : Equiv.Perm Mobius.ExtendedComplex)
    ((f : Equiv.Perm Mobius.ExtendedComplex) ((q : Equiv.Perm Mobius.ExtendedComplex).symm
      ((q : Equiv.Perm Mobius.ExtendedComplex) z))) = (q : Equiv.Perm Mobius.ExtendedComplex) z
  rw [Equiv.symm_apply_apply, hz]

/-- Sending a common fixed point to infinity puts the entire conjugate subgroup in its stabilizer. -/
theorem mobius_subgroupConjugate_le_inftyStabilizer
    (H : Subgroup Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex)
    (hfix : ∀ g : H, g • z = z) (q : Mobius.complexMobiusGroup)
    (hq : (q : Equiv.Perm Mobius.ExtendedComplex) z = ∞) :
    DiscreteGroups.Action.Actions.subgroupConjugate q H ≤ Mobius.mobiusInftyStabilizer := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f).mp hf
  change ((q * g * q⁻¹ : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) ∞ = ∞
  rw [← hq]
  exact mobius_conjugate_fixedpoint g q z (hfix ⟨g, hg⟩)

/-- The common-fixed-point condition has actual affine coordinates for the whole subgroup. -/
theorem mobius_common_fixed_conjugate_inftyStabilizer
    (H : Subgroup Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex) (hfix : ∀ g : H, g • z = z) :
    ∃ q : Mobius.complexMobiusGroup, DiscreteGroups.Action.Actions.subgroupConjugate q H ≤
      Mobius.mobiusInftyStabilizer := by
  obtain ⟨q, hq⟩ := mobius_exists_send_to_infty z
  exact ⟨q, mobius_subgroupConjugate_le_inftyStabilizer H z hfix q hq⟩

/-- Actual subgroup conjugation transports an invariant boundary set by the same map. -/
theorem mobius_subgroupConjugate_preserves_image (H : Subgroup Mobius.complexMobiusGroup)
    (S : Set Mobius.ExtendedComplex)
    (hS : ∀ g : H, (g.1 : Equiv.Perm Mobius.ExtendedComplex) '' S = S) (q : Mobius.complexMobiusGroup) :
    ∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate q H,
      (f : Equiv.Perm Mobius.ExtendedComplex) '' ((q : Equiv.Perm Mobius.ExtendedComplex) '' S) =
        (q : Equiv.Perm Mobius.ExtendedComplex) '' S := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f).mp hf
  calc
    ((q * g * q⁻¹ : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) '' ((q : Equiv.Perm
      Mobius.ExtendedComplex) '' S) =
        (q : Equiv.Perm Mobius.ExtendedComplex) '' ((g : Equiv.Perm Mobius.ExtendedComplex) '' S) := by
      simp only [Set.image_image]
      congr 1
      funext z
      change (q : Equiv.Perm Mobius.ExtendedComplex)
        ((g : Equiv.Perm Mobius.ExtendedComplex) ((q : Equiv.Perm Mobius.ExtendedComplex).symm
          ((q : Equiv.Perm Mobius.ExtendedComplex) z))) =
        (q : Equiv.Perm Mobius.ExtendedComplex) ((g : Equiv.Perm Mobius.ExtendedComplex) z)
      rw [Equiv.symm_apply_apply]
    _ = (q : Equiv.Perm Mobius.ExtendedComplex) '' S := by rw [hS ⟨g, hg⟩]

/-- The set stabilizer of zero and infinity in the actual geometric Mobius group. -/
def mobiusZeroInftyPairStabilizer : Subgroup Mobius.complexMobiusGroup where
  carrier := {f | (f : Equiv.Perm Mobius.ExtendedComplex) '' ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set
    Mobius.ExtendedComplex) = ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex)}
  one_mem' := by
    change (id : Mobius.ExtendedComplex → Mobius.ExtendedComplex) '' ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} :
      Set Mobius.ExtendedComplex) = _
    rw [Set.image_id]
  mul_mem' {f g} hf hg := by
    change ((f * g : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) '' ({((0 : ℂ) :
      Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex) = _
    calc
      ((f * g : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) '' ({((0 : ℂ) :
        Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex) =
          (f : Equiv.Perm Mobius.ExtendedComplex) ''
            ((g : Equiv.Perm Mobius.ExtendedComplex) '' ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set
              Mobius.ExtendedComplex)) := by
        rw [Set.image_image]
        rfl
      _ = ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex) := by rw [hg, hf]
  inv_mem' {f} hf := by
    change ((f⁻¹ : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) '' ({((0 : ℂ) :
      Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex) = _
    calc
      ((f⁻¹ : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) '' ({((0 : ℂ) :
        Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex) =
          ((f⁻¹ : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) '' ((f : Equiv.Perm
            Mobius.ExtendedComplex) '' ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex)) :=
        by rw [hf]
      _ = ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex) := by
        rw [Set.image_image]
        change (fun z : Mobius.ExtendedComplex => (f : Equiv.Perm Mobius.ExtendedComplex).symm
          ((f : Equiv.Perm Mobius.ExtendedComplex) z)) '' _ = _
        simp only [Equiv.symm_apply_apply, Set.image_id']

/-- A conjugating map that normalizes the endpoints normalizes their full actual set stabilizer. -/
theorem mobius_subgroupConjugate_le_zeroInftyPairStabilizer
    (H : Subgroup Mobius.complexMobiusGroup) (a b : Mobius.ExtendedComplex)
    (hpair : ∀ g : H, (g.1 : Equiv.Perm Mobius.ExtendedComplex) '' {a, b} = {a, b})
    (q : Mobius.complexMobiusGroup) (hqa : (q : Equiv.Perm Mobius.ExtendedComplex) a = (0 : ℂ))
    (hqb : (q : Equiv.Perm Mobius.ExtendedComplex) b = ∞) :
    DiscreteGroups.Action.Actions.subgroupConjugate q H ≤ mobiusZeroInftyPairStabilizer := by
  intro f hf
  have h := mobius_subgroupConjugate_preserves_image H {a, b} hpair q f hf
  have hqpair : (q : Equiv.Perm Mobius.ExtendedComplex) '' {a, b} = ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set
    Mobius.ExtendedComplex) := by
    rw [Set.image_pair, hqa, hqb]
  change (f : Equiv.Perm Mobius.ExtendedComplex) '' ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set
    Mobius.ExtendedComplex) = ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex)
  simpa only [hqpair] using h

/-- Every actual subgroup preserving a pair of distinct boundary points has the zero-infinity coordinates. -/
theorem mobius_invariant_pair_conjugate_zeroInftyPairStabilizer
    (H : Subgroup Mobius.complexMobiusGroup) (a b : Mobius.ExtendedComplex) (hab : a ≠ b)
    (hpair : ∀ g : H, (g.1 : Equiv.Perm Mobius.ExtendedComplex) '' {a, b} = {a, b}) :
    ∃ q : Mobius.complexMobiusGroup,
      DiscreteGroups.Action.Actions.subgroupConjugate q H ≤ mobiusZeroInftyPairStabilizer := by
  obtain ⟨q, hqa, hqb⟩ := mobius_exists_send_pair_zero_infty a b hab
  exact ⟨q, mobius_subgroupConjugate_le_zeroInftyPairStabilizer H a b hpair q hqa hqb⟩





theorem mobiusScaling_zero (a : ℂˣ) :
    (Mobius.mobiusScaling a : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ) = (0 : ℂ) := by
  simpa only [mul_zero] using Mobius.mobiusScaling_coe a 0

/-- Reciprocal as an actual orientation-preserving geometric Mobius map. -/
def mobiusReciprocal : Mobius.complexMobiusGroup :=
  Mobius.mobiusMatrixProjection (Mobius.coefficientMatrix 0 1 1 0 (by norm_num))

theorem mobiusReciprocal_perm : (mobiusReciprocal : Equiv.Perm Mobius.ExtendedComplex) = Mobius.reciprocal := by
  rw [mobiusReciprocal, Mobius.mobiusMatrixProjection_coe]
  rfl

theorem mobiusReciprocal_zero :
    (mobiusReciprocal : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ) = ∞ := by
  rw [mobiusReciprocal_perm, Mobius.reciprocal_zero]

theorem mobiusReciprocal_infty :
    (mobiusReciprocal : Equiv.Perm Mobius.ExtendedComplex) ∞ = (0 : ℂ) := by
  rw [mobiusReciprocal_perm, Mobius.reciprocal_infty]

theorem mobiusReciprocal_coe (z : ℂ) (hz : z ≠ 0) :
    (mobiusReciprocal : Equiv.Perm Mobius.ExtendedComplex) z = (z⁻¹ : ℂ) := by
  rw [mobiusReciprocal_perm, Mobius.reciprocal_coe z hz]

/-- Squaring the actual reciprocal gives the identity. -/
theorem mobiusReciprocal_mul_self : mobiusReciprocal * mobiusReciprocal = 1 := by
  let A : Mobius.FractionalLinearMatrix := Mobius.coefficientMatrix 0 1 1 0 (by norm_num)
  have hA : A * A = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Mobius.coefficientMatrix, Matrix.mul_apply]
  change Mobius.mobiusMatrixProjection A * Mobius.mobiusMatrixProjection A = 1
  rw [← map_mul, hA, map_one]


/-- A bijection preserving the two endpoints either fixes them individually or interchanges them. -/
theorem mobius_zeroInftyPair_cases (f : mobiusZeroInftyPairStabilizer) :
    ((f.1 : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ) = (0 : ℂ) ∧
      (f.1 : Equiv.Perm Mobius.ExtendedComplex) ∞ = ∞) ∨
    ((f.1 : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ) = ∞ ∧
      (f.1 : Equiv.Perm Mobius.ExtendedComplex) ∞ = (0 : ℂ)) := by
  have hzero : (f.1 : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ) ∈
      ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex) := by
    rw [← f.property]
    exact Set.mem_image_of_mem _ (by simp)
  have hinfty : (f.1 : Equiv.Perm Mobius.ExtendedComplex) ∞ ∈
      ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex) := by
    rw [← f.property]
    exact Set.mem_image_of_mem _ (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzero hinfty
  by_cases hfix : (f.1 : Equiv.Perm Mobius.ExtendedComplex) ∞ = ∞
  · left
    refine ⟨?_, hfix⟩
    rcases hzero with hz | hz
    · exact hz
    · exact False.elim ((OnePoint.coe_ne_infty (0 : ℂ))
        ((f.1 : Equiv.Perm Mobius.ExtendedComplex).injective (hz.trans hfix.symm)))
  · right
    have hi : (f.1 : Equiv.Perm Mobius.ExtendedComplex) ∞ = (0 : ℂ) := hinfty.resolve_right hfix
    refine ⟨?_, hi⟩
    rcases hzero with hz | hz
    · exact False.elim ((OnePoint.coe_ne_infty (0 : ℂ))
        ((f.1 : Equiv.Perm Mobius.ExtendedComplex).injective (hz.trans hi.symm)))
    · exact hz

/-- Every actual endpoint-pair stabilizer element is multiplication or multiplication after reciprocal. -/
theorem mobius_zeroInftyPair_normal_form (f : mobiusZeroInftyPairStabilizer) :
    ∃ a : ℂˣ, f.1 = Mobius.mobiusScaling a ∨ f.1 = Mobius.mobiusScaling a * mobiusReciprocal := by
  rcases mobius_zeroInftyPair_cases f with ⟨hzero, hinfty⟩ | ⟨hzero, hinfty⟩
  · obtain ⟨a, ha⟩ := Mobius.mobius_fix_zero_infty_eq_scaling f.1 hzero hinfty
    exact ⟨a, Or.inl ha⟩
  · have hzero' : ((f.1 * mobiusReciprocal : Mobius.complexMobiusGroup) :
        Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ) = (0 : ℂ) := by
      change (f.1 : Equiv.Perm Mobius.ExtendedComplex)
        ((mobiusReciprocal : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ)) = (0 : ℂ)
      rw [mobiusReciprocal_zero, hinfty]
    have hinfty' : ((f.1 * mobiusReciprocal : Mobius.complexMobiusGroup) :
        Equiv.Perm Mobius.ExtendedComplex) ∞ = ∞ := by
      change (f.1 : Equiv.Perm Mobius.ExtendedComplex)
        ((mobiusReciprocal : Equiv.Perm Mobius.ExtendedComplex) ∞) = ∞
      rw [mobiusReciprocal_infty, hzero]
    obtain ⟨a, ha⟩ := Mobius.mobius_fix_zero_infty_eq_scaling _ hzero' hinfty'
    refine ⟨a, Or.inr ?_⟩
    calc
      f.1 = (f.1 * mobiusReciprocal) * mobiusReciprocal := by
        rw [mul_assoc, mobiusReciprocal_mul_self, mul_one]
      _ = Mobius.mobiusScaling a * mobiusReciprocal := by rw [ha]

/-- Every scaling preserves the endpoint pair. -/
theorem mobiusScaling_mem_zeroInftyPairStabilizer (a : ℂˣ) :
    Mobius.mobiusScaling a ∈ mobiusZeroInftyPairStabilizer := by
  change (Mobius.mobiusScaling a : Equiv.Perm Mobius.ExtendedComplex) ''
    ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex) = ({((0 : ℂ) : Mobius.ExtendedComplex),
      ∞} : Set Mobius.ExtendedComplex)
  rw [Set.image_pair, mobiusScaling_zero, Mobius.mobiusScaling_infty]

/-- Reciprocal preserves the endpoint pair by interchanging its members. -/
theorem mobiusReciprocal_mem_zeroInftyPairStabilizer :
    mobiusReciprocal ∈ mobiusZeroInftyPairStabilizer := by
  change (mobiusReciprocal : Equiv.Perm Mobius.ExtendedComplex) ''
    ({((0 : ℂ) : Mobius.ExtendedComplex), ∞} : Set Mobius.ExtendedComplex) = ({((0 : ℂ) : Mobius.ExtendedComplex),
      ∞} : Set Mobius.ExtendedComplex)
  rw [Set.image_pair, mobiusReciprocal_zero, mobiusReciprocal_infty, Set.pair_comm]

/-- The two actual families characterize the full endpoint-pair stabilizer. -/
theorem mem_zeroInftyPairStabilizer_iff_normal_form (f : Mobius.complexMobiusGroup) :
    f ∈ mobiusZeroInftyPairStabilizer ↔
      ∃ a : ℂˣ, f = Mobius.mobiusScaling a ∨ f = Mobius.mobiusScaling a * mobiusReciprocal := by
  constructor
  · intro hf
    exact mobius_zeroInftyPair_normal_form ⟨f, hf⟩
  · rintro ⟨a, rfl | rfl⟩
    · exact mobiusScaling_mem_zeroInftyPairStabilizer a
    · exact mobiusZeroInftyPairStabilizer.mul_mem
        (mobiusScaling_mem_zeroInftyPairStabilizer a) mobiusReciprocal_mem_zeroInftyPairStabilizer

/-- The reciprocal branch has the expected finite formula away from its pole. -/
theorem mobiusScaling_mul_reciprocal_coe (a : ℂˣ) (z : ℂ) (hz : z ≠ 0) :
    ((Mobius.mobiusScaling a * mobiusReciprocal : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) z =
      ((a : ℂ) / z : ℂ) := by
  change (Mobius.mobiusScaling a : Equiv.Perm Mobius.ExtendedComplex)
    ((mobiusReciprocal : Equiv.Perm Mobius.ExtendedComplex) z) = _
  rw [mobiusReciprocal_coe z hz, Mobius.mobiusScaling_coe, div_eq_mul_inv]

/-- The geometric exponent notation holds for every actual endpoint-pair stabilizer element. -/
theorem mobius_zeroInftyPair_power_formula (f : mobiusZeroInftyPairStabilizer) :
    ∃ a : ℂˣ, ∃ s : ℤ, s ^ 2 = 1 ∧ ∀ z : ℂ, z ≠ 0 →
      (f.1 : Equiv.Perm Mobius.ExtendedComplex) z = ((a : ℂ) * z ^ s : ℂ) := by
  obtain ⟨a, ha | ha⟩ := mobius_zeroInftyPair_normal_form f
  · refine ⟨a, 1, by norm_num, fun z _ => ?_⟩
    rw [ha, Mobius.mobiusScaling_coe, zpow_one]
  · refine ⟨a, -1, by norm_num, fun z hz => ?_⟩
    rw [ha, mobiusScaling_mul_reciprocal_coe a z hz, zpow_neg_one, div_eq_mul_inv]


/-- The actual affine action has the Euclidean similarity distance scale of its multiplier. -/
theorem mobius_infty_stabilizer_finite_distance (f : Mobius.mobiusInftyStabilizer) (z w : ℂ) :
    dist (Mobius.finiteComplexPart (f.1 : Equiv.Perm Mobius.ExtendedComplex) z)
        (Mobius.finiteComplexPart (f.1 : Equiv.Perm Mobius.ExtendedComplex) w) =
      ‖(Mobius.mobiusMultiplier f : ℂ)‖ * dist z w := by
  rw [dist_eq_norm, dist_eq_norm]
  simp only [Mobius.finiteComplexPart, Mobius.mobius_affine_formula]
  change ‖((Mobius.mobiusMultiplier f : ℂ) * z + Mobius.mobiusAffineConstant f) -
      ((Mobius.mobiusMultiplier f : ℂ) * w + Mobius.mobiusAffineConstant f)‖ = _
  rw [show ((Mobius.mobiusMultiplier f : ℂ) * z + Mobius.mobiusAffineConstant f) -
      ((Mobius.mobiusMultiplier f : ℂ) * w + Mobius.mobiusAffineConstant f) =
      (Mobius.mobiusMultiplier f : ℂ) * (z - w) by ring, norm_mul]

/-- Common boundary fixed points give genuine affine representatives for every conjugated group element. -/
theorem mobius_common_fixed_conjugate_affine (H : Subgroup Mobius.complexMobiusGroup)
    (z : Mobius.ExtendedComplex) (hfix : ∀ g : H, g • z = z) :
    ∃ q : Mobius.complexMobiusGroup, ∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate q H,
      ∃ a : ℂˣ, ∃ b : ℂ, f = Mobius.mobiusMatrixProjection (Mobius.Classification.affineMatrix a b) := by
  obtain ⟨q, hq⟩ := mobius_common_fixed_conjugate_inftyStabilizer H z hfix
  refine ⟨q, fun f hf => ?_⟩
  exact Mobius.mobius_affine_of_fixes_infty f (hq hf)


/-- All elements of the conjugated actual group have the complete two-family endpoint normal form. -/
theorem mobius_invariant_pair_conjugate_normal_form
    (H : Subgroup Mobius.complexMobiusGroup) (a b : Mobius.ExtendedComplex) (hab : a ≠ b)
    (hpair : ∀ g : H, (g.1 : Equiv.Perm Mobius.ExtendedComplex) '' {a, b} = {a, b}) :
    ∃ q : Mobius.complexMobiusGroup, ∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate q H,
      ∃ u : ℂˣ, f = Mobius.mobiusScaling u ∨ f = Mobius.mobiusScaling u * mobiusReciprocal := by
  obtain ⟨q, hq⟩ := mobius_invariant_pair_conjugate_zeroInftyPairStabilizer H a b hab hpair
  exact ⟨q, fun f hf => mobius_zeroInftyPair_normal_form ⟨f, hq hf⟩⟩



def elementaryBoundaryNormal : Inversive.Euclidean 3 := EuclideanSpace.single 2 1

theorem elementaryBoundaryNormal_norm : ‖elementaryBoundaryNormal‖ = 1 := by
  simp [elementaryBoundaryNormal, EuclideanSpace.single, PiLp.norm_single]

theorem elementaryBoundaryNormal_ne_zero : elementaryBoundaryNormal ≠ 0 := by
  intro h
  have hh := elementaryBoundaryNormal_norm
  rw [h, norm_zero] at hh
  norm_num at hh

theorem inner_elementaryBoundaryNormal (x : Inversive.Euclidean 3) :
    inner ℝ x elementaryBoundaryNormal = x 2 := by
  simp [elementaryBoundaryNormal, EuclideanSpace.inner_single_right]

def elementaryBoundaryReflection : Inversive.ExtendedHomeomorph 3 :=
  Inversive.planeReflectionHomeomorph elementaryBoundaryNormal 0 elementaryBoundaryNormal_ne_zero

theorem elementaryBoundaryReflection_height (x : Inversive.Euclidean 3) :
    (Inversive.planeReflectionFinite elementaryBoundaryNormal 0 x) 2 = -x 2 := by
  simpa only [inner_elementaryBoundaryNormal, mul_zero, zero_sub] using
    Inversive.inner_planeReflectionFinite elementaryBoundaryNormal 0 elementaryBoundaryNormal_ne_zero x

theorem elementaryBoundaryPlane_eq : Inversive.plane elementaryBoundaryNormal 0 =
    (Hyperbolic.poincareHalfSpaceSet 2 1 ∪ Hyperbolic.poincareHalfSpaceSet 2 (-1))ᶜ := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [Inversive.plane, Hyperbolic.poincareHalfSpaceSet_infty]
  | coe x =>
      have hp : (x : Inversive.ExtendedEuclidean 3) ∈ Inversive.plane elementaryBoundaryNormal 0 ↔ x 2 = 0 := by
        constructor
        · rintro (hinfty | ⟨y, hy, he⟩)
          · exact (OnePoint.coe_ne_infty x hinfty).elim
          · have hyx := OnePoint.coe_injective he
            simpa only [hyx, inner_elementaryBoundaryNormal] using hy
        · intro hx
          exact Or.inr ⟨x, by simpa only [inner_elementaryBoundaryNormal] using hx, rfl⟩
      rw [hp]
      simp only [mem_compl_iff, mem_union, Hyperbolic.poincareHalfSpaceSet_coe, show (Fin.last 2 : Fin 3) = 2 from
        rfl, one_mul,
        neg_mul, one_mul, neg_pos]
      constructor
      · intro h; simp [h]
      · intro h; push Not at h; linarith

theorem preservesHalfSpaces_commutes_boundaryReflection
    (F : Inversive.ExtendedHomeomorph 3) (hF : F ∈ Inversive.generalMobiusGroup 3)
    (hhalf : Hyperbolic.PreservesPoincareHalfSpaces (n := 2) F) (z : Inversive.ExtendedEuclidean 3) :
    F (elementaryBoundaryReflection z) = elementaryBoundaryReflection (F z) := by
  apply reflection_commutes_of_invariant_sphere F elementaryBoundaryReflection hF
    (Inversive.planeReflection_isReflection _ _ elementaryBoundaryNormal_ne_zero)
  unfold elementaryBoundaryReflection
  rw [Inversive.fixedPoints_planeReflection, elementaryBoundaryPlane_eq, F.image_compl,
    Set.image_union, hhalf 1, hhalf (-1)]

/-- Reflect lower-half-space points upwards while retaining all boundary points and infinity. -/
def elementaryHalfSpaceFold (z : Inversive.ExtendedEuclidean 3) : Inversive.ExtendedEuclidean 3 := by
  classical
  exact if z ∈ Hyperbolic.poincareHalfSpaceSet 2 (-1) then elementaryBoundaryReflection z else z

theorem elementaryHalfSpaceFold_equivariant
    (F : Inversive.ExtendedHomeomorph 3) (hF : F ∈ Inversive.generalMobiusGroup 3)
    (hhalf : Hyperbolic.PreservesPoincareHalfSpaces (n := 2) F) (z : Inversive.ExtendedEuclidean 3) :
    elementaryHalfSpaceFold (F z) = F (elementaryHalfSpaceFold z) := by
  have hmem : F z ∈ Hyperbolic.poincareHalfSpaceSet 2 (-1) ↔ z ∈ Hyperbolic.poincareHalfSpaceSet 2 (-1) := by
    constructor
    · intro hz
      rw [← hhalf (-1)] at hz
      obtain ⟨w, hw, he⟩ := hz
      simpa only [F.injective he] using hw
    · intro hz
      rw [← hhalf (-1)]
      exact ⟨z, hz, rfl⟩
  classical
  unfold elementaryHalfSpaceFold
  rw [hmem]
  split_ifs
  · exact (preservesHalfSpaces_commutes_boundaryReflection F hF hhalf z).symm
  · rfl

theorem extendedEuclidean_nonneg_height_mem_closed {x : Inversive.Euclidean 3} (hx : 0 ≤ x 2) :
    Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (x : Inversive.ExtendedEuclidean 3) ∈
      closure Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet := by
  rcases hx.eq_or_lt with hx | hx
  · apply frontier_subset_closure
    rw [Hyperbolic.QuaternionHalfSpace.frontier_extendedUpperHalfSpaceSet]
    refine Or.inr ⟨Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x, ?_, rfl⟩
    change Hyperbolic.QuaternionHalfSpace.quaternionHeight
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x) = 0
    simpa only [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion_height] using hx.symm
  · apply subset_closure
    exact ⟨Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x, hx, rfl⟩

theorem elementaryHalfSpaceFold_mem_closed (z : Inversive.ExtendedEuclidean 3) :
    Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (elementaryHalfSpaceFold z) ∈
      closure Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet := by
  classical
  induction z using OnePoint.rec with
  | infty =>
      simpa [elementaryHalfSpaceFold, Hyperbolic.poincareHalfSpaceSet_infty,
        Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion] using
        Hyperbolic.QuaternionHalfSpace.infty_mem_closure_extendedUpperHalfSpaceSet
  | coe x =>
      by_cases hx : (x : Inversive.ExtendedEuclidean 3) ∈ Hyperbolic.poincareHalfSpaceSet 2 (-1)
      · rw [elementaryHalfSpaceFold, ite_eq_left hx]
        change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion
          (Inversive.planeReflection elementaryBoundaryNormal 0 x) ∈ _
        rw [Inversive.planeReflection_coe]
        apply extendedEuclidean_nonneg_height_mem_closed
        rw [elementaryBoundaryReflection_height]
        have hneg : x 2 < 0 :=
          by simpa only [Hyperbolic.poincareHalfSpaceSet_coe, show (Fin.last 2 : Fin 3) = 2 from rfl, neg_mul, one_mul,
          neg_pos] using hx
        exact neg_nonneg.mpr hneg.le
      · rw [elementaryHalfSpaceFold, ite_eq_right hx]
        apply extendedEuclidean_nonneg_height_mem_closed
        have hneg : ¬x 2 < 0 :=
          by simpa only [Hyperbolic.poincareHalfSpaceSet_coe, show (Fin.last 2 : Fin 3) = 2 from rfl, neg_mul,
          one_mul, neg_pos] using hx
        exact le_of_not_gt hneg

/-- The geometric full compactified three-space action is the actual native geometric extension. -/
instance mobiusCompactifiedSpaceMulAction : MulAction Mobius.complexMobiusGroup (Inversive.ExtendedEuclidean 3) where
  smul f z := (Mobius.mobiusGeometricPoincareHom f : Inversive.ExtendedHomeomorph 3) z
  one_smul z := by
    change ((Mobius.mobiusGeometricPoincareHom 1 : Inversive.GM 3) : Inversive.ExtendedHomeomorph 3) z = z
    rw [map_one]
    rfl
  mul_smul f g z := by
    change ((Mobius.mobiusGeometricPoincareHom (f * g) : Inversive.GM 3) : Inversive.ExtendedHomeomorph 3) z =
      (Mobius.mobiusGeometricPoincareHom f : Inversive.ExtendedHomeomorph 3)
        ((Mobius.mobiusGeometricPoincareHom g : Inversive.ExtendedHomeomorph 3) z)
    rw [map_mul]
    rfl

/-- Inclusion of the actual closed upper half-space in the full compactification. -/
def closedHalfSpaceToFull (q : ClosedUpperHalfSpace) : Inversive.ExtendedEuclidean 3 :=
  Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm q.val

theorem closedHalfSpaceToFull_equivariant (f : Mobius.complexMobiusGroup) (q : ClosedUpperHalfSpace) :
    closedHalfSpaceToFull (f • q) = f • closedHalfSpaceToFull q := by
  obtain ⟨q, rfl⟩ := closedUpperHalfSpaceSumEquiv.surjective q
  apply Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.injective
  cases q with
  | inl z =>
      simp only [closedHalfSpaceToFull,
        Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.apply_symm_apply,
        closed_smul_boundary, closedUpperHalfSpaceSumEquiv_inl]
      exact (Mobius.mobiusGeometricPoincare_boundary f z).symm
  | inr q =>
      simp only [closedHalfSpaceToFull,
        Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.apply_symm_apply,
        closed_smul_interior, closedUpperHalfSpaceSumEquiv_inr]
      exact (Mobius.mobiusGeometricPoincare_geometric f).2.2 q |>.symm

def fullSpaceToClosed (z : Inversive.ExtendedEuclidean 3) : ClosedUpperHalfSpace :=
  ⟨Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (elementaryHalfSpaceFold z),
    elementaryHalfSpaceFold_mem_closed z⟩

theorem fullSpaceToClosed_equivariant (f : Mobius.complexMobiusGroup) (z : Inversive.ExtendedEuclidean 3) :
    fullSpaceToClosed (f • z) = f • fullSpaceToClosed z := by
  have hi : Function.Injective closedHalfSpaceToFull :=
    Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm.injective.comp Subtype.val_injective
  apply hi
  rw [closedHalfSpaceToFull_equivariant]
  change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm
    (Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (elementaryHalfSpaceFold
      ((Mobius.mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3) z))) =
    (Mobius.mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3)
      (Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm
      (Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (elementaryHalfSpaceFold z)))
  simp only [Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm_apply_apply]
  exact elementaryHalfSpaceFold_equivariant _ (Mobius.mobiusGeometricPoincare f).property
    (Mobius.mobiusGeometricPoincare_preservesHalfSpaces f) z

/-- The full-space and closed-half-space finite-orbit definitions agree. -/
theorem isElementary_iff_compactified_finite_orbit (H : Subgroup Mobius.complexMobiusGroup) :
    IsElementary H ↔ DiscreteGroups.Action.HasFiniteOrbit H (Inversive.ExtendedEuclidean 3) := by
  constructor
  · exact DiscreteGroups.Action.hasFiniteOrbit_of_equivariant_map closedHalfSpaceToFull
      (fun f q => closedHalfSpaceToFull_equivariant f.val q)
  · exact DiscreteGroups.Action.hasFiniteOrbit_of_equivariant_map fullSpaceToClosed
      (fun f z => fullSpaceToClosed_equivariant f.val z)

theorem isElementary_of_compactified_fixed (H : Subgroup Mobius.complexMobiusGroup)
    (z : Inversive.ExtendedEuclidean 3) (hz : ∀ f : H, f • z = z) : IsElementary H :=
  (isElementary_iff_compactified_finite_orbit H).mpr (DiscreteGroups.Action.hasFiniteOrbit_of_fixed z hz)

theorem compactified_finite_orbit_positive_power (H : Subgroup Mobius.complexMobiusGroup)
    (z : Inversive.ExtendedEuclidean 3) (hz : (MulAction.orbit H z).Finite) (f : H) :
    ∃ k : ℕ, 0 < k ∧ ∀ w ∈ MulAction.orbit H z, (f ^ k) • w = w :=
  DiscreteGroups.Action.exists_positive_power_fixing_finite_orbit z hz f

/-- Type 2: a singleton orbit in the actual extended complex boundary. -/
def HasTypeTwoBoundaryOrbit (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  ∃ z : Mobius.ExtendedComplex, MulAction.orbit H z = {z}

/-- Type 3: a genuine two-point orbit in the actual extended complex boundary. -/
def HasTypeThreeBoundaryOrbit (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  ∃ z : Mobius.ExtendedComplex, (MulAction.orbit H z).Finite ∧ (MulAction.orbit H z).ncard = 2

theorem hasTypeTwoBoundaryOrbit_iff (H : Subgroup Mobius.complexMobiusGroup) :
    HasTypeTwoBoundaryOrbit H ↔ ∃ z : Mobius.ExtendedComplex, ∀ f : H, f • z = z := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun f => ?_⟩
    have hf := MulAction.mem_orbit z f
    rwa [hz, mem_singleton_iff] at hf
  · rintro ⟨z, hz⟩
    exact ⟨z, DiscreteGroups.Action.orbit_eq_singleton_of_fixed z hz⟩

theorem hasTypeThreeBoundaryOrbit_invariant_pair (H : Subgroup Mobius.complexMobiusGroup)
    (h : HasTypeThreeBoundaryOrbit H) :
    ∃ a b : Mobius.ExtendedComplex, a ≠ b ∧
      ∀ f : H, (f.val : Equiv.Perm Mobius.ExtendedComplex) '' {a, b} = {a, b} := by
  obtain ⟨z, _, hz⟩ := h
  obtain ⟨a, b, hab, heq⟩ := Set.ncard_eq_two.mp hz
  refine ⟨a, b, hab, fun f => ?_⟩
  change (fun x : Mobius.ExtendedComplex => f • x) '' {a, b} = {a, b}
  rw [← heq, Set.image_smul, MulAction.smul_orbit]

/-- The Type 2 coordinate classification is a genuine subgroup conjugacy to affine similarities. -/
theorem typeTwo_conjugate_affine (H : Subgroup Mobius.complexMobiusGroup)
    (h : HasTypeTwoBoundaryOrbit H) :
    ∃ q : Mobius.complexMobiusGroup, ∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate q H,
      ∃ a : ℂˣ, ∃ b : ℂ, f = Mobius.mobiusMatrixProjection (Mobius.Classification.affineMatrix a b) := by
  obtain ⟨z, hz⟩ := (hasTypeTwoBoundaryOrbit_iff H).mp h
  exact mobius_common_fixed_conjugate_affine H z hz

/-- The Type 3 classification keeps the full actual group element, including zero and infinity. -/
theorem typeThree_conjugate_normal_form (H : Subgroup Mobius.complexMobiusGroup)
    (h : HasTypeThreeBoundaryOrbit H) :
    ∃ q : Mobius.complexMobiusGroup, ∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate q H,
      ∃ a : ℂˣ, f = Mobius.mobiusScaling a ∨ f = Mobius.mobiusScaling a * mobiusReciprocal := by
  obtain ⟨a, b, hab, hp⟩ := hasTypeThreeBoundaryOrbit_invariant_pair H h
  exact mobius_invariant_pair_conjugate_normal_form H a b hab hp

section PuncturedMetric
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
open scoped Topology ContDiff ENNReal

/-- The actual punctured complex plane with its inherited Euclidean topology. -/
def puncturedPlaneDomain : TopologicalSpace.Opens ℂ where
  carrier := ({0} : Set ℂ)ᶜ
  is_open' := isClosed_singleton.isOpen_compl

abbrev PuncturedPlane := puncturedPlaneDomain

instance puncturedPlanePreconnected : PreconnectedSpace PuncturedPlane :=
  Subtype.preconnectedSpace (isConnected_compl_singleton_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ)).isPreconnected

def puncturedDensity : Auxiliary.Analysis.Density puncturedPlaneDomain where
  toFun z := 1 / ‖z.val‖
  positive z := one_div_pos.mpr (norm_pos_iff.mpr z.property)
  continuous := continuous_const.div continuous_subtype_val.norm
    (fun z => norm_ne_zero_iff.mpr z.property)

theorem puncturedDensity_apply (z : PuncturedPlane) : puncturedDensity z = 1 / ‖z.val‖ := rfl

@[instance_reducible]
def puncturedMetricSpace : MetricSpace PuncturedPlane := puncturedDensity.metricSpace

theorem puncturedPathDist_eq_length_inf (z w : PuncturedPlane) :
    puncturedDensity.pathDist z w = sInf (Set.range (fun c :
      Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, ℂ) PuncturedPlane z w => (puncturedDensity.chainLength c).toReal)) :=
  puncturedDensity.pathDist_eq_sInf_chain_lengths z w

def puncturedScaling (a : ℂˣ) : PuncturedPlane ≃ PuncturedPlane where
  toFun z := ⟨(a : ℂ) * z.val, mul_ne_zero a.ne_zero z.property⟩
  invFun z := ⟨((a⁻¹ : ℂˣ) : ℂ) * z.val, mul_ne_zero (a⁻¹).ne_zero z.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp

def puncturedReciprocal : PuncturedPlane ≃ PuncturedPlane where
  toFun z := ⟨z.val⁻¹, inv_ne_zero z.property⟩
  invFun z := ⟨z.val⁻¹, inv_ne_zero z.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp

/-- Open-domain charts retain an ambient formula on an actual neighbourhood. -/
theorem openDensity_chart_map_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D D' : TopologicalSpace.Opens E) (f : D → D') (g : E → E)
    (hfg : ∀ z : D, (f z).val = g z.val) (x : D) :
    writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) x f =ᶠ[𝓝 x.val] g := by
  have hh := (TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
    (H := E) D (x := x)).symm
  filter_upwards [hh] with y hy
  simp only [writtenInExtChartAt, TopologicalSpace.Opens.chartAt_eq, mfld_simps,
    Set.domRestrict, Function.comp_def]
  rw [hfg]
  exact congrArg g hy

/-- Ordinary differentiability of an ambient formula proves manifold differentiability. -/
theorem openDensity_mdifferentiable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D D' : TopologicalSpace.Opens E) (f : D → D') (g : E → E)
    (hfg : ∀ z : D, (f z).val = g z.val) (hf : Continuous f)
    (hg : ∀ x : D, DifferentiableAt ℝ g x.val) :
    MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) f := by
  intro x
  rw [mdifferentiableAt_iff]
  refine ⟨hf.continuousAt, ?_⟩
  have hd := (hg x).congr_of_eventuallyEq (openDensity_chart_map_eventuallyEq D D' f g hfg x)
  have hxchart : (chartAt E x) x = x.val := by simp [TopologicalSpace.Opens.chartAt_eq]
  simpa only [mfld_simps, hxchart] using hd.differentiableWithinAt (s := range 𝓘(ℝ, E))

/-- Ambient-coordinate derivatives give the actual tangent derivative on an open domain. -/
theorem openDensity_mfderiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D D' : TopologicalSpace.Opens E) (f : D → D') (g : E → E)
    (hfg : ∀ z : D, (f z).val = g z.val)
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) f)
    (x : D) (A : E →L[ℝ] E) (hg : HasFDerivAt g A x.val)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    (tangentSpaceCastModel 𝓘(ℝ, E) (f x))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) = A ((tangentSpaceCastModel 𝓘(ℝ, E) x) v) := by
  have heq := openDensity_chart_map_eventuallyEq D D' f g hfg x
  simp only [mfderiv, hf x, ite_true, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  have heq' : (chartAt E (f x) ∘ f ∘ (chartAt E x).symm) =ᶠ[𝓝 x.val] g := by
    simpa only [writtenInExtChartAt, mfld_simps] using heq
  simp only [mfld_simps, fderivWithin_univ]
  have hxchart : (chartAt E x) x = x.val := by simp [TopologicalSpace.Opens.chartAt_eq]
  rw [hxchart, heq'.fderiv_eq, hg.fderiv]

theorem puncturedScaling_mdifferentiable (a : ℂˣ) :
    MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (puncturedScaling a) := by
  apply openDensity_mdifferentiable puncturedPlaneDomain puncturedPlaneDomain
    (puncturedScaling a) (fun z : ℂ => (a : ℂ) * z) (fun _ => rfl)
  · exact (continuous_const.mul continuous_subtype_val).subtype_mk _
  · intro x
    exact (ContinuousLinearMap.mul ℝ ℂ (a : ℂ)).differentiableAt

theorem puncturedReciprocal_mdifferentiable :
    MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) puncturedReciprocal := by
  apply openDensity_mdifferentiable puncturedPlaneDomain puncturedPlaneDomain
    puncturedReciprocal (fun z : ℂ => z⁻¹) (fun _ => rfl)
  · exact (continuous_subtype_val.inv₀ (fun z : PuncturedPlane => z.property)).subtype_mk _
  · intro x
    exact (differentiableAt_inv x.property : DifferentiableAt ℂ Inv.inv x.val).restrictScalars ℝ

theorem puncturedScaling_covariance (a : ℂˣ) (x : PuncturedPlane)
    (v : TangentSpace 𝓘(ℝ, ℂ) x) :
    puncturedDensity (puncturedScaling a x) *
      ‖(tangentSpaceCastModel 𝓘(ℝ, ℂ) (puncturedScaling a x))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (puncturedScaling a) x v)‖ =
      puncturedDensity x * ‖(tangentSpaceCastModel 𝓘(ℝ, ℂ) x) v‖ := by
  rw [openDensity_mfderiv_apply puncturedPlaneDomain puncturedPlaneDomain
    (puncturedScaling a) (fun z : ℂ => (a : ℂ) * z) (fun _ => rfl)
    (puncturedScaling_mdifferentiable a) x (ContinuousLinearMap.mul ℝ ℂ (a : ℂ))
    (ContinuousLinearMap.mul ℝ ℂ (a : ℂ)).hasFDerivAt v]
  change (1 / ‖(a : ℂ) * x.val‖) * ‖(a : ℂ) * _‖ = (1 / ‖x.val‖) * ‖_‖
  rw [norm_mul, norm_mul]
  field_simp [norm_ne_zero_iff.mpr a.ne_zero, norm_ne_zero_iff.mpr x.property]

theorem puncturedReciprocal_covariance (x : PuncturedPlane)
    (v : TangentSpace 𝓘(ℝ, ℂ) x) :
    puncturedDensity (puncturedReciprocal x) *
      ‖(tangentSpaceCastModel 𝓘(ℝ, ℂ) (puncturedReciprocal x))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) puncturedReciprocal x v)‖ =
      puncturedDensity x * ‖(tangentSpaceCastModel 𝓘(ℝ, ℂ) x) v‖ := by
  have hg := (hasDerivAt_inv (𝕜 := ℂ) x.property).hasFDerivAt.restrictScalars ℝ
  rw [openDensity_mfderiv_apply puncturedPlaneDomain puncturedPlaneDomain
    puncturedReciprocal (fun z : ℂ => z⁻¹) (fun _ => rfl)
    puncturedReciprocal_mdifferentiable x _ hg v]
  change (1 / ‖x.val⁻¹‖) * ‖_ * (-(x.val ^ 2)⁻¹)‖ = (1 / ‖x.val‖) * ‖_‖
  rw [norm_inv, norm_mul, norm_neg, norm_inv, norm_pow]
  field_simp [norm_ne_zero_iff.mpr x.property]
  rfl

theorem puncturedScaling_pathDist (a : ℂˣ) (x y : PuncturedPlane) :
    puncturedDensity.pathDist (puncturedScaling a x) (puncturedScaling a y) =
      puncturedDensity.pathDist x y :=
  Auxiliary.Analysis.Density.pathDist_equiv (puncturedScaling a) (puncturedScaling_mdifferentiable a)
    (puncturedScaling_covariance a) x y

theorem puncturedReciprocal_pathDist (x y : PuncturedPlane) :
    puncturedDensity.pathDist (puncturedReciprocal x) (puncturedReciprocal y) =
      puncturedDensity.pathDist x y :=
  Auxiliary.Analysis.Density.pathDist_equiv puncturedReciprocal puncturedReciprocal_mdifferentiable
    puncturedReciprocal_covariance x y

/-- Restriction of the actual endpoint-pair stabilizer to the punctured finite plane. -/
def puncturedMobiusEquiv (f : mobiusZeroInftyPairStabilizer) : PuncturedPlane ≃ PuncturedPlane := by
  classical
  let a := (mobius_zeroInftyPair_normal_form f).choose
  exact if f.val = Mobius.mobiusScaling a then puncturedScaling a
    else puncturedReciprocal.trans (puncturedScaling a)

theorem puncturedMobiusEquiv_coe (f : mobiusZeroInftyPairStabilizer) (x : PuncturedPlane) :
    ((puncturedMobiusEquiv f x).val : Mobius.ExtendedComplex) = (f.val : Equiv.Perm Mobius.ExtendedComplex) x.val := by
  classical
  let a := (mobius_zeroInftyPair_normal_form f).choose
  have ha := (mobius_zeroInftyPair_normal_form f).choose_spec
  change (((if f.val = Mobius.mobiusScaling a then puncturedScaling a
    else puncturedReciprocal.trans (puncturedScaling a)) x).val : Mobius.ExtendedComplex) = _
  split_ifs with h
  · rw [h, Mobius.mobiusScaling_coe]
    rfl
  · have hf : f.val = Mobius.mobiusScaling a * mobiusReciprocal := ha.resolve_left h
    rw [hf, mobiusScaling_mul_reciprocal_coe _ _ x.property]
    change (((a : ℂ) * x.val⁻¹ : ℂ) : Mobius.ExtendedComplex) = _
    rw [div_eq_mul_inv]

theorem puncturedMobiusEquiv_pathDist (f : mobiusZeroInftyPairStabilizer)
    (x y : PuncturedPlane) :
    puncturedDensity.pathDist (puncturedMobiusEquiv f x) (puncturedMobiusEquiv f y) =
      puncturedDensity.pathDist x y := by
  classical
  dsimp only [puncturedMobiusEquiv]
  split_ifs
  · exact puncturedScaling_pathDist _ x y
  · exact (puncturedScaling_pathDist _ _ _).trans (puncturedReciprocal_pathDist x y)

/-- The actual punctured action is a group homomorphism, not an independently chosen family action. -/
def puncturedMobiusHom : mobiusZeroInftyPairStabilizer →* Equiv.Perm PuncturedPlane where
  toFun := puncturedMobiusEquiv
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply OnePoint.coe_injective
    exact (puncturedMobiusEquiv_coe 1 x).trans rfl
  map_mul' f g := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply OnePoint.coe_injective
    change ((puncturedMobiusEquiv (f * g) x).val : Mobius.ExtendedComplex) =
      ((puncturedMobiusEquiv f (puncturedMobiusEquiv g x)).val : Mobius.ExtendedComplex)
    rw [puncturedMobiusEquiv_coe, puncturedMobiusEquiv_coe, puncturedMobiusEquiv_coe]
    rfl

theorem puncturedMobiusHom_injective : Function.Injective puncturedMobiusHom := by
  intro f g h
  apply Subtype.ext
  have hagree (z : ℂ) (hz : z ≠ 0) :
      (f.val : Equiv.Perm Mobius.ExtendedComplex) z = (g.val : Equiv.Perm Mobius.ExtendedComplex) z := by
    have he := congrArg (fun e : Equiv.Perm PuncturedPlane =>
      ((e ⟨z, hz⟩).val : Mobius.ExtendedComplex)) h
    change ((puncturedMobiusEquiv f ⟨z, hz⟩).val : Mobius.ExtendedComplex) =
      ((puncturedMobiusEquiv g ⟨z, hz⟩).val : Mobius.ExtendedComplex) at he
    simpa only [puncturedMobiusEquiv_coe] using he
  apply Mobius.mobius_eq_of_agree_triple f.val g.val ((1 : ℂ) : Mobius.ExtendedComplex)
    ((2 : ℂ) : Mobius.ExtendedComplex) ((3 : ℂ) : Mobius.ExtendedComplex)
  · norm_num [Mobius.TripleDistinct, OnePoint.coe_eq_coe]
  · exact hagree 1 one_ne_zero
  · exact hagree 2 (by norm_num)
  · exact hagree 3 (by norm_num)

theorem puncturedMobiusEquiv_isometry (f : mobiusZeroInftyPairStabilizer) :
    @Isometry PuncturedPlane PuncturedPlane
      puncturedMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      puncturedMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace (puncturedMobiusEquiv f) := by
  apply (@isometry_iff_dist_eq PuncturedPlane PuncturedPlane
    puncturedMetricSpace.toPseudoMetricSpace puncturedMetricSpace.toPseudoMetricSpace _).mpr
  exact puncturedMobiusEquiv_pathDist f

theorem puncturedPieceLength_eq_integral (γ : ℝ → PuncturedPlane) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, ℂ) 1 γ (Icc a b)) :
    puncturedDensity.pieceLength γ a b = ENNReal.ofReal
      (∫ t in a..b, ‖derivWithin (fun u => (γ u).val) (Icc a b) t‖ / ‖(γ t).val‖) := by
  rw [puncturedDensity.pieceLength_eq_ofReal_integral γ a b hab hγ]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [puncturedDensity_apply]
  ring

theorem puncturedMetricSpace_topology :
    puncturedMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace PuncturedPlane) := rfl

/-- The actual Type 3 conjugate acts by genuine punctured length-metric isometries. -/
theorem typeThree_conjugate_punctured_isometries (H : Subgroup Mobius.complexMobiusGroup)
    (h : HasTypeThreeBoundaryOrbit H) :
    ∃ q : Mobius.complexMobiusGroup, ∀ f : DiscreteGroups.Action.Actions.subgroupConjugate q H,
      ∃ e : PuncturedPlane ≃ PuncturedPlane,
        (∀ x : PuncturedPlane, ((e x).val : Mobius.ExtendedComplex) =
          (f.val : Equiv.Perm Mobius.ExtendedComplex) x.val) ∧
        ∀ x y : PuncturedPlane, puncturedDensity.pathDist (e x) (e y) =
          puncturedDensity.pathDist x y := by
  obtain ⟨a, b, hab, hp⟩ := hasTypeThreeBoundaryOrbit_invariant_pair H h
  obtain ⟨q, hq⟩ := mobius_invariant_pair_conjugate_zeroInftyPairStabilizer H a b hab hp
  refine ⟨q, fun f => ?_⟩
  let F : mobiusZeroInftyPairStabilizer := ⟨f.val, hq f.property⟩
  exact ⟨puncturedMobiusEquiv F, puncturedMobiusEquiv_coe F, puncturedMobiusEquiv_pathDist F⟩

end PuncturedMetric
end
end LowDimensionalTopology.Geometry.DiscreteGroups
