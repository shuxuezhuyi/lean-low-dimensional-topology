/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.Mobius
public import LowDimensionalTopology.Geometry.Mobius.Classification.MobiusTypes
public import Mathlib.Data.Set.Card
@[expose] public section
noncomputable section
open Set
open scoped OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

/-- Conjugation transports the entire genuine boundary fixed set. -/
theorem mobiusIteration_fixedPoints_conjugate (f h : complexMobiusGroup) :
    mobiusBoundaryFixedPoints (h * f * h⁻¹) = h.val '' mobiusBoundaryFixedPoints f := by
  ext z
  constructor
  · intro hz
    exact ⟨h.val.symm z, (mobius_conjugate_boundary_fixed_iff f h z).mp hz,
      h.val.apply_symm_apply z⟩
  · rintro ⟨w, hw, rfl⟩
    apply (mobius_conjugate_boundary_fixed_iff f h (h.val w)).mpr
    have hw' : f.val w = w := hw
    simpa only [Equiv.symm_apply_apply] using hw'

/-- Fixing every point of a finite original fixed set forces its conjugator to preserve that set. -/
theorem mobiusIteration_preserves_of_conjugate_fixes (f h : complexMobiusGroup)
    (hf : f ≠ 1)
    (hfix : ∀ z, f.val z = z → (h * f * h⁻¹).val z = z) :
    h.val '' mobiusBoundaryFixedPoints f = mobiusBoundaryFixedPoints f := by
  have hS : (mobiusBoundaryFixedPoints f).Finite := DiscreteGroups.mobius_boundary_fixedPoints_finite f hf
  have hsub : mobiusBoundaryFixedPoints f ⊆ h.val '' mobiusBoundaryFixedPoints f := by
    rw [← mobiusIteration_fixedPoints_conjugate]
    exact hfix
  exact (hS.eq_of_subset_of_encard_le hsub (Set.encard_image_le _ _)).symm

/-- A noninvolution preserving a nonidentity Mobius fixed set fixes every point of that set. -/
theorem mobiusIteration_fixes_of_preserves (f h : complexMobiusGroup) (hf : f ≠ 1)
    (hh : h ^ 2 ≠ 1)
    (hpres : h.val '' mobiusBoundaryFixedPoints f = mobiusBoundaryFixedPoints f) :
    ∀ z, f.val z = z → h.val z = z := by
  intro z hz
  by_contra hn
  have hswap := (mobius_preserved_fixed_pair f h hf hpres z hz hn).1
  exact hh (mobius_sq_eq_one_of_swaps h z (h.val z) (fun he => hn he.symm) rfl hswap)

/-- Conjugation of a map whose square is nonidentity still has nonidentity square. -/
theorem mobiusIteration_conjugate_sq_ne_one (f h : complexMobiusGroup) (hf : f ^ 2 ≠ 1) :
    (h * f * h⁻¹) ^ 2 ≠ 1 := by
  intro he
  apply hf
  have he' := congrArg (fun k : complexMobiusGroup => h⁻¹ * k * h) he
  simpa only [pow_two, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
    mul_inv_cancel_right, inv_mul_cancel, mul_one, one_mul] using he'

/-- Backward propagation along a terminating conjugation iteration preserves the fixed set. -/
theorem mobiusIteration_preserves_fixedPoints (f g : complexMobiusGroup)
    (hf : f ≠ 1) (hf2 : f ^ 2 ≠ 1) (n : ℕ)
    (hn : ((fun h : complexMobiusGroup => h * f * h⁻¹)^[n]) g = f) :
    g.val '' mobiusBoundaryFixedPoints f = mobiusBoundaryFixedPoints f := by
  induction n generalizing g with
  | zero =>
    have hg : g = f := hn
    subst g
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change f.val (f.val w) = f.val w
      rw [show f.val w = w from hw]
      exact hw
    · intro hz
      exact ⟨z, hz, hz⟩
  | succ n ih =>
    have hn' : ((fun h : complexMobiusGroup => h * f * h⁻¹)^[n]) (g * f * g⁻¹) = f := by
      simpa only [Function.iterate_succ_apply] using hn
    have hpres := ih (g * f * g⁻¹) hn'
    have hfix := mobiusIteration_fixes_of_preserves f (g * f * g⁻¹) hf
      (mobiusIteration_conjugate_sq_ne_one f g hf2) hpres
    exact mobiusIteration_preserves_of_conjugate_fixes f g hf hfix

/-- A pair preserving the finite fixed set of its first nonidentity member generates an elementary group. -/
theorem mobiusIteration_elementary_of_preserves (f g : complexMobiusGroup) (hf : f ≠ 1)
    (hg : g.val '' mobiusBoundaryFixedPoints f = mobiusBoundaryFixedPoints f) :
    DiscreteGroups.IsElementary (Subgroup.closure ({f, g} : Set complexMobiusGroup)) := by
  let S := mobiusBoundaryFixedPoints f
  let K := MulAction.stabilizer complexMobiusGroup S
  have hfK : f ∈ K := by
    change f • S = S
    rw [← Set.image_smul]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change f.val (f.val w) = f.val w
      rw [show f.val w = w from hw]
      exact hw
    · intro hz
      exact ⟨z, hz, hz⟩
  have hgK : g ∈ K := by
    change g • S = S
    rw [← Set.image_smul]
    exact hg
  have hcl : Subgroup.closure ({f, g} : Set complexMobiusGroup) ≤ K := by
    apply (Subgroup.closure_le _).mpr
    intro h hh
    rcases Set.mem_insert_iff.mp hh with rfl | hh
    · exact hfK
    · exact Set.mem_singleton_iff.mp hh ▸ hgK
  obtain ⟨a, ha⟩ := mobius_nonidentity_has_boundary_fixed f hf
  apply (DiscreteGroups.isElementary_iff_boundary_or_interior _).mpr
  left
  refine ⟨a, (DiscreteGroups.mobius_boundary_fixedPoints_finite f hf).subset ?_⟩
  rintro z ⟨h, rfl⟩
  have hstable : h.val • S = S := hcl h.property
  change h.val.val a ∈ S
  rw [← hstable, ← Set.image_smul]
  exact ⟨a, ha, rfl⟩

/-- For the actual Mobius group and all natural iteration indices. -/
theorem elementary_and_conjugation_second_iterate_eq_of_iterate_eq (f g : complexMobiusGroup) (hf : f ≠ 1)
    (hf2 : orderOf f ≠ 2) (n : ℕ)
    (hn : ((fun h : complexMobiusGroup => h * f * h⁻¹)^[n]) g = f) :
    DiscreteGroups.IsElementary (Subgroup.closure ({f, g} : Set complexMobiusGroup)) ∧
      ((fun h : complexMobiusGroup => h * f * h⁻¹)^[2]) g = f := by
  have hfsq : f ^ 2 ≠ 1 := fun he => hf2 (orderOf_eq_prime he hf)
  have hpres := mobiusIteration_preserves_fixedPoints f g hf hfsq n hn
  refine ⟨mobiusIteration_elementary_of_preserves f g hf hpres, ?_⟩
  have hg1 : g * f * g⁻¹ ≠ 1 := by
    intro he
    apply hf
    have he' := congrArg (fun k : complexMobiusGroup => g⁻¹ * k * g) he
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one, one_mul] using he'
  have hsame : MobiusSameFixedPoints f (g * f * g⁻¹) := by
    intro z
    change z ∈ mobiusBoundaryFixedPoints f ↔ z ∈ mobiusBoundaryFixedPoints (g * f * g⁻¹)
    rw [mobiusIteration_fixedPoints_conjugate, hpres]
  have hc := (mobius_commute_of_same_fixedPoints f (g * f * g⁻¹) hf hg1 hsame).symm.eq
  change (g * f * g⁻¹) * f * (g * f * g⁻¹)⁻¹ = f
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

end LowDimensionalTopology.Geometry.Mobius
