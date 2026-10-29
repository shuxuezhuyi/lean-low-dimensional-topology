/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.Classification.MobiusTypes

/-!
# Relative conjugacy and the multiplier relation

Conjugacy relative to an automorphism subgroup restricts the conjugator only.
The transformations being compared remain arbitrary actual sphere Möbius maps.
A multiplier is a nonzero standard dilation parameter distinct from one for a
nonidentity, nonparabolic map; both reciprocal choices are retained.
-/

@[expose] public section

set_option autoImplicit false

open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Mobius

/-- Conjugacy by a member of the specified subgroup of actual sphere automorphisms.
Neither of the two transformations is required to belong to that subgroup. -/
def IsMobiusConjugateWithin (H : Subgroup complexMobiusGroup)
    (f g : complexMobiusGroup) : Prop :=
  ∃ q : complexMobiusGroup, q ∈ H ∧ q * f * q⁻¹ = g

/-- Taking the full ambient group recovers ordinary sphere conjugacy. -/
theorem isMobiusConjugateWithin_top_iff (f g : complexMobiusGroup) :
    IsMobiusConjugateWithin ⊤ f g ↔ IsConj f g := by
  constructor
  · rintro ⟨q, _, hq⟩
    exact isConj_iff.mpr ⟨q, hq⟩
  · intro h
    obtain ⟨q, hq⟩ := isConj_iff.mp h
    exact ⟨q, Subgroup.mem_top q, hq⟩

/-- On members of the specified subgroup this agrees with its intrinsic conjugacy. -/
theorem isMobiusConjugateWithin_subgroup_iff (H : Subgroup complexMobiusGroup)
    (f g : H) : IsMobiusConjugateWithin H (f : complexMobiusGroup)
      (g : complexMobiusGroup) ↔ IsConj f g := by
  constructor
  · rintro ⟨q, hq, he⟩
    apply isConj_iff.mpr
    refine ⟨⟨q, hq⟩, ?_⟩
    exact Subtype.ext he
  · intro h
    obtain ⟨q, hq⟩ := isConj_iff.mp h
    exact ⟨q, q.property, congrArg (fun x : H => (x : complexMobiusGroup)) hq⟩

/-- A multiplier of an arbitrary nonidentity, nonparabolic actual Möbius map.
Units express the nonzero parameter; `k ≠ 1` excludes the translation branch
of `mobiusStandardElement`. This is a relation, not a choice of one endpoint. -/
def IsMobiusMultiplier (f : complexMobiusGroup) (k : ℂˣ) : Prop :=
  f ≠ 1 ∧ ¬ MobiusParabolic f ∧ k ≠ 1 ∧ IsConj f (mobiusStandardElement k)

/-- The normal form is an actual global sphere map: multiplication on the finite
chart and the fixed point at infinity, conjugated by an actual Möbius map. -/
theorem IsMobiusMultiplier.normalForm {f : complexMobiusGroup} {k : ℂˣ}
    (h : IsMobiusMultiplier f k) :
    ∃ q : complexMobiusGroup, q * f * q⁻¹ = mobiusStandardElement k ∧
      (∀ z : ℂ, (mobiusStandardElement k : Equiv.Perm ExtendedComplex) z =
        (((k : ℂ) * z : ℂ) : ExtendedComplex)) ∧
      (mobiusStandardElement k : Equiv.Perm ExtendedComplex) ∞ = ∞ := by
  obtain ⟨q, hq⟩ := isConj_iff.mp h.2.2.2
  refine ⟨q, hq, ?_, mobiusStandardElement_infty k⟩
  intro z
  have hk : (k : ℂ) ≠ 1 := fun he => h.2.2.1 (Units.ext he)
  simpa only [ite_eq_right hk] using mobiusStandardElement_coe k z

/-- The source squared-trace equation for every multiplier choice. -/
theorem IsMobiusMultiplier.squaredTrace {f : complexMobiusGroup} {k : ℂˣ}
    (h : IsMobiusMultiplier f k) :
    mobiusSquaredTrace f = (k : ℂ) + (k : ℂ)⁻¹ + 2 := by
  exact ((mobius_isConj_iff_squaredTrace_eq f (mobiusStandardElement k)
    h.1 (mobiusStandardElement_ne_one k)).mp h.2.2.2).trans
      (mobiusStandardElement_squaredTrace k)

/-- Every map in exactly the source domain admits a multiplier. -/
theorem exists_mobiusMultiplier (f : complexMobiusGroup) (hf : f ≠ 1)
    (hp : ¬ MobiusParabolic f) : ∃ k : ℂˣ, IsMobiusMultiplier f k := by
  obtain ⟨k, hc⟩ := mobius_nonidentity_conjugate_standard f hf
  have hk : k ≠ 1 := by
    intro he
    apply hp
    apply (mobius_parabolic_iff_squaredTrace_eq_four f hf).mpr
    calc
      mobiusSquaredTrace f = mobiusSquaredTrace (mobiusStandardElement k) :=
        (mobius_isConj_iff_squaredTrace_eq f (mobiusStandardElement k)
          hf (mobiusStandardElement_ne_one k)).mp hc
      _ = 4 := by rw [mobiusStandardElement_squaredTrace, he]; norm_num
  exact ⟨k, hf, hp, hk, hc⟩

/-- A multiplier exists precisely on the source nonidentity/nonparabolic domain. -/
theorem exists_mobiusMultiplier_iff (f : complexMobiusGroup) :
    (∃ k : ℂˣ, IsMobiusMultiplier f k) ↔ f ≠ 1 ∧ ¬ MobiusParabolic f := by
  constructor
  · rintro ⟨k, h⟩
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hf, hp⟩
    exact exists_mobiusMultiplier f hf hp

/-- Reversing the two standard fixed points gives the reciprocal multiplier. -/
theorem IsMobiusMultiplier.inv {f : complexMobiusGroup} {k : ℂˣ}
    (h : IsMobiusMultiplier f k) : IsMobiusMultiplier f k⁻¹ := by
  have hc : IsConj (mobiusStandardElement k) (mobiusStandardElement k⁻¹) := by
    apply (complexMobius_isConj_iff _ _).mpr
    rw [mobiusStandardElement_equiv, mobiusStandardElement_equiv]
    exact Classification.standard_conjugate_inverse k
  exact ⟨h.1, h.2.1, inv_ne_one.mpr h.2.2.1, h.2.2.2.trans hc⟩

/-- All multiplier choices are exactly the reciprocal pair. They may coincide,
for example for the order-two dilation parameter `-1`. -/
theorem IsMobiusMultiplier.choices {f : complexMobiusGroup} {k : ℂˣ}
    (h : IsMobiusMultiplier f k) (l : ℂˣ) :
    IsMobiusMultiplier f l ↔ l = k ∨ l = k⁻¹ := by
  constructor
  · intro hl
    exact (Classification.standardTrace_eq_iff l k).mp
      (hl.squaredTrace.symm.trans h.squaredTrace)
  · rintro (rfl | rfl)
    · exact h
    · exact h.inv

end LowDimensionalTopology.Geometry.Mobius
