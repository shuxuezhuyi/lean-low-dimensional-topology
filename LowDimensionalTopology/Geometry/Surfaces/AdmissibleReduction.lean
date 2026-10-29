module

public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleFreeClasses
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Actual admissible multicurves and reduced surface maps

The finite nonempty family contains simultaneous actual embedded essential
circles. Their unoriented free classes are distinct. Reduction preserves the
literal geometric union; reducibility allows a freely homotopic homeomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The book's actual finite nonempty disjoint essential multicurve. -/
structure AdmissibleMulticurve (X : Type u) [TopologicalSpace X] where
  curves : Finset (EssentialSimpleCircle X)
  nonempty : curves.Nonempty
  disjoint : (curves : Set (EssentialSimpleCircle X)).PairwiseDisjoint
    (fun c => Set.range c.val)
  classes_injective : Set.InjOn
    (fun c : EssentialSimpleCircle X => c.freeClass) (curves : Set (EssentialSimpleCircle X))

namespace AdmissibleMulticurve

/-- The simultaneous original point-set union of exactly the supplied circle maps. -/
def carrier (C : AdmissibleMulticurve X) : Set X :=
  ⋃ c ∈ C.curves, Set.range c.val

theorem curve_subset_carrier (C : AdmissibleMulticurve X)
    {c : EssentialSimpleCircle X} (hc : c ∈ C.curves) :
    Set.range c.val ⊆ C.carrier := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, hx⟩⟩

theorem carrier_nonempty (C : AdmissibleMulticurve X) : C.carrier.Nonempty := by
  obtain ⟨c, hc⟩ := C.nonempty
  exact ⟨c.val (1 : Circle), C.curve_subset_carrier hc ⟨1, rfl⟩⟩

/-- Different members are not freely homotopic with either orientation. -/
theorem not_homotopic_or_reverse (C : AdmissibleMulticurve X)
    {c d : EssentialSimpleCircle X} (hc : c ∈ C.curves) (hd : d ∈ C.curves)
    (hcd : c ≠ d) :
    ¬ (c.val.Homotopic d.val ∨ c.val.Homotopic (d.val.comp circleReversal)) := by
  intro h
  exact hcd (C.classes_injective hc hd ((EssentialSimpleCircle.freeClass_eq_iff c d).mpr h))

end AdmissibleMulticurve

/-- Being reduced by C means exact preservation of its original geometric union. -/
def IsReducedBy (f : X ≃ₜ X) (C : AdmissibleMulticurve X) : Prop :=
  f '' C.carrier = C.carrier

theorem isReducedBy_refl (C : AdmissibleMulticurve X) :
    IsReducedBy (Homeomorph.refl X) C := by
  change id '' C.carrier = C.carrier
  exact Set.image_id _

theorem IsReducedBy.comp {f g : X ≃ₜ X} {C : AdmissibleMulticurve X}
    (hf : IsReducedBy f C) (hg : IsReducedBy g C) : IsReducedBy (f.trans g) C := by
  change f '' C.carrier = C.carrier at hf
  change g '' C.carrier = C.carrier at hg
  change (fun x => g (f x)) '' C.carrier = C.carrier
  rw [← Set.image_image, hf, hg]

theorem IsReducedBy.symm {f : X ≃ₜ X} {C : AdmissibleMulticurve X}
    (hf : IsReducedBy f C) : IsReducedBy f.symm C := by
  change f '' C.carrier = C.carrier at hf
  change f.symm '' C.carrier = C.carrier
  calc
    f.symm '' C.carrier = f.symm '' (f '' C.carrier) :=
      congrArg (fun s : Set X => f.symm '' s) hf.symm
    _ = C.carrier := by
      rw [Set.image_image]
      simp

/-- A map is reducible when an actual freely homotopic homeomorphism is reduced. -/
def IsReducible (f : X ≃ₜ X) : Prop :=
  ∃ g : X ≃ₜ X,
    ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap g) ∧
      ∃ C : AdmissibleMulticurve X, IsReducedBy g C

/-- Irreducibility is precisely the negation of the original reducibility predicate. -/
def IsIrreducible (f : X ≃ₜ X) : Prop := ¬ IsReducible f

theorem IsReducedBy.isReducible {f : X ≃ₜ X} {C : AdmissibleMulticurve X}
    (hf : IsReducedBy f C) : IsReducible f :=
  ⟨f, ContinuousMap.Homotopic.refl _, C, hf⟩

/-- Reducibility depends only on ordinary free homotopy of the original maps. -/
theorem isReducible_congr {f g : X ≃ₜ X}
    (hfg : ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap g)) :
    IsReducible f ↔ IsReducible g := by
  constructor
  · rintro ⟨k, hfk, C, hk⟩
    exact ⟨k, hfg.symm.trans hfk, C, hk⟩
  · rintro ⟨k, hgk, C, hk⟩
    exact ⟨k, hfg.trans hgk, C, hk⟩

/-- Irreducibility has the same genuine homotopy invariance. -/
theorem isIrreducible_congr {f g : X ≃ₜ X}
    (hfg : ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap g)) :
    IsIrreducible f ↔ IsIrreducible g :=
  not_congr (isReducible_congr hfg)

end LowDimensionalTopology.Geometry.Surfaces
