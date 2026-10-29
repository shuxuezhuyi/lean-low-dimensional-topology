module

public import LowDimensionalTopology.Geometry.Surfaces.AdmissibleCurveClassStraightening
public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleCircleRangeClass
public import LowDimensionalTopology.Geometry.Teichmuller.MarkedSpectrumReindexing
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Data.Fintype.Card

/-!
# The geometric-union and free-class criteria for reducibility

The ranges of the actual members of an admissible family are the connected
components of its geometric union. The existing connected-component image
theorem therefore turns preservation of that union into a permutation of
all its members. Only removing their circle parameterizations uses the
explicit independent circle-homotopy input. The reverse implication reuses
the separately proved simultaneous-straightening consumer.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

namespace AdmissibleMulticurve

variable [T2Space X]

/-- Each actual member range is exactly a component of the geometric union. -/
theorem connectedComponentIn_carrier_eq_range (C : AdmissibleMulticurve X)
    (c : C.curves) {x : X} (hx : x ∈ Set.range c.val.val) :
    connectedComponentIn C.carrier x = Set.range c.val.val := by
  classical
  let rest : Set X := ⋃ d ∈ C.curves.erase c.val, Set.range d.val
  have hcClosed : IsClosed (Set.range c.val.val) :=
    c.val.isClosedEmbedding.isClosed_range
  have hrestClosed : IsClosed rest := by
    exact isClosed_biUnion_finset fun d _ => d.isClosedEmbedding.isClosed_range
  have hdisjoint : Disjoint (Set.range c.val.val) rest := by
    apply Set.disjoint_left.mpr
    intro y hcy hry
    simp only [rest, Set.mem_iUnion] at hry
    obtain ⟨d, hd, hdy⟩ := hry
    exact Set.disjoint_left.mp
      (C.disjoint c.property (Finset.mem_erase.mp hd).2
        (Finset.mem_erase.mp hd).1.symm) hcy hdy
  have hcover : C.carrier ⊆ Set.range c.val.val ∪ rest := by
    intro y hy
    simp only [carrier, Set.mem_iUnion] at hy
    obtain ⟨d, hd, hdy⟩ := hy
    by_cases hdc : d = c.val
    · exact Or.inl (hdc ▸ hdy)
    · right
      simp only [rest, Set.mem_iUnion]
      exact ⟨d, Finset.mem_erase.mpr ⟨hdc, hd⟩, hdy⟩
  apply Set.Subset.antisymm
  · have hchoice :=
      (isPreconnected_iff_subset_of_disjoint_closed.mp
        (isPreconnected_connectedComponentIn :
          IsPreconnected (connectedComponentIn C.carrier x)))
        (Set.range c.val.val) rest hcClosed hrestClosed
        ((connectedComponentIn_subset C.carrier x).trans hcover)
        (by rw [hdisjoint.inter_eq, Set.inter_empty])
    rcases hchoice with hsub | hsub
    · exact hsub
    · exact False.elim (Set.disjoint_left.mp hdisjoint hx
        (hsub (mem_connectedComponentIn (C.curve_subset_carrier c.property hx))))
  · exact (isPreconnected_range c.val.val.continuous).subset_connectedComponentIn
      hx (C.curve_subset_carrier c.property)

/-- A homeomorphism preserving the entire union sends every member onto a member. -/
theorem exists_image_range_of_isReducedBy (C : AdmissibleMulticurve X)
    (k : X ≃ₜ X) (hk : IsReducedBy k C) (c : C.curves) :
    ∃ d : C.curves, k '' Set.range c.val.val = Set.range d.val.val := by
  change k '' C.carrier = C.carrier at hk
  let x := c.val.val (1 : Circle)
  have hxc : x ∈ Set.range c.val.val := ⟨1, rfl⟩
  have hx : x ∈ C.carrier := C.curve_subset_carrier c.property hxc
  have hkx : k x ∈ C.carrier := by
    rw [← hk]
    exact ⟨x, hx, rfl⟩
  have hmem : ∃ d ∈ C.curves, k x ∈ Set.range d.val := by
    simpa only [carrier, Set.mem_iUnion, exists_prop] using hkx
  obtain ⟨d, hd, hkd⟩ := hmem
  refine ⟨⟨d, hd⟩, ?_⟩
  calc
    k '' Set.range c.val.val = k '' connectedComponentIn C.carrier x :=
      congrArg (fun s : Set X => k '' s)
        (C.connectedComponentIn_carrier_eq_range c hxc).symm
    _ = connectedComponentIn (k '' C.carrier) (k x) := k.image_connectedComponentIn hx
    _ = connectedComponentIn C.carrier (k x) := by rw [hk]
    _ = Set.range d.val := C.connectedComponentIn_carrier_eq_range ⟨d, hd⟩ hkd

/-- The action on the actual geometric members is a genuine finite permutation. -/
theorem exists_range_permutation_of_isReducedBy (C : AdmissibleMulticurve X)
    (k : X ≃ₜ X) (hk : IsReducedBy k C) :
    ∃ e : C.curves ≃ C.curves,
      ∀ c : C.curves, k '' Set.range c.val.val = Set.range (e c).val.val := by
  classical
  let p (c : C.curves) : C.curves :=
    Classical.choose (C.exists_image_range_of_isReducedBy k hk c)
  have hp (c : C.curves) : k '' Set.range c.val.val = Set.range (p c).val.val :=
    Classical.choose_spec (C.exists_image_range_of_isReducedBy k hk c)
  have hinj : Function.Injective p := by
    intro c d hcd
    apply Subtype.ext
    by_contra hne
    have hr : Set.range c.val.val = Set.range d.val.val :=
      k.injective.image_injective (by rw [hp c, hp d, hcd])
    have hpoint : c.val.val (1 : Circle) ∈ Set.range d.val.val :=
      hr ▸ (show c.val.val (1 : Circle) ∈ Set.range c.val.val from ⟨1, rfl⟩)
    exact Set.disjoint_left.mp (C.disjoint c.property d.property hne) ⟨1, rfl⟩ hpoint
  let e : C.curves ≃ C.curves :=
    Equiv.ofBijective p ⟨hinj, Finite.surjective_of_injective hinj⟩
  exact ⟨e, fun c => hp c⟩

/-- Union preservation induces class-set invariance after parameterizations are removed. -/
theorem preserves_freeClasses_of_isReducedBy
    (hCircle : LowDimensionalTopology.Unproved.Topology.CircleHomeomorphHomotopyDichotomy)
    (C : AdmissibleMulticurve X) (k : X ≃ₜ X) (hk : IsReducedBy k C) :
    essentialSimpleFreeClassEquiv k '' C.freeClasses = C.freeClasses := by
  obtain ⟨e, he⟩ := C.exists_range_permutation_of_isReducedBy k hk
  have hclass (c : C.curves) :
      essentialSimpleFreeClassEquiv k c.val.freeClass = (e c).val.freeClass := by
    have hr : Set.range (c.val.mapHomeomorph k).val = Set.range (e c).val.val := by
      change Set.range (k ∘ c.val.val) = _
      rw [Set.range_comp]
      exact he c
    exact EssentialSimpleCircle.freeClass_eq_of_range_eq_of_circleHomeomorphHomotopyDichotomy
      hCircle (c.val.mapHomeomorph k) (e c).val hr
  ext a
  constructor
  · rintro ⟨b, ⟨c, rfl⟩, rfl⟩
    exact ⟨e c, (hclass c).symm⟩
  · rintro ⟨d, rfl⟩
    refine ⟨(e.symm d).val.freeClass, ⟨e.symm d, rfl⟩, ?_⟩
    simpa only [e.apply_symm_apply] using hclass (e.symm d)

end AdmissibleMulticurve

/-- The original reducibility witness yields an invariant actual admissible class set. -/
theorem exists_preserved_admissibleFreeClasses_of_isReducible [T2Space X]
    (hCircle : LowDimensionalTopology.Unproved.Topology.CircleHomeomorphHomotopyDichotomy)
    (f : X ≃ₜ X) (hf : IsReducible f) :
    ∃ C : AdmissibleMulticurve X,
      essentialSimpleFreeClassEquiv f '' C.freeClasses = C.freeClasses := by
  obtain ⟨k, hfk, C, hk⟩ := hf
  refine ⟨C, ?_⟩
  rw [essentialSimpleFreeClassEquiv_eq_of_homotopic f k hfk]
  exact AdmissibleMulticurve.preserves_freeClasses_of_isReducedBy hCircle C k hk

/-- The complete geometric-union/free-class criterion, with its two independent
classical prerequisites kept explicit. -/
theorem isReducible_iff_preserves_admissibleFreeClasses_of_straightening
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hCircle : LowDimensionalTopology.Unproved.Topology.CircleHomeomorphHomotopyDichotomy)
    (hStraight : LowDimensionalTopology.Unproved.Surfaces.SimultaneousAdmissibleCurveStraightening R g)
    (f : X ≃ₜ X) :
    IsReducible f ↔ ∃ C : AdmissibleMulticurve X,
      essentialSimpleFreeClassEquiv f '' C.freeClasses = C.freeClasses := by
  let : T2Space X := R.t2Space
  constructor
  · exact exists_preserved_admissibleFreeClasses_of_isReducible hCircle f
  · rintro ⟨C, hC⟩
    exact isReducible_of_preserves_admissibleFreeClasses_of_straightening
      R hg hgenus hStraight f C hC

end LowDimensionalTopology.Geometry.Surfaces
