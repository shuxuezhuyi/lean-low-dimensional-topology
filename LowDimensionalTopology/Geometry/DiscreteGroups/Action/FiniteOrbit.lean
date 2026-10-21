module
public import Mathlib.Algebra.Group.Action.Sum
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite orbits of group actions

Finite-orbit criteria are transported through subgroups, equivariant maps and sums of
actions. Central elements with finite fixed sets and actions on finite invariant sets
provide further finiteness criteria.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false
open Set Function
open scoped Pointwise

namespace LowDimensionalTopology.Geometry.DiscreteGroups.Action

section FiniteOrbits

variable (G X : Type*) [Group G] [MulAction G X]

/-- Existence of a finite point orbit for the specified action. -/
def HasFiniteOrbit : Prop := ∃ x : X, (MulAction.orbit G x).Finite

variable {G X}

theorem hasFiniteOrbit_of_finite [Finite G] [Nonempty X] : HasFiniteOrbit G X :=
  ⟨Classical.choice inferInstance, Finite.finite_mulAction_orbit _⟩

theorem orbit_eq_singleton_of_fixed (x : X) (hx : ∀ g : G, g • x = x) :
    MulAction.orbit G x = {x} := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact hx g
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact MulAction.mem_orbit_self x

theorem hasFiniteOrbit_of_fixed (x : X) (hx : ∀ g : G, g • x = x) : HasFiniteOrbit G X := by
  refine ⟨x, ?_⟩
  rw [orbit_eq_singleton_of_fixed x hx]
  exact Set.finite_singleton x

theorem finite_orbit_subgroup (H : Subgroup G) (x : X)
    (hx : (MulAction.orbit G x).Finite) : (MulAction.orbit H x).Finite := by
  apply hx.subset
  rintro y ⟨g, rfl⟩
  exact MulAction.mem_orbit x (g : G)

theorem hasFiniteOrbit_subgroup (H : Subgroup G) (h : HasFiniteOrbit G X) :
    HasFiniteOrbit H X := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, finite_orbit_subgroup H x hx⟩

variable {Y : Type*} [MulAction G Y]

theorem orbit_image_equivariant (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (x : X) :
    e '' MulAction.orbit G x = MulAction.orbit G (e x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨g, rfl⟩, rfl⟩
    rw [he]
    exact MulAction.mem_orbit _ g
  · rintro ⟨g, rfl⟩
    exact ⟨g • x, MulAction.mem_orbit _ g, he g x⟩

theorem finite_orbit_equivariant_iff (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (x : X) :
    (MulAction.orbit G (e x)).Finite ↔ (MulAction.orbit G x).Finite := by
  rw [← orbit_image_equivariant e he]
  exact Set.finite_image_iff e.injective.injOn

theorem hasFiniteOrbit_equivariant_iff (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    HasFiniteOrbit G Y ↔ HasFiniteOrbit G X := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    apply (finite_orbit_equivariant_iff e he (e.symm y)).mp
    simpa only [e.apply_symm_apply] using hy
  · rintro ⟨x, hx⟩
    exact ⟨e x, (finite_orbit_equivariant_iff e he x).mpr hx⟩

theorem orbit_inl_eq_image (x : X) :
    MulAction.orbit G (Sum.inl x : X ⊕ Y) = Sum.inl '' MulAction.orbit G x := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g • x, MulAction.mem_orbit _ g, rfl⟩
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    exact MulAction.mem_orbit _ g

theorem orbit_inr_eq_image (y : Y) :
    MulAction.orbit G (Sum.inr y : X ⊕ Y) = Sum.inr '' MulAction.orbit G y := by
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g • y, MulAction.mem_orbit _ g, rfl⟩
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    exact MulAction.mem_orbit _ g

/-- Finite orbits of a component-preserving sum action occur in one of its components. -/
theorem hasFiniteOrbit_sum_iff : HasFiniteOrbit G (X ⊕ Y) ↔
    HasFiniteOrbit G X ∨ HasFiniteOrbit G Y := by
  constructor
  · rintro ⟨x | y, h⟩
    · left
      rw [orbit_inl_eq_image] at h
      exact ⟨x, h.of_finite_image Sum.inl_injective.injOn⟩
    · right
      rw [orbit_inr_eq_image] at h
      exact ⟨y, h.of_finite_image Sum.inr_injective.injOn⟩
  · rintro (⟨x, hx⟩ | ⟨y, hy⟩)
    · refine ⟨Sum.inl x, ?_⟩
      rw [orbit_inl_eq_image]
      exact hx.image _
    · refine ⟨Sum.inr y, ?_⟩
      rw [orbit_inr_eq_image]
      exact hy.image _

/-- One positive power fixes every point of a given finite orbit simultaneously. -/
theorem exists_positive_power_fixing_finite_orbit (x : X)
    (hx : (MulAction.orbit G x).Finite) (g : G) :
    ∃ n : ℕ, 0 < n ∧ ∀ y ∈ MulAction.orbit G x, (g ^ n) • y = y := by
  let : Finite (MulAction.orbit G x) := hx.to_subtype
  let F : G →* Equiv.Perm (MulAction.orbit G x) := MulAction.toPermHom G _
  refine ⟨orderOf (F g), orderOf_pos _, ?_⟩
  intro y hy
  have hF : F (g ^ orderOf (F g)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
  change ((F (g ^ orderOf (F g))) ⟨y, hy⟩ : MulAction.orbit G x).val = y
  rw [hF]
  rfl

end FiniteOrbits

section CommutingActions

variable {G X : Type*} [Group G] [MulAction G X]

/-- The orbit of a fixed point stays in the fixed set of a central element. -/
theorem orbit_subset_fixed_of_commute (g : G) (x : X) (hx : g • x = x)
    (hcomm : ∀ h : G, Commute g h) :
    MulAction.orbit G x ⊆ {y : X | g • y = y} := by
  rintro y ⟨h, rfl⟩
  change g • (h • x) = h • x
  rw [← mul_smul, (hcomm h).eq, mul_smul, hx]

/-- A finite nonempty fixed set of a central element supplies a genuine finite orbit. -/
theorem finite_orbit_of_commute_fixed (g : G) (x : X) (hx : g • x = x)
    (hcomm : ∀ h : G, Commute g h) (hfinite : {y : X | g • y = y}.Finite) :
    (MulAction.orbit G x).Finite :=
  hfinite.subset (orbit_subset_fixed_of_commute g x hx hcomm)

/-- The finite-fixed-set criterion for a general action. -/
theorem hasFiniteOrbit_of_commuting_finite_fixed (g : G)
    (hcomm : ∀ h : G, Commute g h) (hne : ∃ x : X, g • x = x)
    (hfinite : {y : X | g • y = y}.Finite) : HasFiniteOrbit G X := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, finite_orbit_of_commute_fixed g x hx hcomm hfinite⟩

end CommutingActions

section FiniteInvariantSets

variable {G X : Type*} [Group G] [MulAction G X]

/-- A finite invariant set with at least three points makes a two-fixed-point action faithful. -/
theorem finite_of_finite_invariant_set_fixed_encard_le_two
    (hfixed : ∀ g : G, g ≠ 1 → {x : X | g • x = x}.encard ≤ 2)
    (S : Set X) (hS : S.Finite) (hstable : ∀ g : G, MapsTo (g • ·) S S)
    (hcard : 2 < S.ncard) : Finite G := by
  let : Finite S := hS.to_subtype
  let : MulAction G S := {
    smul g x := ⟨g • x.val, hstable g x.property⟩
    one_smul x := Subtype.ext (one_smul G x.val)
    mul_smul g h x := Subtype.ext (mul_smul g h x.val) }
  let F : G →* Equiv.Perm S := MulAction.toPermHom G S
  have hF : Function.Injective F := (injective_iff_map_eq_one F).mpr (by
    intro g hg
    by_contra hne
    have hsub : S ⊆ {x : X | g • x = x} := by
      intro x hx
      have h := congrArg (fun p : Equiv.Perm S => (p ⟨x, hx⟩).val) hg
      exact h
    have hbound : S.encard ≤ 2 := (encard_le_encard hsub).trans (hfixed g hne)
    exact (not_le_of_gt hcard) (encard_le_coe_iff_finite_ncard_le.mp hbound).2)
  exact Finite.of_injective F hF

/-- The finite-orbit version of the same faithful finite-permutation argument. -/
theorem finite_of_finite_orbit_fixed_encard_le_two
    (hfixed : ∀ g : G, g ≠ 1 → {x : X | g • x = x}.encard ≤ 2)
    (x : X) (hx : (MulAction.orbit G x).Finite)
    (hcard : 2 < (MulAction.orbit G x).ncard) : Finite G :=
  finite_of_finite_invariant_set_fixed_encard_le_two hfixed (MulAction.orbit G x) hx
    (fun g => MulAction.mapsTo_smul_orbit g x) hcard

/-- Infinite two-fixed-point actions have finite orbits of cardinality at most two. -/
theorem infinite_finite_orbit_ncard_le_two [Infinite G]
    (hfixed : ∀ g : G, g ≠ 1 → {x : X | g • x = x}.encard ≤ 2)
    (x : X) (hx : (MulAction.orbit G x).Finite) : (MulAction.orbit G x).ncard ≤ 2 := by
  by_contra hcard
  have : Finite G := finite_of_finite_orbit_fixed_encard_le_two hfixed x hx
    (lt_of_not_ge hcard)
  exact not_finite G

/-- A finite orbit of size at most two is either a fixed point or a genuine two-point invariant orbit. -/
theorem finite_orbit_singleton_or_pair (x : X) (hx : (MulAction.orbit G x).Finite)
    (hcard : (MulAction.orbit G x).ncard ≤ 2) :
    (MulAction.orbit G x = {x} ∧ ∀ g : G, g • x = x) ∨
      ∃ a b : X, a ≠ b ∧ MulAction.orbit G x = {a, b} ∧
        ∀ g : G, (fun y : X => g • y) '' {a, b} = {a, b} := by
  have hpos : 0 < (MulAction.orbit G x).ncard :=
    (ncard_pos hx).mpr ⟨x, MulAction.mem_orbit_self x⟩
  have hc : (MulAction.orbit G x).ncard = 1 ∨ (MulAction.orbit G x).ncard = 2 := by omega
  rcases hc with hc | hc
  · obtain ⟨a, ha⟩ := ncard_eq_one.mp hc
    have hfixed (g : G) : g • x = x := by
      have hg := MulAction.mem_orbit x g
      have hself := MulAction.mem_orbit_self (M := G) x
      rw [ha, Set.mem_singleton_iff] at hg hself
      exact hg.trans hself.symm
    exact Or.inl ⟨orbit_eq_singleton_of_fixed x hfixed, hfixed⟩
  · obtain ⟨a, b, hab, habset⟩ := ncard_eq_two.mp hc
    refine Or.inr ⟨a, b, hab, habset, fun g => ?_⟩
    rw [Set.image_smul, ← habset, MulAction.smul_orbit]

end FiniteInvariantSets

section EquivariantMaps
variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
theorem orbit_image_of_equivariant_map (f : X → Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) (x : X) :
    f '' MulAction.orbit G x = MulAction.orbit G (f x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨g, rfl⟩, rfl⟩
    rw [hf]
    exact MulAction.mem_orbit _ g
  · rintro ⟨g, rfl⟩
    exact ⟨g • x, MulAction.mem_orbit _ g, hf g x⟩

theorem hasFiniteOrbit_of_equivariant_map (f : X → Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) (h : HasFiniteOrbit G X) :
    HasFiniteOrbit G Y := by
  obtain ⟨x, hx⟩ := h
  refine ⟨f x, ?_⟩
  rw [← orbit_image_of_equivariant_map f hf]
  exact hx.image f
end EquivariantMaps

end LowDimensionalTopology.Geometry.DiscreteGroups.Action
