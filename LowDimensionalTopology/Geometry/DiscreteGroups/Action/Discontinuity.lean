/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.CompactlyCoherentSpace
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Sequences

/-!
# Elementary properties of discontinuous actions
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.DiscreteGroups.Action

section Basic

variable (G X : Type*) [Group G] [TopologicalSpace X] [MulAction G X]

/-- The single-compact-set condition. -/
def IsDiscontinuous : Prop :=
  ∀ K : Set X, IsCompact K → {g : G | ((g • ·) '' K ∩ K).Nonempty}.Finite

theorem isDiscontinuous_iff_properlyDiscontinuousSMul :
    IsDiscontinuous G X ↔ ProperlyDiscontinuousSMul G X := by
  constructor
  · intro h
    refine ⟨fun {K L} hK hL => (h (K ∪ L) (hK.union hL)).subset ?_⟩
    rintro g ⟨y, ⟨x, hx, rfl⟩, hy⟩
    exact ⟨g • x, ⟨x, Or.inl hx, rfl⟩, Or.inr hy⟩
  · intro h K hK
    exact h.finite_disjoint_inter_image hK hK

theorem isDiscontinuous_of_finite [Finite G] : IsDiscontinuous G X :=
  (isDiscontinuous_iff_properlyDiscontinuousSMul G X).mpr inferInstance

variable {G X}

/-- Passing to a subgroup preserves the source definition. -/
theorem IsDiscontinuous.subgroup (h : IsDiscontinuous G X) (H : Subgroup G) :
    IsDiscontinuous H X := by
  let : ProperlyDiscontinuousSMul G X :=
    (isDiscontinuous_iff_properlyDiscontinuousSMul G X).mp h
  exact (isDiscontinuous_iff_properlyDiscontinuousSMul H X).mpr inferInstance

variable {H Y : Type*} [Group H] [TopologicalSpace Y] [MulAction H Y]

/-- A homeomorphism and an equivariant relabeling of the acting group preserve discontinuity. -/
theorem properlyDiscontinuous_transport (φ : G ≃ H) (e : X ≃ₜ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) (h : ProperlyDiscontinuousSMul G X) :
    ProperlyDiscontinuousSMul H Y := by
  refine ⟨fun {K L} hK hL =>
    ((h.finite_disjoint_inter_image (hK.image e.symm.continuous)
      (hL.image e.symm.continuous)).image φ).subset ?_⟩
  rintro g ⟨_, ⟨x, hx, rfl⟩, hLx⟩
  refine ⟨φ.symm g, ?_, φ.apply_symm_apply g⟩
  refine ⟨φ.symm g • e.symm x, ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩,
    g • x, hLx, ?_⟩
  apply e.injective
  simpa only [e.apply_symm_apply, φ.apply_symm_apply] using (he (φ.symm g) (e.symm x)).symm

theorem IsDiscontinuous.transport (φ : G ≃ H) (e : X ≃ₜ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) (h : IsDiscontinuous G X) :
    IsDiscontinuous H Y :=
  (isDiscontinuous_iff_properlyDiscontinuousSMul H Y).mpr
    (properlyDiscontinuous_transport φ e he
      ((isDiscontinuous_iff_properlyDiscontinuousSMul G X).mp h))

/-- Restriction of the actual action to an invariant subset. -/
@[instance_reducible]
def invariantSubsetMulAction (S : Set X) (hS : ∀ (g : G) x, x ∈ S → g • x ∈ S) :
    MulAction G S where
  smul g x := ⟨g • x.val, hS g x.val x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

/-- No closedness or local compactness is needed for restriction to an invariant subset. -/
theorem IsDiscontinuous.invariantSubset (h : IsDiscontinuous G X) (S : Set X)
    (hS : ∀ (g : G) x, x ∈ S → g • x ∈ S) :
    @IsDiscontinuous G S _ _ (invariantSubsetMulAction S hS) := by
  let discontinuousInvariantAction := invariantSubsetMulAction S hS
  change IsDiscontinuous G S
  intro K hK
  refine (h (Subtype.val '' K) (hK.image continuous_subtype_val)).subset ?_
  rintro g ⟨_, ⟨x, hx, rfl⟩, hgx⟩
  exact ⟨g • x.val, ⟨x.val, ⟨x, hx, rfl⟩, rfl⟩, g • x, hgx, rfl⟩

/-- An injective sequence of group elements cannot yield a convergent point orbit. -/
theorem IsDiscontinuous.not_tendsto_orbit (h : IsDiscontinuous G X)
    (g : ℕ → G) (hg : Function.Injective g) (x y : X) :
    ¬ Tendsto (fun n => g n • x) atTop (𝓝 y) := by
  intro ht
  let K := insert x (insert y (range (fun n => g n • x)))
  have hK : IsCompact K := ht.isCompact_insert_range.insert x
  have hfin := h K hK
  have hr : (range g).Finite := hfin.subset (by
    rintro _ ⟨n, rfl⟩
    exact ⟨g n • x, ⟨x, mem_insert x _, rfl⟩,
      Or.inr (Or.inr (mem_range_self n))⟩)
  exact (Set.infinite_range_of_injective hg) hr

/-- Every point stabilizer is finite. -/
theorem IsDiscontinuous.finite_stabilizer (h : IsDiscontinuous G X) (x : X) :
    (MulAction.stabilizer G x : Set G).Finite :=
  ((isDiscontinuous_iff_properlyDiscontinuousSMul G X).mp h).finite_stabilizer' G x

/-- Every compact subset meets each orbit in finitely many points. -/
theorem IsDiscontinuous.finite_inter_orbit (h : IsDiscontinuous G X) (x : X)
    {K : Set X} (hK : IsCompact K) : (K ∩ MulAction.orbit G x).Finite := by
  have hp := (isDiscontinuous_iff_properlyDiscontinuousSMul G X).mp h
  refine ((hp.finite_disjoint_inter_image (isCompact_singleton (x := x)) hK).image
    (fun g : G => g • x)).subset ?_
  rintro z ⟨hzK, g, rfl⟩
  exact ⟨g, ⟨g • x, ⟨x, mem_singleton x, rfl⟩, hzK⟩, rfl⟩

/-- In a compactly coherent T1 space, every subset of an orbit is closed. -/
theorem IsDiscontinuous.isClosed_subset_orbit [T1Space X] [CompactlyCoherentSpace X]
    (h : IsDiscontinuous G X) (x : X) {A : Set X} (hA : A ⊆ MulAction.orbit G x) :
    IsClosed A := by
  apply (CompactlyCoherentSpace.isClosed_iff A).mpr
  intro K hK
  have hfin : (K ∩ A).Finite := (h.finite_inter_orbit x hK).subset (by
    intro z hz
    exact ⟨hz.1, hA hz.2⟩)
  have hp := hfin.preimage (Subtype.val_injective (p := fun x => x ∈ K)).injOn
  convert hp.isClosed using 1
  ext z
  simp only [mem_preimage, mem_inter_iff, z.property, true_and]

/-- The orbit itself is discrete; no local compactness assumption is used. -/
theorem IsDiscontinuous.isDiscrete_orbit [T1Space X] [CompactlyCoherentSpace X]
    (h : IsDiscontinuous G X) (x : X) : IsDiscrete (MulAction.orbit G x) := by
  refine ⟨discreteTopology_iff_forall_isClosed.mpr ?_⟩
  intro A
  have hc := h.isClosed_subset_orbit x (A := Subtype.val '' A) (by
    rintro _ ⟨z, _, rfl⟩
    exact z.property)
  convert hc.preimage continuous_subtype_val using 1
  ext z
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    exact (Subtype.ext hwz : w = z) ▸ hw

/-- On a second-countable T1 space, every orbit is countable. -/
theorem IsDiscontinuous.countable_orbit [T1Space X] [SecondCountableTopology X]
    (h : IsDiscontinuous G X) (x : X) : (MulAction.orbit G x).Countable := by
  let : DiscreteTopology (MulAction.orbit G x) := (h.isDiscrete_orbit x).to_subtype
  exact Set.countable_coe_iff.mpr
    (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)

/-- A nonempty second-countable T1 action satisfying the compact-set condition has countable group. -/
theorem IsDiscontinuous.countable_of_nonempty [T1Space X] [SecondCountableTopology X]
    (h : IsDiscontinuous G X) (x : X) : Countable G := by
  classical
  let : Countable (MulAction.orbit G x) := (h.countable_orbit x).to_subtype
  let f : G → MulAction.orbit G x := fun g => ⟨g • x, MulAction.mem_orbit x g⟩
  apply Countable.of_preimage_singleton (f := f)
  intro y
  have hp := (isDiscontinuous_iff_properlyDiscontinuousSMul G X).mp h
  refine ((hp.finite_disjoint_inter_image (isCompact_singleton (x := x))
    (isCompact_singleton (x := y.val))).subset ?_).countable
  intro g hg
  have he : g • x = y.val := congrArg Subtype.val hg
  exact ⟨g • x, ⟨x, mem_singleton x, rfl⟩, he⟩

/-- Faithfulness also handles the empty space, whose self-homeomorphism group is trivial. -/
theorem IsDiscontinuous.countable [T1Space X] [SecondCountableTopology X] [FaithfulSMul G X]
    (h : IsDiscontinuous G X) : Countable G := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · let : IsEmpty X := hX
    let : Subsingleton G := ⟨fun _ _ => eq_of_smul_eq_smul (fun x : X => isEmptyElim x)⟩
    exact inferInstance
  · exact h.countable_of_nonempty (Classical.choice hX)

end Basic

section HomeomorphConjugacy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Actual conjugation between the groups of self-homeomorphisms. -/
def homeomorphConjugation (e : X ≃ₜ Y) : (X ≃ₜ X) ≃* (Y ≃ₜ Y) where
  toFun f := e.symm.trans (f.trans e)
  invFun f := e.trans (f.trans e.symm)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_mul' f g := by ext x; simp

def conjugateHomeomorphSubgroup (e : X ≃ₜ Y) (K : Subgroup (X ≃ₜ X)) :
    Subgroup (Y ≃ₜ Y) := K.map (homeomorphConjugation e).toMonoidHom

def conjugateHomeomorphSubgroupEquiv (e : X ≃ₜ Y) (K : Subgroup (X ≃ₜ X)) :
    K ≃* conjugateHomeomorphSubgroup e K := (homeomorphConjugation e).subgroupMap K

theorem conjugateHomeomorphSubgroup_equivariant (e : X ≃ₜ Y)
    (K : Subgroup (X ≃ₜ X)) (g : K) (x : X) :
    e (g • x) = conjugateHomeomorphSubgroupEquiv e K g • e x := by
  change e ((g : X ≃ₜ X) x) = e ((g : X ≃ₜ X) (e.symm (e x)))
  rw [e.symm_apply_apply]

/-- The literal conjugated group, rather than just an abstract copied action. -/
theorem IsDiscontinuous.homeomorphConjugate (e : X ≃ₜ Y) (K : Subgroup (X ≃ₜ X))
    (h : IsDiscontinuous K X) : IsDiscontinuous (conjugateHomeomorphSubgroup e K) Y :=
  h.transport (conjugateHomeomorphSubgroupEquiv e K).toEquiv e
    (conjugateHomeomorphSubgroup_equivariant e K)

/-- The conjugation formula for an actual group of self-homeomorphisms, including the empty space. -/
theorem homeomorphSubgroup_countable [T1Space X] [SecondCountableTopology X]
    (K : Subgroup (X ≃ₜ X)) (h : IsDiscontinuous K X) : Countable K := h.countable

end HomeomorphConjugacy

end LowDimensionalTopology.Geometry.DiscreteGroups.Action
