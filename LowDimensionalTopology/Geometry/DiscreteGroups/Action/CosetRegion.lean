module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.OrbitQuotient

/-!
# Coset-stable regions for subgroup actions.

A coset-stable region is invariant under a subgroup and disjoint from its translates
by elements outside that subgroup. Restricting a locally finite subgroup tiling to
such an open region preserves closure coverage and uniqueness of orbit representatives.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped Pointwise

namespace LowDimensionalTopology.Geometry.DiscreteGroups.Action

/-- The original subgroup-invariant region whose other coset translates are disjoint. -/
structure IsCosetStableRegion {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (S : Set X) : Prop where
  invariant : ∀ h : H, h • S = S
  disjoint : ∀ g : G, g ∉ H → Disjoint (g • S) S

/-- A locally finite subgroup tiling restricts densely to every genuine open invariant region. -/
theorem coset_region_subgroup_closure_cover {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X] (H : Subgroup G) (D S : Set X)
    (ho : IsOpen S) (hS : ∀ h : H, h • S = S)
    (hl : LocallyFinite (fun h : H => h • closure D))
    (hc : (⋃ h : H, h • closure D) = univ) :
    closure S ⊆ ⋃ h : H, h • closure (D ∩ S) := by
  let cosetSubgroupContinuous : ContinuousConstSMul H X :=
    ⟨fun h => continuous_const_smul h.val⟩
  have hDlf : LocallyFinite (fun h : H => h • D) :=
    hl.subset (fun _ => Set.smul_set_mono subset_closure)
  have hcl (h : H) : closure (h • D) = h • closure D :=
    ((Homeomorph.smul h).image_closure D).symm
  have hdense : closure (⋃ h : H, h • D) = univ := by
    rw [hDlf.closure_iUnion]
    simp_rw [hcl]
    exact hc
  have he : (⋃ h : H, h • D) ∩ S = ⋃ h : H, h • (D ∩ S) := by
    rw [iUnion_inter]
    congr 1
    funext h
    rw [smul_set_inter,hS h]
  have hsub : S ⊆ closure (⋃ h : H, h • (D ∩ S)) := by
    intro x hx
    have hh : x ∈ closure ((⋃ h : H, h • D) ∩ S) :=
      ho.closure_inter ⟨by rw [hdense];trivial,hx⟩
    rwa [he] at hh
  have hf : LocallyFinite (fun h : H => h • (D ∩ S)) :=
    hl.subset (fun _ => Set.smul_set_mono (inter_subset_left.trans subset_closure))
  have hi (h : H) : closure (h • (D ∩ S)) = h • closure (D ∩ S) :=
    ((Homeomorph.smul h).image_closure (D ∩ S)).symm
  have hh := closure_minimal hsub isClosed_closure
  rw [hf.closure_iUnion] at hh
  simpa only [hi] using hh

theorem IsCosetStableRegion.mem_of_intersection {G X : Type*} [Group G] [MulAction G X]
    {H : Subgroup G} {S : Set X} (hS : IsCosetStableRegion H S)
    {g : G} (h : (g • S ∩ S).Nonempty) : g ∈ H := by
  by_contra hn
  exact (Set.disjoint_left.mp (hS.disjoint g hn) h.choose_spec.1 h.choose_spec.2)

/-- Full-group orbit coverage follows from the actual coset-region coverage. -/
theorem coset_region_closure_meetsEveryOrbit {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X] (H : Subgroup G) (D S : Set X)
    (ho : IsOpen S) (hS : ∀ h : H, h • S = S)
    (hl : LocallyFinite (fun h : H => h • closure D))
    (hc : (⋃ h : H, h • closure D) = univ)
    (hcover : MeetsEveryOrbit G X (closure S)) :
    MeetsEveryOrbit G X (closure (D ∩ S)) := by
  intro x
  obtain ⟨g,hg⟩ := hcover x
  obtain ⟨h,y,hy,he⟩ := mem_iUnion.mp
    (coset_region_subgroup_closure_cover H D S ho hS hl hc hg)
  refine ⟨h.val⁻¹ * g,?_⟩
  change h.val • y = g • x at he
  rw [mul_smul,←he]
  change h⁻¹ • (h • y) ∈ closure (D ∩ S)
  rwa [inv_smul_smul]

/-- Stable coset regions introduce no new identifications among the original subgroup representatives. -/
theorem coset_region_orbit_unique {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (D S : Set X) (hS : IsCosetStableRegion H S)
    (hD : ∀ x ∈ D, ∀ y ∈ D, orbitProjection H X x = orbitProjection H X y → x = y)
    {x y : X} (hx : x ∈ D ∩ S) (hy : y ∈ D ∩ S)
    (hxy : orbitProjection G X x = orbitProjection G X y) : x = y := by
  obtain ⟨g,hg⟩ := (Quotient.exact hxy : MulAction.orbitRel G X x y)
  change g • y = x at hg
  have hm : g ∈ H := hS.mem_of_intersection ⟨x,⟨y,hy.2,hg⟩,hx.2⟩
  apply hD x hx.1 y hy.1
  exact Quotient.sound ⟨⟨g,hm⟩,hg⟩

end LowDimensionalTopology.Geometry.DiscreteGroups.Action
