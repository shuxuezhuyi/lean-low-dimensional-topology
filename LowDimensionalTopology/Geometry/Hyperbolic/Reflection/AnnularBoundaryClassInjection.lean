module
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularDiscGroup
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.PantsThreeFreeWords
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenGapLocalFiniteness
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian
open DiscreteGroups.Action.Actions
noncomputable section

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "G" => annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr
local notation "P" => HalfPlaneFuchsianGroup.cayleyData (annularPairReflectionHalfPlaneData E r x hE hr hin hout)
local notation "e" => annularPairReflectionDiscFreeEquiv E r x hE hr hin hout

/-- The three literal words in the same actual original Cayley disc group. -/
def annularDiscPeripheralWord (i : Fin 3) : G := e (pantsThreeFreeWords i)

local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout

/-- Literal primitive words generate actual maximal cyclic subgroups of the whole disc group. -/
theorem annularDiscPeripheralWord_maximal (i : Fin 3) :
    IsMaximalCyclicIn G (Subgroup.zpowers (g i).val) := by
  refine ⟨Subgroup.zpowers_le_of_mem (g i).property, inferInstance, ?_⟩
  intro L hLG hLC hKL
  obtain ⟨a, ha⟩ := (L.isCyclic_iff_exists_zpowers_eq_top).mp hLC
  have haL : a ∈ L := by rw [← ha]; exact Subgroup.mem_zpowers a
  let A : G := ⟨a, hLG haL⟩
  have hgL : (g i).val ∈ L := hKL (Subgroup.mem_zpowers (g i).val)
  rw [← ha] at hgL
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgL
  have hfree : pantsThreeFreeWords i = (e).symm A ^ n := by
    apply (e).injective
    rw [map_zpow, (e).apply_symm_apply]
    exact Subtype.ext hn.symm
  rcases pantsThreeFreeWords_zpow_exponent i ((e).symm A) n hfree with hn1 | hn1
  · have hga : (g i).val = a := by simpa [hn1] using hn.symm
    simpa only [hga] using ha.symm
  · have hga : (g i).val = a⁻¹ := by simpa [hn1] using hn.symm
    simpa only [hga, Subgroup.zpowers_inv] using ha.symm

/-- Each actual peripheral cyclic subgroup is a genuine boundary-class representative
under the stated ordinary-interval geometry. -/
def annularBoundaryWordSubgroup
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (P).asFuchsianDisc (g i)) (i : Fin 3) :
    fuchsianMaximalBoundaryHyperbolicCyclicSubgroups (P).asFuchsianDisc :=
  ⟨Subgroup.zpowers (g i).val,
    annularDiscPeripheralWord_maximal E r x hE hr hin hout i,
    g i, Subgroup.mem_zpowers (g i).val, hB i⟩

/-- The original three words mapped to the actual whole-group boundary cyclic quotient. -/
def annularBoundaryWordClass
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (P).asFuchsianDisc (g i)) :
    Fin 3 → FuchsianBoundaryHyperbolicCyclicConjugacyClasses (P).asFuchsianDisc :=
  fun i => Quotient.mk _ (annularBoundaryWordSubgroup E r x hE hr hin hout hB i)

/-- Distinct literal words give distinct actual boundary cyclic conjugacy classes. -/
theorem annularBoundaryWordClass_injective
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (P).asFuchsianDisc (g i)) :
    Function.Injective (annularBoundaryWordClass E r x hE hr hin hout hB) := by
  let := mobiusSubgroupConjugationAction G
  intro i j hij
  by_contra hne
  have hrel := Quotient.exact hij
  change MulAction.orbitRel G (Subgroup Mobius.complexMobiusGroup)
    (Subgroup.zpowers (g i).val) (Subgroup.zpowers (g j).val) at hrel
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨h, hh⟩ := hrel
  change subgroupConjugate h.val (Subgroup.zpowers (g j).val) =
    Subgroup.zpowers (g i).val at hh
  have hm : (g i).val ∈ subgroupConjugate h.val (Subgroup.zpowers (g j).val) := by
    rw [hh]
    exact Subgroup.mem_zpowers (g i).val
  obtain ⟨b, hb, hbi⟩ := (mem_subgroupConjugate_iff h.val _ _).mp hm
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
  have heq : pantsThreeFreeWords i =
      (e).symm h * pantsThreeFreeWords j ^ n * ((e).symm h)⁻¹ := by
    apply (e).injective
    simp only [map_mul, map_zpow, map_inv, (e).apply_symm_apply]
    apply Subtype.ext
    change (g i).val = h.val * (g j).val ^ n * h.val⁻¹
    rw [hn]
    exact hbi.symm
  exact (pantsThreeFreeWords_not_conjugate_zpow i j hne) ⟨(e).symm h, n, heq⟩

/-- Actual finite generation supplies finiteness for the literal boundary-class lower bound. -/
theorem annularBoundaryWordClass_three_le
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (P).asFuchsianDisc (g i)) :
    3 ≤ Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses (P).asFuchsianDisc) := by
  let : Finite (FuchsianBoundaryHyperbolicCyclicConjugacyClasses (P).asFuchsianDisc) :=
    finitelyGenerated_boundary_cyclic_classes_finite P
      (annularPairReflectionDiscGroup_fg E r x hE hr hin hout)
  simpa using Nat.card_le_card_of_injective
    (annularBoundaryWordClass E r x hE hr hin hout hB)
    (annularBoundaryWordClass_injective E r x hE hr hin hout hB)

end
end LowDimensionalTopology.Geometry.Hyperbolic
