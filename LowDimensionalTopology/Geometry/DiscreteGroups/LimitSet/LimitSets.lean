/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.NonElementaryLoxodromics
public import LowDimensionalTopology.Geometry.Mobius.Topology
public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Topology.DenseEmbedding
@[expose] public section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- All endpoints of loxodromic elements of the actual subgroup. -/
def mobiusLoxodromicFixedPointSet (H : Subgroup Mobius.complexMobiusGroup) : Set Mobius.ExtendedComplex :=
  {z | ∃ g : H, Mobius.MobiusLoxodromic g.val ∧ g • z = z}

/-- The closure is taken in the original compactified complex plane. -/
def mobiusLimitSet (H : Subgroup Mobius.complexMobiusGroup) : Set Mobius.ExtendedComplex :=
  closure (mobiusLoxodromicFixedPointSet H)

/-- The ordinary set is the complement of the limit set. -/
def mobiusOrdinarySet (H : Subgroup Mobius.complexMobiusGroup) : Set Mobius.ExtendedComplex :=
  (mobiusLimitSet H)ᶜ

theorem mobiusLimitSet_isClosed (H : Subgroup Mobius.complexMobiusGroup) :
    IsClosed (mobiusLimitSet H) := isClosed_closure

theorem mobiusOrdinarySet_isOpen (H : Subgroup Mobius.complexMobiusGroup) :
    IsOpen (mobiusOrdinarySet H) := (mobiusLimitSet_isClosed H).isOpen_compl

theorem mobiusLoxodromicFixedPointSet_subset_limitSet (H : Subgroup Mobius.complexMobiusGroup) :
    mobiusLoxodromicFixedPointSet H ⊆ mobiusLimitSet H := subset_closure

theorem mobiusLoxodromicFixedPointSet_mono {H K : Subgroup Mobius.complexMobiusGroup} (hHK : H ≤ K) :
    mobiusLoxodromicFixedPointSet H ⊆ mobiusLoxodromicFixedPointSet K := by
  rintro z ⟨g, hg, hfix⟩
  exact ⟨⟨g.val, hHK g.property⟩, hg, hfix⟩

theorem mobiusLimitSet_mono {H K : Subgroup Mobius.complexMobiusGroup} (hHK : H ≤ K) :
    mobiusLimitSet H ⊆ mobiusLimitSet K :=
  closure_mono (mobiusLoxodromicFixedPointSet_mono hHK)

theorem mobiusOrdinarySet_antitone {H K : Subgroup Mobius.complexMobiusGroup} (hHK : H ≤ K) :
    mobiusOrdinarySet K ⊆ mobiusOrdinarySet H :=
  compl_subset_compl.mpr (mobiusLimitSet_mono hHK)

theorem mobiusLoxodromicFixedPointSet_invariant (H : Subgroup Mobius.complexMobiusGroup)
    (h : H) {z : Mobius.ExtendedComplex} (hz : z ∈ mobiusLoxodromicFixedPointSet H) :
    h • z ∈ mobiusLoxodromicFixedPointSet H := by
  obtain ⟨g, hg, hfix⟩ := hz
  refine ⟨h * g * h⁻¹, Mobius.mobiusLoxodromic_conjugation_forward g.val h.val hg, ?_⟩
  rw [mul_smul, mul_smul, inv_smul_smul, hfix]

theorem mobiusLoxodromicFixedPointSet_image (H : Subgroup Mobius.complexMobiusGroup) (h : H) :
    (h.val : Equiv.Perm Mobius.ExtendedComplex) '' mobiusLoxodromicFixedPointSet H =
      mobiusLoxodromicFixedPointSet H := by
  apply Set.Subset.antisymm
  · rintro z ⟨w, hw, rfl⟩
    exact mobiusLoxodromicFixedPointSet_invariant H h hw
  · intro z hz
    exact ⟨h⁻¹ • z, mobiusLoxodromicFixedPointSet_invariant H h⁻¹ hz, smul_inv_smul h z⟩

theorem mobiusLimitSet_image (H : Subgroup Mobius.complexMobiusGroup) (h : H) :
    (h.val : Equiv.Perm Mobius.ExtendedComplex) '' mobiusLimitSet H = mobiusLimitSet H := by
  change (Mobius.mobiusBoundaryHomeomorph h.val) '' closure (mobiusLoxodromicFixedPointSet H) = _
  rw [Homeomorph.image_closure]
  exact congrArg closure (mobiusLoxodromicFixedPointSet_image H h)

theorem mobiusLimitSet_invariant (H : Subgroup Mobius.complexMobiusGroup) (h : H)
    {z : Mobius.ExtendedComplex} (hz : z ∈ mobiusLimitSet H) : h • z ∈ mobiusLimitSet H := by
  rw [← mobiusLimitSet_image H h]
  exact ⟨z, hz, rfl⟩

theorem mobiusOrdinarySet_invariant (H : Subgroup Mobius.complexMobiusGroup) (h : H)
    {z : Mobius.ExtendedComplex} (hz : z ∈ mobiusOrdinarySet H) : h • z ∈ mobiusOrdinarySet H := by
  intro hh
  have he := mobiusLimitSet_invariant H h⁻¹ hh
  rw [inv_smul_smul] at he
  exact hz he

/-- A perfect set is closed and has no isolated points. -/
theorem mobius_perfect_iff_closed_no_isolated (S : Set Mobius.ExtendedComplex) :
    Perfect S ↔ IsClosed S ∧
      ∀ z ∈ S, ∀ U ∈ 𝓝 z, ∃ w ∈ U ∩ S, w ≠ z := by
  rw [perfect_def, preperfect_iff_nhds]


/-- Invariance and non-elementarity make every nonempty boundary set infinite. -/
theorem nonElementary_invariant_nonempty_infinite (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (S : Set Mobius.ExtendedComplex) (hne : S.Nonempty)
    (hinv : ∀ g : H, ∀ z ∈ S, g • z ∈ S) : S.Infinite := by
  obtain ⟨z, hz⟩ := hne
  apply (nonElementary_boundary_orbit_infinite H hH z).mono
  rintro w ⟨g, rfl⟩
  exact hinv g z hz

theorem mobiusLoxodromicFixedPointSet_nonempty (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) : (mobiusLoxodromicFixedPointSet H).Nonempty := by
  obtain ⟨f, hf, hlo⟩ := nonElementary_exists_loxodromic H hH
  obtain ⟨z, hz⟩ := Mobius.mobius_nonidentity_has_boundary_fixed f hlo.1
  exact ⟨z, ⟨⟨f, hf⟩, hlo, hz⟩⟩

theorem mobiusLoxodromicFixedPointSet_infinite (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) : (mobiusLoxodromicFixedPointSet H).Infinite :=
  nonElementary_invariant_nonempty_infinite H hH _
    (mobiusLoxodromicFixedPointSet_nonempty H hH)
    (fun g _ hz => mobiusLoxodromicFixedPointSet_invariant H g hz)

theorem mobius_attracting_repelling_fixed_iff (f : Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (a b : Mobius.ExtendedComplex) (hd : Mobius.IsMobiusAttractingRepellingPair f a b) (z : Mobius.ExtendedComplex) :
    f.val z = z ↔ z = a ∨ z = b := by
  constructor
  · intro hz
    by_cases hza : z = a
    · exact Or.inl hza
    by_cases hzb : z = b
    · exact Or.inr hzb
    exact False.elim (hf (Mobius.mobius_eq_one_of_three_fixed f a b z hd.1 (Ne.symm hza) (Ne.symm hzb)
      hd.2.1 hd.2.2.1 hz))
  · rintro (rfl | rfl)
    · exact hd.2.1
    · exact hd.2.2.1

/-- Every nonempty closed invariant set contains all actual loxodromic endpoints. -/
theorem mobiusLimitSet_minimal (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H)
    (S : Set Mobius.ExtendedComplex) (hS : IsClosed S) (hne : S.Nonempty)
    (hinv : ∀ g : H, ∀ z ∈ S, g • z ∈ S) : mobiusLimitSet H ⊆ S := by
  apply closure_minimal _ hS
  rintro v ⟨f, hlo, hfix⟩
  obtain ⟨a, b, hd⟩ := Mobius.mobius_loxodromic_attracting_repelling f.val hlo
  have hi := nonElementary_invariant_nonempty_infinite H hH S hne hinv
  obtain ⟨w, hwS, hwab⟩ := (hi.sdiff ((Set.finite_singleton b).insert a)).nonempty
  have hwa : w ≠ a := fun he => hwab (Or.inl he)
  have hwb : w ≠ b := fun he => hwab (Or.inr he)
  have haS : a ∈ S := hS.mem_of_tendsto (hd.2.2.2.1 w hwb)
    (Eventually.of_forall fun n => hinv (f ^ n) w hwS)
  have hbS : b ∈ S := hS.mem_of_tendsto (hd.2.2.2.2 w hwa)
    (Eventually.of_forall fun n => hinv (f⁻¹ ^ n) w hwS)
  rcases (mobius_attracting_repelling_fixed_iff f.val hlo.1 a b hd v).mp hfix with rfl | rfl
  · exact haS
  · exact hbS

/-- The actual loxodromic endpoint set has no isolated points, even for nondiscrete groups. -/
theorem mobiusLoxodromicFixedPointSet_preperfect (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) : Preperfect (mobiusLoxodromicFixedPointSet H) := by
  rintro v ⟨f, hlo, hfix⟩
  obtain ⟨a, b, hd⟩ := Mobius.mobius_loxodromic_attracting_repelling f.val hlo
  obtain ⟨w, hwA, hwab⟩ := ((mobiusLoxodromicFixedPointSet_infinite H hH).sdiff
    ((Set.finite_singleton b).insert a)).nonempty
  have hwa : w ≠ a := fun he => hwab (Or.inl he)
  have hwb : w ≠ b := fun he => hwab (Or.inr he)
  have hac := (Mobius.mobius_loxodromic_orbit_accumulation hd w hwa hwb v).mpr
    ((mobius_attracting_repelling_fixed_iff f.val hlo.1 a b hd v).mp hfix)
  apply hac.mono
  apply Filter.principal_mono.mpr
  rintro z ⟨n, rfl⟩
  exact mobiusLoxodromicFixedPointSet_invariant H
    ⟨f.val ^ n, H.zpow_mem f.property n⟩ hwA

theorem mobiusLimitSet_perfect (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H) :
    Perfect (mobiusLimitSet H) := (mobiusLoxodromicFixedPointSet_preperfect H hH).perfect_closure

theorem mobiusLimitSet_nonempty (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H) :
    (mobiusLimitSet H).Nonempty :=
  (mobiusLoxodromicFixedPointSet_nonempty H hH).mono
    (mobiusLoxodromicFixedPointSet_subset_limitSet H)

local instance mobiusLimitSetChordalMetric : MetricSpace Mobius.ExtendedComplex := Mobius.complexChordalMetricSpace

theorem mobiusLimitSet_not_countable (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H) :
    ¬(mobiusLimitSet H).Countable := by
  obtain ⟨f, hmem, _, hinj⟩ := (mobiusLimitSet_perfect H hH).exists_nat_bool_injection
    (mobiusLimitSet_nonempty H hH)
  intro hc
  let : Countable (mobiusLimitSet H) := hc.to_subtype
  have hi : Function.Injective (fun x : ℕ → Bool => (⟨f x, hmem ⟨x, rfl⟩⟩ : mobiusLimitSet H)) := by
    intro x y he
    exact hinj (congrArg Subtype.val he)
  let : Countable (ℕ → Bool) := hi.countable
  obtain ⟨enumerate, henum⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n, hn⟩ := henum (fun k => !(enumerate k k))
  have he := congrFun hn n
  cases hv : enumerate n n <;> simp [hv] at he

/-- With the actual geometric subgroup and original sphere topology. -/
theorem limitSet_nonempty_closed_invariant_minimal_perfect_uncountable (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) :
    (mobiusLimitSet H).Nonempty ∧ IsClosed (mobiusLimitSet H) ∧
      (∀ g : H, (g.val : Equiv.Perm Mobius.ExtendedComplex) '' mobiusLimitSet H = mobiusLimitSet H) ∧
      (∀ S : Set Mobius.ExtendedComplex, IsClosed S → S.Nonempty →
        (∀ g : H, ∀ z ∈ S, g • z ∈ S) → mobiusLimitSet H ⊆ S) ∧
      Perfect (mobiusLimitSet H) ∧ ¬(mobiusLimitSet H).Countable :=
  ⟨mobiusLimitSet_nonempty H hH, mobiusLimitSet_isClosed H, mobiusLimitSet_image H,
    mobiusLimitSet_minimal H hH, mobiusLimitSet_perfect H hH, mobiusLimitSet_not_countable H hH⟩

/-- The endpoint set is dense in the limit set with its inherited sphere topology. -/
theorem mobiusLoxodromicFixedPointSet_denseRange (H : Subgroup Mobius.complexMobiusGroup) :
    DenseRange (fun z : mobiusLoxodromicFixedPointSet H =>
      (⟨z.val, mobiusLoxodromicFixedPointSet_subset_limitSet H z.property⟩ : mobiusLimitSet H)) := by
  intro z
  rw [closure_subtype]
  have hr : Subtype.val '' Set.range (fun z : mobiusLoxodromicFixedPointSet H =>
      (⟨z.val, mobiusLoxodromicFixedPointSet_subset_limitSet H z.property⟩ : mobiusLimitSet H)) =
      mobiusLoxodromicFixedPointSet H := by
    ext w
    constructor
    · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
      exact u.property
    · intro hw
      exact ⟨⟨w, mobiusLoxodromicFixedPointSet_subset_limitSet H hw⟩,
        ⟨⟨w, hw⟩, rfl⟩, rfl⟩
  rw [hr]
  exact z.property

/-- Countability needs the group-countability hypothesis omitted in the source paragraph. -/
theorem mobiusLoxodromicFixedPointSet_countable (H : Subgroup Mobius.complexMobiusGroup) [Countable H] :
    (mobiusLoxodromicFixedPointSet H).Countable := by
  have hc : (⋃ g : {f : H // Mobius.MobiusLoxodromic f.val},
      {z : Mobius.ExtendedComplex | g.val • z = z}).Countable := by
    apply Set.countable_iUnion
    intro g
    rcases Mobius.mobius_nonidentity_fixedPoint_dichotomy g.val.val g.property.1 with
      ⟨a, ha⟩ | ⟨a, b, _, hab⟩
    · apply (Set.countable_singleton a).mono
      intro z hz
      exact (ha z).mp hz
    · apply ((Set.countable_singleton b).insert a).mono
      intro z hz
      exact (hab z).mp hz
  apply hc.mono
  rintro z ⟨g, hg, hz⟩
  exact Set.mem_iUnion.mpr ⟨⟨g, hg⟩, hz⟩

/-- Discrete actual Möbius subgroups satisfy the corrected endpoint-countability assertion. -/
theorem discreteMobius_loxodromicFixedPointSet_countable (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) : (mobiusLoxodromicFixedPointSet H).Countable := by
  let : Countable H := Mobius.discreteMobius_countable H hH
  exact mobiusLoxodromicFixedPointSet_countable H

end
end LowDimensionalTopology.Geometry.DiscreteGroups
