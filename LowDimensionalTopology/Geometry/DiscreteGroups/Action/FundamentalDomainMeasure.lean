module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FundamentalDomain
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Tactic.Group

/-!
# Measures of fundamental sets

An exact fundamental set for a group action determines a measure-theoretic fundamental domain
when the fixed-point set of every nonidentity element is null. For a subgroup, a union of translates
indexed by left cosets provides a fundamental domain whose measure is the original measure times
the extended coset cardinal. Using `ENat.card` includes subgroups of infinite index.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Pointwise ENNReal

namespace LowDimensionalTopology.Geometry.DiscreteGroups.Action

section GenericArea

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]

/-- Exact orbit representatives form a measure-theoretic fundamental domain when the fixed-point
sets of nonidentity elements are null. -/
theorem IsFundamentalSet.measureDomain_of_fixed_null {F : Set X} {μ : Measure X}
    (hF : IsFundamentalSet G X F) (hm : NullMeasurableSet F μ)
    (hnull : ∀ g : G, g ≠ 1 → μ {x : X | g • x = x} = 0) :
    MeasureTheory.IsFundamentalDomain G F μ where
  nullMeasurableSet := hm
  ae_covers := Filter.Eventually.of_forall (IsFundamentalSet.meetsEveryOrbit G X hF)
  aedisjoint := by
    intro g k hne
    change μ ((g • F) ∩ (k • F)) = 0
    apply measure_mono_null _ (hnull (k * g⁻¹) (by
      intro he
      exact hne (mul_inv_eq_one.mp he).symm))
    intro x hx
    obtain ⟨a, ha, hga⟩ := hx.1
    obtain ⟨b, hb, hkb⟩ := hx.2
    have hab : a = b := IsFundamentalSet.eq_of_mem G X hF ha hb
      ((orbitProjection_smul G X g a).symm.trans
        ((congrArg (orbitProjection G X) (hga.trans hkb.symm)).trans
          (orbitProjection_smul G X k b)))
    subst b
    change (k * g⁻¹) • x = x
    rw [mul_smul, ← hga, inv_smul_smul]
    exact hkb.trans hga.symm

/-- The set of points with nontrivial stabilizer. -/
def actionSingularSet : Set X := ⋃ g : G, ⋃ (_ : g ≠ 1), {x : X | g • x = x}

theorem actionSingularSet_null [Countable G] {μ : Measure X}
    (hnull : ∀ g : G, g ≠ 1 → μ {x : X | g • x = x} = 0) :
    μ (actionSingularSet (G := G) (X := X)) = 0 :=
  measure_iUnion_null (fun g => measure_iUnion_null (fun hg => hnull g hg))

omit [MeasurableSpace X] in
theorem action_eq_of_not_singular {x : X} (hx : x ∉ actionSingularSet (G := G) (X := X))
    {g k : G} (he : g • x = k • x) : g = k := by
  by_contra hne
  apply hx
  refine mem_iUnion.mpr ⟨k⁻¹ * g, mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact fun h => hne (inv_mul_eq_one.mp h).symm
  · change (k⁻¹ * g) • x = x
    rw [mul_smul, he, inv_smul_smul]

/-- The inverse left-coset representative translates used for subgroup fundamental domains. -/
def subgroupTransversalPiece (K : Subgroup G) (F : Set X) (q : G ⧸ K) : Set X := q.out⁻¹ • F

/-- The union of inverse coset-representative translates of a fundamental set. -/
def subgroupTransversalSet (K : Subgroup G) (F : Set X) : Set X :=
  ⋃ q : G ⧸ K, subgroupTransversalPiece K F q

omit [MeasurableSpace X] in
theorem subgroupTransversalSet_meets (K : Subgroup G) {F : Set X}
    (hF : IsFundamentalSet G X F) : MeetsEveryOrbit K X (subgroupTransversalSet K F) := by
  intro x
  obtain ⟨g, hg⟩ := IsFundamentalSet.meetsEveryOrbit G X hF x
  let q : G ⧸ K := QuotientGroup.mk g
  have hk : q.out⁻¹ * g ∈ K := by
    apply QuotientGroup.eq.mp
    exact q.out_eq
  refine ⟨⟨q.out⁻¹ * g, hk⟩, mem_iUnion.mpr ⟨q, ?_⟩⟩
  exact ⟨g • x, hg, (mul_smul q.out⁻¹ g x).symm⟩

omit [MeasurableSpace X] in
/-- Translates of the subgroup transversal union are disjoint at points with trivial stabilizer. -/
theorem subgroupTransversalSet_disjoint_at (K : Subgroup G) {F : Set X}
    (hF : IsFundamentalSet G X F) {a b : K} (hne : a ≠ b) {x : X}
    (hx : x ∉ actionSingularSet (G := G) (X := X)) :
    x ∉ (a • subgroupTransversalSet K F) ∩ (b • subgroupTransversalSet K F) := by
  rintro ⟨⟨y, hy, hay⟩, ⟨z, hz, hbz⟩⟩
  obtain ⟨q, yF, hyF, hqy⟩ := mem_iUnion.mp hy
  obtain ⟨r, zF, hzF, hrz⟩ := mem_iUnion.mp hz
  have hqy' : q.out • ((a.val)⁻¹ • x) = yF := by
    rw [← hay]
    change q.out • (a.val⁻¹ • (a.val • y)) = yF
    rw [inv_smul_smul, ← hqy, smul_inv_smul]
  have hrz' : r.out • ((b.val)⁻¹ • x) = zF := by
    rw [← hbz]
    change r.out • (b.val⁻¹ • (b.val • z)) = zF
    rw [inv_smul_smul, ← hrz, smul_inv_smul]
  have hproj : orbitProjection G X yF = orbitProjection G X zF := by
    rw [← hqy', ← hrz']
    simp only [orbitProjection_smul]
  have he : q.out * a.val⁻¹ = r.out * b.val⁻¹ := action_eq_of_not_singular hx (by
    rw [mul_smul, mul_smul, hqy', hrz']
    exact IsFundamentalSet.eq_of_mem G X hF hyF hzF hproj)
  have hqr : q = r := by
    calc
      q = QuotientGroup.mk q.out := q.out_eq.symm
      _ = QuotientGroup.mk r.out := QuotientGroup.eq.mpr (by
        have hprod : q.out⁻¹ * r.out = a.val⁻¹ * b.val := by
          calc
            q.out⁻¹ * r.out = q.out⁻¹ * (r.out * b.val⁻¹) * b.val := by group
            _ = q.out⁻¹ * (q.out * a.val⁻¹) * b.val := by rw [he]
            _ = a.val⁻¹ * b.val := by group
        rw [hprod]
        exact K.mul_mem (K.inv_mem a.property) b.property)
      _ = r := r.out_eq
  subst r
  exact hne (Subtype.ext (inv_injective (mul_left_cancel he)))

local instance subgroupCosetCountable (K : Subgroup G) [Countable G] : Countable (G ⧸ K) :=
  (QuotientGroup.mk_surjective (s := K)).countable

/-- The coset union is a measure-theoretic fundamental domain for the subgroup. -/
theorem subgroupTransversalSet_measureDomain [Countable G] [MeasurableConstSMul G X]
    {μ : Measure X} [SMulInvariantMeasure G X μ] (K : Subgroup G) {F : Set X}
    (hF : IsFundamentalSet G X F) (hm : NullMeasurableSet F μ)
    (hnull : ∀ g : G, g ≠ 1 → μ {x : X | g • x = x} = 0) :
    MeasureTheory.IsFundamentalDomain K (subgroupTransversalSet K F) μ where
  nullMeasurableSet := NullMeasurableSet.iUnion (fun q => hm.smul q.out⁻¹)
  ae_covers := Filter.Eventually.of_forall (subgroupTransversalSet_meets K hF)
  aedisjoint := by
    intro a b hab
    apply measure_mono_null _ (actionSingularSet_null hnull)
    intro x hx
    by_contra hxs
    exact subgroupTransversalSet_disjoint_at K hF hab hxs hx

/-- Every coset contributes the same measure; the extended coset cardinal allows infinite index. -/
theorem subgroupTransversalSet_measure [Countable G] [MeasurableConstSMul G X]
    {μ : Measure X} [SMulInvariantMeasure G X μ] (K : Subgroup G) {F : Set X}
    (hF : IsFundamentalSet G X F) (hm : NullMeasurableSet F μ)
    (hnull : ∀ g : G, g ≠ 1 → μ {x : X | g • x = x} = 0) :
    μ (subgroupTransversalSet K F) = (ENat.card (G ⧸ K) : ℝ≥0∞) * μ F := by
  have hd : Pairwise (fun q r =>
      AEDisjoint μ (subgroupTransversalPiece K F q) (subgroupTransversalPiece K F r)) := by
    intro q r hqr
    apply (hF.measureDomain_of_fixed_null hm hnull).aedisjoint
    intro he
    exact hqr (Quotient.out_injective (inv_injective he))
  rw [subgroupTransversalSet, measure_iUnion₀ hd (fun q => hm.smul q.out⁻¹)]
  simp only [subgroupTransversalPiece, measure_smul, ENNReal.tsum_const]

/-- The measure of a subgroup fundamental set is multiplied by the extended coset cardinal when
nonidentity elements have null fixed-point sets. -/
theorem fundamentalSet_subgroup_index_area [Countable G] [MeasurableConstSMul G X]
    {μ : Measure X} [SMulInvariantMeasure G X μ] (K : Subgroup G) {F₀ F₁ : Set X}
    (h₀ : IsFundamentalSet K X F₀) (hm₀ : NullMeasurableSet F₀ μ)
    (h₁ : IsFundamentalSet G X F₁) (hm₁ : NullMeasurableSet F₁ μ)
    (hnull : ∀ g : G, g ≠ 1 → μ {x : X | g • x = x} = 0) :
    μ F₀ = (ENat.card (G ⧸ K) : ℝ≥0∞) * μ F₁ := by
  have hnK (k : K) (hk : k ≠ 1) : μ {x : X | k • x = x} = 0 :=
    hnull k.val (fun he => hk (Subtype.ext he))
  exact (h₀.measureDomain_of_fixed_null hm₀ hnK).measure_eq
    (subgroupTransversalSet_measureDomain K h₁ hm₁ hnull) |>.trans
      (subgroupTransversalSet_measure K h₁ hm₁ hnull)

end GenericArea

end LowDimensionalTopology.Geometry.DiscreteGroups.Action
end
