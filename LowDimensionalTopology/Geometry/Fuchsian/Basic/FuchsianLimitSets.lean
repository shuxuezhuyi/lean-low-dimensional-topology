/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianStabilizers
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.MobiusOrbitLimits
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Include parabolic endpoints when extending the definition to elementary groups. -/
def fuchsianLimitEndpoints (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  {z | ∃ g : H, (_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val ∨
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic g.val) ∧ g.val.val z = z}

/-- The full endpoint-closure limit set, agreeing for non-elementary groups. -/
def fuchsianLimitSet (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  closure (fuchsianLimitEndpoints H)

theorem fuchsianLimitSet_eq_nonElementary (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) : fuchsianLimitSet H = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet_isClosed H)
    rintro z ⟨g, hp | hl, hz⟩
    · exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_fixed_mem_limitSet H hH g hp z hz
    · exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLoxodromicFixedPointSet_subset_limitSet H ⟨g,
      hl, hz⟩
  · apply closure_mono
    rintro z ⟨g, hl, hz⟩
    exact ⟨g, Or.inr hl, hz⟩

/-- The full limit-set assertion, with elementary parabolic groups included. -/
theorem FuchsianDisc.limitSet_subset_frontier {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : fuchsianLimitSet H ⊆ frontier D.carrier := by
  apply closure_minimal _ isClosed_frontier
  rintro z ⟨g, hp | hl, hz⟩
  · exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_fixed_mem_disc_frontier g.val hp D.isDisc (D.image_eq g) hz
  · exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier g.val (D.loxodromic_hyperbolic g hl)
      D.isDisc (D.image_eq g) hz

/-- Finite groups have empty limit set in the full convention as well. -/
theorem fuchsianLimitSet_of_finite (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H] :
    fuchsianLimitSet H = ∅ := by
  have he : fuchsianLimitEndpoints H = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨g, hg, _⟩
    have ho : IsOfFinOrder g.val := by
      obtain ⟨n,hn,he⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,congrArg Subtype.val he⟩
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder g.val hg ho
  rw [fuchsianLimitSet, he, closure_empty]

/-- The elementary parabolic limit set is exactly its common fixed point. -/
theorem fuchsianLimitSet_of_elementary_parabolic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hpH : p ∈ H) (hp :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic p) :
    ∃ a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, fuchsianLimitSet H = {a} ∧ ∀ f : H, f.val.val a = a := by
  obtain ⟨a, ha, hall⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.elementary_parabolic_common_fixedPoint H hE p hpH hp
  have hno := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elementary_parabolic_no_loxodromic H hd hE p hpH hp
  have hsub : fuchsianLimitEndpoints H ⊆ {a} := by
    rintro z ⟨g, hg | hg, hz⟩
    · obtain ⟨b, hb⟩ := hg.2
      exact ((hb z).mp hz).trans ((hb a).mp (hall g)).symm
    · exact False.elim (hno g.val g.property hg)
  refine ⟨a, Set.Subset.antisymm (closure_minimal hsub isClosed_singleton) ?_, hall⟩
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact subset_closure ⟨⟨p, hpH⟩, Or.inl hp, (ha a).mpr rfl⟩

/-- A loxodromic member of an elementary discrete group fixes both points of any invariant pair. -/
theorem elementary_invariant_pair_fixed_by_loxodromic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (a b : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hp : ∀ f : H, f.val.val '' ({a,b} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = {a,b})
    (g : H) (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic g.val) : g.val.val a = a ∧ g.val.val b = b := by
  have hOrbit (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz : z ∈ ({a,b} : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
      (MulAction.orbit H z).Finite := by
    apply (Set.toFinite ({a,b} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)).subset
    rintro w ⟨f, rfl⟩
    rw [← hp f]
    exact ⟨z, hz, rfl⟩
  exact ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.finite_boundary_orbit_fixed_by_loxodromic H g.val g.property hg a (hOrbit a (by simp)),
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.finite_boundary_orbit_fixed_by_loxodromic H g.val g.property hg b (hOrbit b (by simp))⟩

/-- Two distinct fixed points exhaust the fixed set of a nonidentity actual Mobius map. -/
theorem fuchsian_fixedPoints_subset_pair (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g
  ≠ 1)
    (a b : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hab : a ≠ b) (ha : g.val a = a) (hb : g.val b
      = b)
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz : g.val z = z) : z ∈ ({a,b} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  by_contra hn
  have hza : z ≠ a := fun he => hn (by simp [he])
  have hzb : z ≠ b := fun he => hn (by simp [he])
  exact hg (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_one_of_three_fixed g a b z hab hza.symm hzb.symm ha
    hb hz)

/-- The elementary loxodromic limit set is exactly the invariant endpoint pair. -/
theorem fuchsianLimitSet_of_elementary_loxodromic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hpH : p ∈ H) (hp :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic p) :
    ∃ a b : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, a ≠ b ∧ fuchsianLimitSet H = {a,b} := by
  obtain ⟨a,b,hab,hpa,hpb,hpair⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elementary_loxodromic_fixed_pair H hd hE p hpH hp
  have hno := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elementary_loxodromic_structure H hd hE p
    hpH hp).2
  have hsub : fuchsianLimitEndpoints H ⊆ ({a,b} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rintro z ⟨g, hg | hg, hz⟩
    · exact False.elim (hno g.val g.property hg)
    · obtain ⟨hga,hgb⟩ := elementary_invariant_pair_fixed_by_loxodromic H a b hpair g hg
      exact fuchsian_fixedPoints_subset_pair g.val hg.1 a b hab hga hgb z hz
  refine ⟨a,b,hab,Set.Subset.antisymm (closure_minimal hsub (Set.toFinite _).isClosed) ?_⟩
  rintro z (rfl | hz)
  · exact subset_closure ⟨⟨p,hpH⟩, Or.inr hp, hpa⟩
  · rw [Set.mem_singleton_iff] at hz
    subst z
    exact subset_closure ⟨⟨p,hpH⟩, Or.inr hp, hpb⟩

/-- Every elementary discrete limit set is contained in a pair, with singleton and empty cases retained. -/
theorem elementary_fuchsianLimitSet_subset_pair (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) :
    ∃ a b : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, fuchsianLimitSet H ⊆ {a,b} := by
  by_cases hP : ∃ p ∈ H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic p
  · obtain ⟨p,hpH,hp⟩ := hP
    obtain ⟨a,ha,_⟩ := fuchsianLimitSet_of_elementary_parabolic H hd hE p hpH hp
    exact ⟨a,a,by rw [ha]; simp⟩
  by_cases hL : ∃ p ∈ H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic p
  · obtain ⟨p,hpH,hp⟩ := hL
    obtain ⟨a,b,_,hab⟩ := fuchsianLimitSet_of_elementary_loxodromic H hd hE p hpH hp
    exact ⟨a,b,by rw [hab]⟩
  have hall : ∀ f ∈ H, f ≠ 1 → _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f := by
    intro f hf hn
    rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy f hn with hp | hl | he
    · exact False.elim (hP ⟨f,hf,hp⟩)
    · exact False.elim (hL ⟨f,hf,hl⟩)
    · exact he
  obtain ⟨q,hq⟩ := (_root_.LowDimensionalTopology.Geometry.Mobius.all_nonidentity_elliptic_iff_common_halfSpace_fixedPoint H).mp hall
  let : Finite H := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_finite_of_common_H3_fixed H hd q hq
  exact ⟨(0 : ℂ),∞,by rw [fuchsianLimitSet_of_finite]; exact Set.empty_subset _⟩

/-- The first kind fills the actual frontier of the chosen invariant disc. -/
def FuchsianDisc.IsFirstKind {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) : Prop :=
  fuchsianLimitSet H = frontier D.carrier

/-- The second kind occupies a proper subset of that actual frontier. -/
def FuchsianDisc.IsSecondKind {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) : Prop :=
  fuchsianLimitSet H ⊂ frontier D.carrier

/-- A genuine disc frontier cannot be contained in any two-point set. -/
theorem complexDisc_frontier_not_subset_pair {D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD
  : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (a b : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : ¬frontier D ⊆ ({a,b} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  obtain ⟨q,_,hq⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.complexDisc_frontier_normalize hD
  have hmem (z : ℂ) (hz : ‖z‖ = 1) : q.val.symm (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ frontier D := by
    have hm : (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ q.val '' frontier D := by
      rw [hq]
      simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe, sub_zero] using hz
    obtain ⟨v,hv,hvz⟩ := hm
    have he : v = q.val.symm (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := q.val.eq_symm_apply.mpr hvz
    rwa [← he]
  have h12 : q.val.symm ((1 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ≠ q.val.symm ((-1 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    intro he
    have h := OnePoint.coe_injective (q.val.symm.injective he)
    norm_num at h
  have h13 : q.val.symm ((1 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ≠ q.val.symm (Complex.I : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    intro he
    have h := OnePoint.coe_injective (q.val.symm.injective he)
    norm_num [Complex.ext_iff] at h
  have h23 : q.val.symm ((-1 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ≠ q.val.symm (Complex.I : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    intro he
    have h := OnePoint.coe_injective (q.val.symm.injective he)
    norm_num [Complex.ext_iff] at h
  intro hsub
  have h1 := hsub (hmem 1 (by simp))
  have h2 := hsub (hmem (-1) (by simp))
  have h3 := hsub (hmem Complex.I (by simp))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2 h3
  aesop

/-- The first-or-second-kind dichotomy is exhaustive. -/
theorem FuchsianDisc.first_or_second_kind {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) :
    D.IsFirstKind ∨ D.IsSecondKind := by
  by_cases h : frontier D.carrier ⊆ fuchsianLimitSet H
  · exact Or.inl (Set.Subset.antisymm D.limitSet_subset_frontier h)
  · exact Or.inr ⟨D.limitSet_subset_frontier, h⟩

/-- Every elementary Fuchsian group is of the second kind in the full limit-set convention. -/
theorem FuchsianDisc.elementary_isSecondKind {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) : D.IsSecondKind := by
  obtain ⟨a,b,hab⟩ := elementary_fuchsianLimitSet_subset_pair H D.discrete hE
  exact ⟨D.limitSet_subset_frontier, fun h =>
    complexDisc_frontier_not_subset_pair D.isDisc a b (h.trans hab)⟩

end LowDimensionalTopology.Geometry.Fuchsian
