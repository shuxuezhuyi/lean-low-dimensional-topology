/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.LimitSets
public import LowDimensionalTopology.Geometry.Mobius.Topology.MobiusOmittedValues
public import Mathlib.Basic.Denumerable
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteMobiusGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusLocalDomains
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusDiscTrapping
@[expose] public section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
noncomputable section
local instance mobiusOrbitLimitChordalMetric : MetricSpace Mobius.ExtendedComplex := Mobius.complexChordalMetricSpace

/-- The orbit limit uses distinct group elements, although their orbit values may repeat. -/
def mobiusOrbitLimitSet (H : Subgroup Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex) : Set
    Mobius.ExtendedComplex :=
  {w | ∃ u : ℕ → H, Function.Injective u ∧ Tendsto (fun n => u n • z) atTop (𝓝 w)}

/-- An enumeration of a countably infinite group characterizes orbit limits by cluster points. -/
theorem mobiusOrbitLimitSet_iff_cluster_enumeration (H : Subgroup Mobius.complexMobiusGroup)
    (z w : Mobius.ExtendedComplex) (e : ℕ ≃ H) :
    w ∈ mobiusOrbitLimitSet H z ↔ MapClusterPt w atTop (fun n => e n • z) := by
  constructor
  · rintro ⟨u, hu, ht⟩
    have hi : Function.Injective (fun n => e.symm (u n)) := e.symm.injective.comp hu
    apply MapClusterPt.of_comp hi.nat_tendsto_atTop
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using ht.mapClusterPt
  · intro hw
    obtain ⟨k, hk, ht⟩ := hw.tendsto_subseq
    exact ⟨e ∘ k, e.injective.comp hk.injective, ht⟩

theorem mobiusOrbitLimitSet_isClosed (H : Subgroup Mobius.complexMobiusGroup)
    [Countable H] [Infinite H] (z : Mobius.ExtendedComplex) : IsClosed (mobiusOrbitLimitSet H z) := by
  obtain ⟨e⟩ := (inferInstance : Nonempty (ℕ ≃ H))
  have he : mobiusOrbitLimitSet H z = {w | MapClusterPt w atTop (fun n => e n • z)} := by
    ext w
    exact mobiusOrbitLimitSet_iff_cluster_enumeration H z w e
  rw [he]
  exact isClosed_setOfPred_clusterPt

theorem mobiusOrbitLimitSet_nonempty (H : Subgroup Mobius.complexMobiusGroup)
    [Infinite H] (z : Mobius.ExtendedComplex) : (mobiusOrbitLimitSet H z).Nonempty := by
  let e : ℕ ↪ H := Infinite.natEmbedding H
  obtain ⟨w, k, hk, ht⟩ := CompactSpace.tendsto_subseq (fun n => e n • z)
  exact ⟨w, e ∘ k, e.injective.comp hk.injective, ht⟩

theorem mobiusOrbitLimitSet_invariant (H : Subgroup Mobius.complexMobiusGroup) (h : H)
    (z : Mobius.ExtendedComplex) {w : Mobius.ExtendedComplex} (hw : w ∈ mobiusOrbitLimitSet H z) :
    h • w ∈ mobiusOrbitLimitSet H z := by
  obtain ⟨u, hu, ht⟩ := hw
  refine ⟨fun n => h * u n, ?_, ?_⟩
  · intro m n he
    exact hu (mul_left_cancel he)
  · have hc := (Mobius.mobiusBoundaryHomeomorph h.val).continuous.continuousAt.tendsto.comp ht
    change Tendsto (fun n => h • (u n • z)) atTop (𝓝 (h • w)) at hc
    simpa only [mul_smul] using hc

/-- For an initial point in the closed invariant limit set, every orbit limit stays there. -/
theorem mobiusOrbitLimitSet_subset_of_mem_limitSet (H : Subgroup Mobius.complexMobiusGroup)
    {z : Mobius.ExtendedComplex} (hz : z ∈ mobiusLimitSet H) : mobiusOrbitLimitSet H z ⊆ mobiusLimitSet H := by
  rintro w ⟨u, _, ht⟩
  exact (mobiusLimitSet_isClosed H).mem_of_tendsto ht
    (Eventually.of_forall fun n => mobiusLimitSet_invariant H (u n) hz)

/-- The actual non-elementary subgroup is infinite. -/
theorem nonElementary_infinite (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H) :
    Infinite H := by
  obtain ⟨a, ha, _⟩ := exists_injective_loxodromic_sequence_pairwise_disjoint_fixedPoints H hH
  exact Infinite.of_injective a ha

/-- Minimality puts the limit set into every orbit-limit set of a countable subgroup. -/
theorem mobiusLimitSet_subset_orbitLimitSet (H : Subgroup Mobius.complexMobiusGroup)
    [Countable H] (hH : IsNonElementary H) (z : Mobius.ExtendedComplex) :
    mobiusLimitSet H ⊆ mobiusOrbitLimitSet H z := by
  let : Infinite H := nonElementary_infinite H hH
  exact mobiusLimitSet_minimal H hH _ (mobiusOrbitLimitSet_isClosed H z)
    (mobiusOrbitLimitSet_nonempty H z) (fun g _ hw => mobiusOrbitLimitSet_invariant H g z hw)

/-- The first branch of needs only group countability. -/
theorem mobiusOrbitLimitSet_eq_of_mem_limitSet (H : Subgroup Mobius.complexMobiusGroup)
    [Countable H] (hH : IsNonElementary H) {z : Mobius.ExtendedComplex} (hz : z ∈ mobiusLimitSet H) :
    mobiusOrbitLimitSet H z = mobiusLimitSet H :=
  Set.Subset.antisymm (mobiusOrbitLimitSet_subset_of_mem_limitSet H hz)
    (mobiusLimitSet_subset_orbitLimitSet H hH z)

/-- Fixed left composition preserves divergence of the actual normalized matrix norms. -/
theorem mobiusNormalizedNorm_left_mul_tendsto (q : Mobius.complexMobiusGroup)
    (f : ℕ → Mobius.complexMobiusGroup)
    (hf : Tendsto (fun n => Mobius.mobiusNormalizedNorm (f n)) atTop atTop) :
    Tendsto (fun n => Mobius.mobiusNormalizedNorm (q * f n)) atTop atTop := by
  have hc : 0 < Mobius.mobiusNormalizedNorm q⁻¹ + 1 := by linarith [mobiusNormalizedNorm_nonneg q⁻¹]
  apply tendsto_atTop_mono _ (hf.atTop_div_const hc)
  intro n
  apply (div_le_iff₀ hc).mpr
  have hm := mobiusNormalizedNorm_mul_le q⁻¹ (q * f n)
  simp only [inv_mul_cancel_left] at hm
  nlinarith [mobiusNormalizedNorm_nonneg (q * f n)]

/-- Two omitted sphere values turn one orbit limit into uniform convergence on a compact set. -/
theorem mobius_omitted_pair_eventually_mapsTo
    {D K V : Set Mobius.ExtendedComplex} (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (a b : Mobius.ExtendedComplex) (hab : a ≠ b) (f : ℕ → Mobius.complexMobiusGroup)
    (homit : ∀ n, ∀ z ∈ D, (f n).val z ≠ a ∧ (f n).val z ≠ b)
    (hnorm : Tendsto (fun n => Mobius.mobiusNormalizedNorm (f n)) atTop atTop)
    (z : Mobius.ExtendedComplex) (hz : z ∈ K) (w : Mobius.ExtendedComplex)
    (hw : Tendsto (fun n => (f n).val z) atTop (𝓝 w)) (hV : IsOpen V) (hwV : w ∈ V) :
    ∀ᶠ n in atTop, (f n).val '' K ⊆ V := by
  obtain ⟨q, hqa, hqb⟩ := mobius_exists_send_pair_zero_infty a b hab
  let F : ℕ → Mobius.complexMobiusGroup := fun n => q * f n
  have hF : ∀ n, ∀ z ∈ D, (F n).val z ≠ ((0 : ℂ) : Mobius.ExtendedComplex) ∧ (F n).val z ≠ ∞ := by
    intro n x hx
    constructor
    · intro he
      apply (homit n x hx).1
      apply q.val.injective
      exact he.trans hqa.symm
    · intro he
      apply (homit n x hx).2
      apply q.val.injective
      exact he.trans hqb.symm
  have hd := Mobius.mobius_omitted_values_diameter_tendsto_zero hD hK hKD F hF
    (mobiusNormalizedNorm_left_mul_tendsto q f hnorm)
  have ht : Tendsto (fun n => (F n).val z) atTop (𝓝 (q.val w)) :=
    (Mobius.mobiusBoundaryHomeomorph q).continuous.continuousAt.tendsto.comp hw
  have hqV : IsOpen (q.val '' V) := (Mobius.mobiusBoundaryHomeomorph q).isOpenMap V hV
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hqV (q.val w) ⟨w, hwV, rfl⟩
  have he2 : 0 < ε / 2 := half_pos hε
  have hdiam : ∀ᶠ n in atTop, Mobius.complexChordalDiameter ((F n).val '' K) < ε / 2 :=
    hd.eventually (gt_mem_nhds he2)
  have hanchor : ∀ᶠ n in atTop, dist ((F n).val z) (q.val w) < ε / 2 :=
    (Metric.tendsto_nhds.mp ht) _ he2
  filter_upwards [hdiam, hanchor] with n hn hm
  rintro y ⟨x, hx, rfl⟩
  have hbound : dist ((F n).val x) ((F n).val z) ≤
      Mobius.complexChordalDiameter ((F n).val '' K) :=
    Metric.dist_le_diam_of_mem ((hK.image (Mobius.continuous_mobiusBoundary (F n))).isBounded)
      ⟨x, hx, rfl⟩ ⟨z, hz, rfl⟩
  have hin : (F n).val x ∈ q.val '' V := by
    apply hball
    change dist ((F n).val x) (q.val w) < ε
    exact lt_of_le_of_lt (dist_triangle _ _ _) (by linarith)
  obtain ⟨y, hy, he⟩ := hin
  have heq : y = (f n).val x := q.val.injective he
  rwa [← heq]


/-- The ordinary-set branch of the orbit-limit theorem reduces to the exact round-disc trapping lemma. -/
theorem mobiusOrbitLimitSet_subset_limitSet_of_disc_trapping
    (htrap : ∀ (D : Set Mobius.ExtendedComplex) (f : Mobius.complexMobiusGroup),
      Mobius.IsComplexOpenDisc D → f.val '' closure D ⊆ D →
      ∃ v ∈ D, Mobius.MobiusLoxodromic f ∧ f.val v = v)
    (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (z : Mobius.ExtendedComplex) :
    mobiusOrbitLimitSet H z ⊆ mobiusLimitSet H := by
  by_cases hz : z ∈ mobiusLimitSet H
  · exact mobiusOrbitLimitSet_subset_of_mem_limitSet H hz
  intro w hw
  by_contra hwL
  obtain ⟨u, hu, ht⟩ := hw
  obtain ⟨f, hfH, hfL⟩ := nonElementary_exists_loxodromic H hH
  obtain ⟨a, b, hp⟩ := Mobius.mobius_loxodromic_attracting_repelling f hfL
  have haL : a ∈ mobiusLimitSet H :=
    mobiusLoxodromicFixedPointSet_subset_limitSet H ⟨⟨f, hfH⟩, hfL, hp.2.1⟩
  have hbL : b ∈ mobiusLimitSet H :=
    mobiusLoxodromicFixedPointSet_subset_limitSet H ⟨⟨f, hfH⟩, hfL, hp.2.2.1⟩
  obtain ⟨b', hb'⟩ := exists_ne w
  obtain ⟨q, hqw, _⟩ := mobius_exists_send_pair_zero_infty w b' (Ne.symm hb')
  obtain ⟨r, hr, hDr, hwD, hcl⟩ := mobiusNormalizedDisc_closure_basis q w hqw
    (mobiusOrdinarySet H) (mobiusOrdinarySet_isOpen H) hwL
  let D := mobiusNormalizedDisc q r
  let K := insert z (closure D)
  have hK : IsCompact K := isClosed_closure.isCompact.insert z
  have hKD : K ⊆ mobiusOrdinarySet H := by
    intro x hx
    rcases hx with rfl | hx
    · exact hz
    · exact hcl hx
  have homit : ∀ n, ∀ x ∈ mobiusOrdinarySet H,
      (u n).val.val x ≠ a ∧ (u n).val.val x ≠ b := by
    intro n x hx
    have ho := mobiusOrdinarySet_invariant H (u n) hx
    constructor
    · intro he
      apply ho
      change (u n).val.val x ∈ mobiusLimitSet H
      rw [he]
      exact haL
    · intro he
      apply ho
      change (u n).val.val x ∈ mobiusLimitSet H
      rw [he]
      exact hbL
  have hev := mobius_omitted_pair_eventually_mapsTo (mobiusOrdinarySet_isOpen H) hK hKD
    a b hp.1 (fun n => (u n).val) homit
    (Mobius.discreteMobius_injective_sequence_norm_tendsto H hd u hu)
    z (Set.mem_insert _ _) w ht hDr.isOpen hwD
  obtain ⟨n, hn⟩ := hev.exists
  have htrapD : (u n).val.val '' closure D ⊆ D :=
    (Set.image_mono (Set.subset_insert z (closure D))).trans hn
  obtain ⟨v, hv, hlo, hfix⟩ := htrap D (u n).val hDr htrapD
  have hvL := mobiusLoxodromicFixedPointSet_subset_limitSet H ⟨u n, hlo, hfix⟩
  exact hcl (subset_closure hv) hvL

/-- Every open ambient sphere domain satisfying the compact-hit condition lies in the ordinary set. -/
theorem mobius_discontinuous_open_subset_ordinary (H : Subgroup Mobius.complexMobiusGroup)
    (D : Set Mobius.ExtendedComplex) (hD : IsOpen D) (hdisc : IsMobiusDiscontinuousOn H D) :
    D ⊆ mobiusOrdinarySet H := by
  intro z hz hzL
  have hzcl : z ∈ closure (mobiusLoxodromicFixedPointSet H) := hzL
  obtain ⟨w, hwD, hwA⟩ := mem_closure_iff.mp hzcl D hD hz
  obtain ⟨g, hlo, hfix⟩ := hwA
  exact not_discontinuous_on_set_containing_parabolic_or_loxodromic_fixedPoint H D g (Or.inr hlo) w hwD hfix hdisc

/-- Uniform two-value contraction and the orbit-limit characterization imply ordinary discontinuity. -/
theorem mobius_ordinary_discontinuous_of_orbit_limit_subset
    (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H)
    (hd : Mobius.IsDiscreteMobiusSubgroup H)
    (hsub : ∀ z : Mobius.ExtendedComplex, mobiusOrbitLimitSet H z ⊆ mobiusLimitSet H) :
    IsMobiusDiscontinuousOn H (mobiusOrdinarySet H) := by
  intro K hK hKO
  by_contra hfinite
  let T : Set H := {g : H | (g.val.val '' K ∩ K).Nonempty}
  have hT : T.Infinite := hfinite
  let e : ℕ ↪ T := hT.natEmbedding
  let u : ℕ → H := fun n => (e n).val
  have hui : Function.Injective u := Subtype.val_injective.comp e.injective
  obtain ⟨z, _, hzK⟩ := (e 0).property
  obtain ⟨w, k, hk, ht⟩ := CompactSpace.tendsto_subseq (fun n => (u n).val.val z)
  let v : ℕ → H := u ∘ k
  have hvi : Function.Injective v := hui.comp hk.injective
  have hwL : w ∈ mobiusLimitSet H := hsub z ⟨v, hvi, ht⟩
  have hwK : w ∉ K := fun hh => hKO hh hwL
  obtain ⟨f, hfH, hfL⟩ := nonElementary_exists_loxodromic H hH
  obtain ⟨a, b, hp⟩ := Mobius.mobius_loxodromic_attracting_repelling f hfL
  have haL : a ∈ mobiusLimitSet H :=
    mobiusLoxodromicFixedPointSet_subset_limitSet H ⟨⟨f, hfH⟩, hfL, hp.2.1⟩
  have hbL : b ∈ mobiusLimitSet H :=
    mobiusLoxodromicFixedPointSet_subset_limitSet H ⟨⟨f, hfH⟩, hfL, hp.2.2.1⟩
  have homit : ∀ n, ∀ x ∈ mobiusOrdinarySet H,
      (v n).val.val x ≠ a ∧ (v n).val.val x ≠ b := by
    intro n x hx
    have ho := mobiusOrdinarySet_invariant H (v n) hx
    constructor
    · intro he
      apply ho
      change (v n).val.val x ∈ mobiusLimitSet H
      rwa [he]
    · intro he
      apply ho
      change (v n).val.val x ∈ mobiusLimitSet H
      rwa [he]
  have hev := mobius_omitted_pair_eventually_mapsTo (mobiusOrdinarySet_isOpen H) hK hKO
    a b hp.1 (fun n => (v n).val) homit
    (Mobius.discreteMobius_injective_sequence_norm_tendsto H hd v hvi)
    z hzK w ht hK.isClosed.isOpen_compl hwK
  obtain ⟨n, hn⟩ := hev.exists
  obtain ⟨y, hyI, hyK⟩ := (e (k n)).property
  exact hn hyI hyK

/-- Minimality also puts the limit set in the closure of each actual boundary orbit. -/
theorem mobiusLimitSet_subset_closure_orbit (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (z : Mobius.ExtendedComplex) :
    mobiusLimitSet H ⊆ closure (MulAction.orbit H z) := by
  apply mobiusLimitSet_minimal H hH _ isClosed_closure
    ⟨z, subset_closure (MulAction.mem_orbit_self z)⟩
  intro h w hw
  have hm : MapsTo (fun x : Mobius.ExtendedComplex => h • x) (MulAction.orbit H z)
      (MulAction.orbit H z) := by
    rintro x ⟨g, rfl⟩
    exact ⟨h * g, mul_smul h g z⟩
  exact hm.closure (Mobius.continuous_mobiusBoundary h.val) hw

/-- The nondense-orbit corollary in fact does not require the source's discreteness hypothesis. -/
theorem mobius_ordinary_nonempty_iff_exists_nondense_orbit
    (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H) :
    (mobiusOrdinarySet H).Nonempty ↔ ∃ z : Mobius.ExtendedComplex, ¬Dense (MulAction.orbit H z) := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨z, hz⟩ := mobiusLimitSet_nonempty H hH
    refine ⟨z, fun hdense => ?_⟩
    have hsub : MulAction.orbit H z ⊆ mobiusLimitSet H := by
      rintro x ⟨g, rfl⟩
      exact mobiusLimitSet_invariant H g hz
    exact hw ((closure_minimal hsub (mobiusLimitSet_isClosed H)) (hdense w))
  · rintro ⟨z, hn⟩
    by_contra hempty
    apply hn
    intro w
    apply mobiusLimitSet_subset_closure_orbit H hH z
    by_contra hw
    exact hempty ⟨w, hw⟩

/-- The current convention identifies a Kleinian group with a discrete actual Mobius subgroup. -/
def IsKleinianGroup (H : Subgroup Mobius.complexMobiusGroup) : Prop := Mobius.IsDiscreteMobiusSubgroup H

/-- The historical convention additionally requires a nonempty ordinary set. -/
def IsClassicalKleinianGroup (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  Mobius.IsDiscreteMobiusSubgroup H ∧ (mobiusOrdinarySet H).Nonempty

/-- A parabolic fixed point lies in the limit set of every non-elementary containing subgroup. -/
theorem mobius_parabolic_fixed_mem_limitSet (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (g : H) (hg : Mobius.MobiusParabolic g.val)
    (z : Mobius.ExtendedComplex) (hz : g.val.val z = z) : z ∈ mobiusLimitSet H := by
  obtain ⟨a, ha, ht⟩ := Mobius.mobius_parabolic_iterates_tendsto g.val hg
  obtain ⟨w, hw⟩ := mobiusLimitSet_nonempty H hH
  have haL : a ∈ mobiusLimitSet H := (mobiusLimitSet_isClosed H).mem_of_tendsto (ht w)
    (Eventually.of_forall fun n => mobiusLimitSet_invariant H (g ^ n) hw)
  obtain ⟨b, hb⟩ := hg.2
  have hza : z = a := ((hb z).mp hz).trans ((hb a).mp ha).symm
  rwa [hza]

/-- The parabolic/loxodromic fixed-point assertion does not need discreteness. -/
theorem mobius_parabolic_or_loxodromic_fixed_mem_limitSet (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (g : H) (hg : Mobius.MobiusParabolic g.val ∨ Mobius.MobiusLoxodromic g.val)
    (z : Mobius.ExtendedComplex) (hz : g.val.val z = z) : z ∈ mobiusLimitSet H := by
  rcases hg with hp | hl
  · exact mobius_parabolic_fixed_mem_limitSet H hH g hp z hz
  · exact mobiusLoxodromicFixedPointSet_subset_limitSet H ⟨g, hl, hz⟩

/-- Every accumulation along distinct elements belongs to the true limit set. -/
theorem mobiusOrbitLimitSet_subset_limitSet (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (hd : Mobius.IsDiscreteMobiusSubgroup H) (z : Mobius.ExtendedComplex) :
    mobiusOrbitLimitSet H z ⊆ mobiusLimitSet H :=
  mobiusOrbitLimitSet_subset_limitSet_of_disc_trapping mobius_disc_trapping_fixed_point H hH hd z

/-- preserving the source's distinct-group-elements convention. -/
theorem limitSet_eq_orbitLimitSet (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (hd : Mobius.IsDiscreteMobiusSubgroup H) (z : Mobius.ExtendedComplex) :
    mobiusLimitSet H = mobiusOrbitLimitSet H z := by
  let : Countable H := Mobius.discreteMobius_countable H hd
  exact Set.Subset.antisymm (mobiusLimitSet_subset_orbitLimitSet H hH z)
    (mobiusOrbitLimitSet_subset_limitSet H hH hd z)

/-- The actual compact-hit discontinuity statement on the open ordinary set. -/
theorem mobius_ordinary_discontinuous (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (hd : Mobius.IsDiscreteMobiusSubgroup H) :
    IsMobiusDiscontinuousOn H (mobiusOrdinarySet H) :=
  mobius_ordinary_discontinuous_of_orbit_limit_subset H hH hd
    (mobiusOrbitLimitSet_subset_limitSet H hH hd)

/-- The ordinary set is a domain of discontinuity and is maximal among all open ambient domains of discontinuity, including non-invariant ones. -/
theorem ordinarySet_discontinuous_and_maximal_open_domain (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (hd : Mobius.IsDiscreteMobiusSubgroup H) :
    IsMobiusDiscontinuousOn H (mobiusOrdinarySet H) ∧
      ∀ D : Set Mobius.ExtendedComplex, IsOpen D → IsMobiusDiscontinuousOn H D →
        D ⊆ mobiusOrdinarySet H :=
  ⟨mobius_ordinary_discontinuous H hH hd, mobius_discontinuous_open_subset_ordinary H⟩

end
end LowDimensionalTopology.Geometry.DiscreteGroups
