module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Basic
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
@[expose] public section
noncomputable section
open Set Filter Topology
open scoped Pointwise OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual closed tiles are indexed by the original Fuchsian group elements. -/
def fuchsianDomainTile {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (g : H) : Set P.domain.carrier := g • closure D

theorem fuchsianDomainTile_closed {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (g : H) : IsClosed (fuchsianDomainTile P D g) :=
  (Homeomorph.smul g).isClosedMap _ isClosed_closure

/-- genuine closed tiles meet every compact set only finitely often. -/
structure IsLocallyFiniteFuchsianDomain {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) : Prop where
  fundamental : IsFuchsianFundamentalDomain P D
  compact_hits_finite : ∀ K : Set P.domain.carrier, IsCompact K →
    {g : H | (fuchsianDomainTile P D g ∩ K).Nonempty}.Finite

/-- The source compact-set definition implies the standard neighborhood definition. -/
theorem IsLocallyFiniteFuchsianDomain.locallyFinite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) : LocallyFinite (fuchsianDomainTile P D) := by
  intro x
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  exact ⟨K, hxK, hD.compact_hits_finite K hK⟩

/-- Both standard formulations of local finiteness agree in the genuine hyperbolic plane. -/
theorem isLocallyFiniteFuchsianDomain_iff {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    IsLocallyFiniteFuchsianDomain P D ↔
      IsFuchsianFundamentalDomain P D ∧ LocallyFinite (fuchsianDomainTile P D) := by
  exact ⟨fun h => ⟨h.fundamental, h.locallyFinite⟩,
    fun ⟨hf, hl⟩ => ⟨hf, fun _ hK => hl.finite_nonempty_inter_compact hK⟩⟩

/-- At every actual point there are only finitely many incident closed tiles. -/
theorem IsLocallyFiniteFuchsianDomain.incident_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (x : P.domain.carrier) :
    {g : H | x ∈ fuchsianDomainTile P D g}.Finite := hD.locallyFinite.point_finite x

/-- A finite neighborhood star, with every participating tile incident to x. -/
theorem IsLocallyFiniteFuchsianDomain.finite_neighborhood_star {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (x : P.domain.carrier) :
    ∃ N : Set P.domain.carrier, IsCompact N ∧ N ∈ 𝓝 x ∧
      {g : H | x ∈ fuchsianDomainTile P D g}.Finite ∧
      N ⊆ ⋃ g ∈ {g : H | x ∈ fuchsianDomainTile P D g}, fuchsianDomainTile P D g ∧
      ∀ g : H, x ∉ fuchsianDomainTile P D g → Disjoint N (fuchsianDomainTile P D g) := by
  have hN := hD.locallyFinite.iInter_compl_mem_nhds (fuchsianDomainTile_closed P D) x
  obtain ⟨N, hNx, hNsub, hNc⟩ := LocallyCompactSpace.local_compact_nhds x _ hN
  have hd (g : H) (hg : x ∉ fuchsianDomainTile P D g) :
      Disjoint N (fuchsianDomainTile P D g) := Set.disjoint_left.mpr (fun z hz hzg =>
        (mem_iInter₂.mp (hNsub hz) g hg) hzg)
  refine ⟨N, hNc, hNx, hD.incident_finite x, ?_, hd⟩
  intro y hy
  have hcov := hD.fundamental.closure_cover
  have hym : y ∈ ⋃ g : H, fuchsianDomainTile P D g := by
    change y ∈ ⋃ g : H, (fun z : P.domain.carrier => g • z) '' closure D
    rw [hcov]
    trivial
  obtain ⟨g, hgy⟩ := mem_iUnion.mp hym
  have hxg : x ∈ fuchsianDomainTile P D g := by
    by_contra hg
    exact Set.disjoint_left.mp (hd g hg) hy hgy
  exact mem_iUnion₂.mpr ⟨g, hxg, hgy⟩

/-- Under local finiteness the native comparison map is closed. -/
theorem IsLocallyFiniteFuchsianDomain.comparison_isClosedMap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) : IsClosedMap (fuchsianDomainComparisonMap P D) := by
  intro C hC
  let S : Set P.domain.carrier := (Subtype.val : closure D → P.domain.carrier) ''
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedProjection H P.domain.carrier (closure D))
      ⁻¹' C)
  have hS : IsClosed S := isClosed_closure.isClosedEmbedding_subtypeVal.isClosedMap _
    (hC.preimage (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedProjection_continuous H
      P.domain.carrier (closure D)))
  have hScl : S ⊆ closure D := by rintro _ ⟨z, _hz, rfl⟩; exact z.property
  have hl : LocallyFinite (fun g : H => g • S) :=
    hD.locallyFinite.subset (fun _ => Set.smul_set_mono hScl)
  have hc : IsClosed (⋃ g : H, g • S) :=
    hl.isClosed_iUnion (fun g => (Homeomorph.smul g).isClosedMap S hS)
  have he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier ⁻¹' (fuchsianDomainComparisonMap P D '' C) =
      ⋃ g : H, g • S := by
    ext x
    constructor
    · rintro ⟨q, hq, hqx⟩
      induction q using Quotient.inductionOn with
      | h z =>
        obtain ⟨g, hg⟩ := (Quotient.exact hqx : MulAction.orbitRel H P.domain.carrier z.val x)
        refine mem_iUnion.mpr ⟨g⁻¹, z.val, ⟨z, hq, rfl⟩, ?_⟩
        change g⁻¹ • z.val = x
        rw [← hg, inv_smul_smul]
    · intro hx
      obtain ⟨g, z, ⟨w, hw, hwz⟩, hgz⟩ := mem_iUnion.mp hx
      subst z
      refine ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedProjection H P.domain.carrier
        (closure D) w, hw, ?_⟩
      change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier w.val = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier x
      rw [← hgz, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul]
  apply (isQuotientMap_quotient_mk' (s := MulAction.orbitRel H P.domain.carrier)).isClosed_preimage.mp
  change IsClosed (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier ⁻¹'
    _)
  rw [he]
  exact hc

/-- local-finiteness direction: the actual identified closure is the full actual orbit space. -/
theorem IsLocallyFiniteFuchsianDomain.comparison_isHomeomorph {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) : IsHomeomorph (fuchsianDomainComparisonMap P D) := by
  apply isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
  have hd := _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianFundamentalDomain.comparisonData hD.fundamental
  exact ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.comparisonMap_continuous H P.domain.carrier
    (closure D), hD.comparison_isClosedMap,
    hd.comparison_injective, hd.comparison_surjective⟩

/-- The same genuine comparison map bundled as a homeomorphism, without changing its action. -/
def IsLocallyFiniteFuchsianDomain.comparisonHomeomorph {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) :
    FuchsianClosedDomainQuotient P D ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.domain :=
  hD.comparison_isHomeomorph.homeomorph _

theorem IsLocallyFiniteFuchsianDomain.comparisonHomeomorph_apply {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (q : FuchsianClosedDomainQuotient P D) :
    hD.comparisonHomeomorph q = fuchsianDomainComparisonMap P D q := rfl

/-- A regular point has a neighborhood meeting only finitely many closed domain tiles. -/
def FuchsianDomainRegularPoint {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (x : P.domain.carrier) : Prop :=
  ∃ N ∈ 𝓝 x, {g : H | (fuchsianDomainTile P D g ∩ N).Nonempty}.Finite

/-- Exceptional means failure of the actual local finite-copy condition. -/
def FuchsianDomainExceptionalPoint {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (x : P.domain.carrier) : Prop := ¬FuchsianDomainRegularPoint P D x

/-- The absence of exceptional points is exactly local finiteness, under the original domain hypothesis. -/
theorem isLocallyFiniteFuchsianDomain_iff_no_exceptional {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    IsLocallyFiniteFuchsianDomain P D ↔ IsFuchsianFundamentalDomain P D ∧
      ∀ x : P.domain.carrier, ¬FuchsianDomainExceptionalPoint P D x := by
  simp only [FuchsianDomainExceptionalPoint, not_not]
  exact isLocallyFiniteFuchsianDomain_iff P D

/-- A distinct open tile is disjoint even from the closed original tile. -/
theorem IsFuchsianFundamentalDomain.disjoint_image_closure {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) {g : H} (hg : g ≠ 1) :
    Disjoint (g • D) (closure D) := by
  have hgo : IsOpen (g • D) := (Homeomorph.smul g).isOpenMap D ((isFuchsianFundamentalDomain_iff P D).mp hD).1
  have hsub : D ⊆ (g • D)ᶜ := by
    intro x hx hgx
    exact Set.disjoint_left.mp (hD.disjoint_image hg) hgx hx
  have hc := closure_minimal hsub hgo.isClosed_compl
  exact Set.disjoint_left.mpr (fun _ hx hcx => hc hcx hx)

/-- An interior representative has no different orbit mate anywhere in the closed fundamental domain. -/
theorem IsFuchsianFundamentalDomain.interior_closure_orbit_unique {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) {z w : P.domain.carrier}
    (hz : z ∈ D) (hw : w ∈ closure D)
    (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier w = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier z) : w = z := by
  obtain ⟨g, hg⟩ := (Quotient.exact he : MulAction.orbitRel H P.domain.carrier w z)
  have hg1 : g = 1 := by
    by_contra hn
    exact Set.disjoint_left.mp (hD.disjoint_image_closure hn) ⟨z, hz, hg⟩ hw
  simpa only [hg1, one_smul] using hg.symm

/-- Sets of interior representatives have no extra identifications on the closed domain. -/
theorem IsFuchsianFundamentalDomain.restricted_saturation_interior {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D Z : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (hZ : Z ⊆ D) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedProjection H P.domain.carrier (closure D) ⁻¹'
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedProjection H P.domain.carrier (closure D)
        ''
        ((Subtype.val : closure D → P.domain.carrier) ⁻¹' Z)) =
      (Subtype.val : closure D → P.domain.carrier) ⁻¹' Z := by
  ext w
  constructor
  · rintro ⟨z, hz, he⟩
    have hwz : w.val = z.val := hD.interior_closure_orbit_unique (hZ hz) w.property
      (congrArg (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.comparisonMap H P.domain.carrier (closure
        D)) he).symm
    change w.val ∈ Z
    rw [hwz]
    exact hz
  · intro hw
    exact ⟨w, hw, rfl⟩

/-- A closed set of genuine interior representatives remains closed in the identified closed domain. -/
theorem IsFuchsianFundamentalDomain.restricted_image_closed {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D Z : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (hZ : Z ⊆ D) (hZc : IsClosed Z) :
    IsClosed (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedProjection H P.domain.carrier
      (closure D) ''
      ((Subtype.val : closure D → P.domain.carrier) ⁻¹' Z)) := by
  apply (isQuotientMap_quotient_mk' (s :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedOrbitRel H P.domain.carrier (closure
    D))).isClosed_preimage.mp
  change IsClosed (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedProjection H P.domain.carrier
    (closure D) ⁻¹' _)
  rw [hD.restricted_saturation_interior hZ]
  exact hZc.preimage continuous_subtype_val

/-- Any point common to two open fundamental tiles forces the original group elements to coincide. -/
theorem IsFuchsianFundamentalDomain.tile_intersection_eq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) {g k : H} {x : P.domain.carrier}
    (hxg : x ∈ g • D) (hxk : x ∈ k • D) : g = k := by
  by_contra hne
  obtain ⟨u, hu, hgu⟩ := hxg
  obtain ⟨v, hv, hkv⟩ := hxk
  have hn : k⁻¹ * g ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
  change g • u = x at hgu
  change k • v = x at hkv
  have he : (k⁻¹ * g) • u = v := by rw [mul_smul, hgu, ← hkv, inv_smul_smul]
  exact Set.disjoint_left.mp (hD.disjoint_image hn) ⟨u, hu, he⟩ hv

/-- A limit of points in infinitely many distinct open tiles lies in no open tile. -/
theorem IsFuchsianFundamentalDomain.distinct_tile_limit_not_interior {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (g : ℕ → H) (hg : Function.Injective g)
    (u : ℕ → P.domain.carrier) (hu : ∀ n, u n ∈ D) (x : P.domain.carrier)
    (ht : Tendsto (fun n => g n • u n) atTop (𝓝 x)) (k : H) : x ∉ k • D := by
  intro hx
  have hop : IsOpen (k • D) := (Homeomorph.smul k).isOpenMap D
    ((isFuchsianFundamentalDomain_iff P D).mp hD).1
  have he : ∀ᶠ n in atTop, g n = k :=
    (ht.eventually (hop.mem_nhds hx)).mono (fun n hn =>
      hD.tile_intersection_eq ⟨u n, hu n, rfl⟩ hn)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hh : N = N + 1 := hg ((hN N le_rfl).trans (hN (N + 1) (by omega)).symm)
  omega

/-- Proper discontinuity forces representatives whose distinct translates converge to escape
all compact sets; their actual set of values is therefore closed. -/
theorem properlyDiscontinuous_closed_representatives
    {G X : Type*} [Group G] [TopologicalSpace X] [T1Space X] [CompactlyCoherentSpace X]
    [MulAction G X] [ProperlyDiscontinuousSMul G X]
    (g : ℕ → G) (hg : Function.Injective g) (u : ℕ → X) (x : X)
    (ht : Tendsto (fun n => g n • u n) atTop (𝓝 x)) : IsClosed (Set.range u) := by
  apply (CompactlyCoherentSpace.isClosed_iff _).mpr
  intro K hK
  let L := insert x (Set.range (fun n => g n • u n))
  have hL : IsCompact L := ht.isCompact_insert_range
  have hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) hK hL
  have hi : {n : ℕ | u n ∈ K}.Finite :=
    (hf.preimage hg.injOn).subset (fun n hn =>
      ⟨g n • u n, ⟨u n, hn, rfl⟩, Or.inr (Set.mem_range_self n)⟩)
  have hKR : (K ∩ Set.range u).Finite := (hi.image u).subset (by
    rintro z ⟨hz, n, rfl⟩
    exact ⟨n, hz, rfl⟩)
  have hp := hKR.preimage (Subtype.val_injective (p := fun x : X => x ∈ K)).injOn
  convert hp.isClosed using 1
  ext z
  simp only [mem_preimage, mem_inter_iff, z.property, true_and]

/-- Failure of local finiteness yields distinct genuine translates of interior points converging
at an actual ambient point. This sequence is constructed, rather than assumed. -/
theorem not_locallyFinite_closed_tiles_exists_sequence
    {G X : Type*} [Group G] [MetricSpace X] [MulAction G X] [ContinuousConstSMul G X]
    (D : Set X) (hnot : ¬LocallyFinite (fun g : G => g • closure D)) :
    ∃ (x : X) (g : ℕ → G) (u : ℕ → X), Function.Injective g ∧
      (∀ n, u n ∈ D) ∧ Tendsto (fun n => g n • u n) atTop (𝓝 x) := by
  classical
  unfold LocallyFinite at hnot
  push Not at hnot
  obtain ⟨x, hx⟩ := hnot
  let A : (ℕ × G × X) → Prop := fun a =>
    a.2.2 ∈ D ∧ dist (a.2.1 • a.2.2) x < 1 / ((a.1 : ℝ) + 1)
  let R : (ℕ × G × X) → (ℕ × G × X) → Prop := fun a b => a.1 < b.1 ∧ a.2.1 ≠ b.2.1
  have hchoose : ∀ s : Finset (ℕ × G × X), (∀ a ∈ s, A a) →
      ∃ b, A b ∧ ∀ a ∈ s, R a b := by
    intro s _hs
    let N := s.sup Prod.fst + 1
    have hr : 0 < 1 / ((N : ℝ) + 1) := by positivity
    obtain ⟨g, hg, hgnot⟩ := (hx (Metric.ball x (1 / ((N : ℝ) + 1)))
      (Metric.ball_mem_nhds x hr)).exists_notMem_finset (s.image (fun a => a.2.1))
    obtain ⟨v, ⟨z, hz, hgz⟩, hv⟩ := hg
    have hop : IsOpen ((fun y : X => g • y) ⁻¹' Metric.ball x (1 / ((N : ℝ) + 1))) :=
      Metric.isOpen_ball.preimage (continuous_const_smul g)
    have hzin : z ∈ (fun y : X => g • y) ⁻¹' Metric.ball x (1 / ((N : ℝ) + 1)) := by
      change g • z ∈ Metric.ball x _
      change g • z = v at hgz
      rw [hgz]
      exact hv
    obtain ⟨u, huV, huD⟩ := mem_closure_iff.mp hz _ hop hzin
    refine ⟨(N, g, u), ⟨huD, huV⟩, ?_⟩
    intro a ha
    refine ⟨Nat.lt_succ_of_le (Finset.le_sup ha), ?_⟩
    intro he
    exact hgnot (Finset.mem_image.mpr ⟨a, ha, he⟩)
  obtain ⟨f, hf, hfr⟩ := exists_seq_of_forall_finset_exists A R hchoose
  have htime : StrictMono (fun n => (f n).1) := fun m n hmn => (hfr m n hmn).1
  have hinj : Function.Injective (fun n => (f n).2.1) := by
    intro m n he
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hfr m n h).2 he
    · exact (hfr n m h).2 he.symm
  refine ⟨x, (fun n => (f n).2.1), (fun n => (f n).2.2), hinj,
    (fun n => (hf n).1), ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound (n : ℕ) : dist ((f n).2.1 • (f n).2.2) x ≤ 1 / ((n : ℝ) + 1) := by
    have hn : (n : ℝ) + 1 ≤ ((f n).1 : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right (htime.id_le n) 1
    exact (hf n).2.le.trans (one_div_le_one_div_of_le (by positivity) hn)
  exact squeeze_zero (fun _ => dist_nonneg) hbound tendsto_one_div_add_atTop_nhds_zero_nat

/-- An auxiliary compatible metric from the genuine finite-disc coordinate, used only for sequences. -/
@[instance_reducible] def UnitDiscFuchsianGroup.coordinateMetricSpace {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : MetricSpace P.domain.carrier :=
  @Topology.IsEmbedding.comapMetricSpace P.domain.carrier ℂ
    inferInstance inferInstance (fun x => (P.finiteCoordinate x : ℂ))
      (Complex.UnitDisc.isEmbedding_coe.comp P.finiteCoordinate.isEmbedding)

/-- A homeomorphic closed-domain comparison map implies local finiteness,
including when the group has finite elliptic stabilizers. -/
theorem IsFuchsianFundamentalDomain.locallyFinite_of_comparison_homeomorph
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (hθ : IsHomeomorph (fuchsianDomainComparisonMap P D)) :
    IsLocallyFiniteFuchsianDomain P D := by
  by_contra hn
  have hnot : ¬LocallyFinite (fuchsianDomainTile P D) :=
    fun hl => hn ((isLocallyFiniteFuchsianDomain_iff P D).mpr ⟨hD, hl⟩)
  let : MetricSpace P.domain.carrier := P.coordinateMetricSpace
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  obtain ⟨x, g, u, hg, hu, ht⟩ := not_locallyFinite_closed_tiles_exists_sequence D hnot
  let : ProperlyDiscontinuousSMul H P.domain.carrier :=
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_properlyDiscontinuous P.domain P.discontinuous
  have hZ : Set.range u ⊆ D := by rintro _ ⟨n, rfl⟩; exact hu n
  have hZc : IsClosed (Set.range u) := properlyDiscontinuous_closed_representatives g hg u x ht
  let C : Set (FuchsianClosedDomainQuotient P D) :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedProjection H P.domain.carrier (closure D) ''
      ((Subtype.val : closure D → P.domain.carrier) ⁻¹' Set.range u)
  have hC : IsClosed C := hD.restricted_image_closed hZ hZc
  have hθC : IsClosed (fuchsianDomainComparisonMap P D '' C) := hθ.isClosedMap C hC
  have hseq (n : ℕ) : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection P.domain (g n • u n) ∈
      fuchsianDomainComparisonMap P D '' C := by
    let z : closure D := ⟨u n, subset_closure (hu n)⟩
    refine ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedProjection H P.domain.carrier
      (closure D) z,
      ⟨z, ⟨n, rfl⟩, rfl⟩, ?_⟩
    exact (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_smul P.domain (g n) (u n)).symm
  have hxC : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection P.domain x ∈ fuchsianDomainComparisonMap P D '' C :=
    hθC.mem_of_tendsto ((_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_continuous
      P.domain).continuousAt.tendsto.comp ht)
      (Filter.Eventually.of_forall hseq)
  obtain ⟨q, ⟨z, ⟨n, hnz⟩, rfl⟩, he⟩ := hxC
  change _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection P.domain z.val = _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection P.domain x at he
  obtain ⟨k, hk⟩ := (Quotient.exact he : MulAction.orbitRel H P.domain.carrier z.val x)
  have he' : k⁻¹ • u n = x := by rw [hnz, ← hk, inv_smul_smul]
  exact hD.distinct_tile_limit_not_interior g hg u hu x ht k⁻¹ ⟨u n, hu n, he'⟩

/-- both implications for the actual original comparison map. -/
theorem locallyFinite_iff_comparisonMap_isHomeomorph {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D) :
    IsLocallyFiniteFuchsianDomain P D ↔ IsHomeomorph (fuchsianDomainComparisonMap P D) :=
  ⟨fun h => h.comparison_isHomeomorph, hD.locallyFinite_of_comparison_homeomorph⟩

end LowDimensionalTopology.Geometry.Fuchsian
