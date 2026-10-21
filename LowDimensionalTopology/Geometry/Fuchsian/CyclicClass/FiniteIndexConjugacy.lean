/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The pretransitive orbit quotient construction is adapted from Mathlib's
GroupTheory/GroupAction/Quotient.lean, by Chris Hughes and Thomas Browning.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.PowerConjugacy
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Quotient
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- One transitive ambient orbit splits into at most the subgroup index many orbits. -/
theorem subgroup_pretransitive_orbit_card_le_index {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (H : Subgroup G) [Finite (G ⧸ H)] :
    Nat.card (MulAction.orbitRel.Quotient H X) ≤ H.index := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨b⟩⟩
  · have : IsEmpty (MulAction.orbitRel.Quotient H X) := inferInstance
    simp only [Nat.card_of_isEmpty, Nat.zero_le]
  have hfinite : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  let f : Quotient (QuotientGroup.rightRel H) → MulAction.orbitRel.Quotient H X :=
    fun a => Quotient.liftOn' a (fun g => ⟦g • b⟧) fun g₁ g₂ r => by
      replace r := Setoid.symm' _ r
      rw [QuotientGroup.rightRel_eq] at r
      simp only [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨⟨g₁ * g₂⁻¹, r⟩, by simp [mul_smul]⟩
  have hsurj : Function.Surjective f :=
    (Quotient.surjective_liftOn' _).2
      (Quotient.mk''_surjective.comp (MulAction.surjective_smul _ _))
  have hc := Nat.card_le_card_of_surjective f hsurj
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)] at hc
  exact hc

/-- The orbit-count inequality underlying, without geometric hypotheses. -/
theorem subgroup_orbit_card_le_index_mul {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) [Finite (G ⧸ H)] [Finite (MulAction.orbitRel.Quotient G X)] :
    Nat.card (MulAction.orbitRel.Quotient H X) ≤
      H.index * Nat.card (MulAction.orbitRel.Quotient G X) := by
  classical
  let Ω := MulAction.orbitRel.Quotient G X
  let : Fintype Ω := Fintype.ofFinite Ω
  rw [Nat.card_congr (MulAction.equivSubgroupOrbits X H), Nat.card_sigma]
  calc
    ∑ ω : Ω, Nat.card (MulAction.orbitRel.Quotient H (MulAction.orbitRel.Quotient.orbit ω))
        ≤ ∑ _ω : Ω, H.index := Finset.sum_le_sum fun ω _ =>
          subgroup_pretransitive_orbit_card_le_index H
    _ = H.index * Nat.card Ω := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

/-- A maximal cyclic subgroup of the original actual Mobius subgroup. -/
def IsMaximalCyclicIn (H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Prop :=
  K ≤ H ∧ IsCyclic K ∧
    ∀ L : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, L ≤ H → IsCyclic L → K ≤ L → L = K

theorem cyclic_mobius_commute (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hK :
  IsCyclic K)
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ∈ K) (hg : g ∈ K) : Commute f g := by
  have := hK
  let F : K := ⟨f, hf⟩
  let G : K := ⟨g, hg⟩
  obtain ⟨a, ha⟩ := exists_zpow_surjective K
  obtain ⟨m, hm⟩ := ha F
  obtain ⟨n, hn⟩ := ha G
  have he : F * G = G * F := by rw [← hm, ← hn]; exact zpow_mul_comm a m n
  exact congrArg (fun k : K => k.val) he

/-- A cyclic subgroup containing a parabolic map fixes its actual unique fixed point. -/
theorem cyclic_parabolic_fixes (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hK :
  IsCyclic K)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfK : f ∈ K) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfp : f.val p = p) : ∀ g ∈ K, g.val p = p := by
  obtain ⟨w, hw⟩ := hf.2
  have hpw := (hw p).mp hfp
  intro g hg
  have hc := cyclic_mobius_commute K hK f g hfK hg
  have he := congrArg (fun k : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => k.val p) hc.eq
  change f.val (g.val p) = g.val (f.val p) at he
  rw [hfp] at he
  exact ((hw (g.val p)).mp he).trans hpw.symm

/-- A cyclic subgroup containing an elliptic map fixes its unique point in the invariant disc. -/
theorem cyclic_elliptic_disc_fixes {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K ≤ H) (hK : IsCyclic K)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfK : f ∈ K) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (p : D.carrier) (hfp : f.val p.val = p.val) : ∀ g ∈ K, g.val p.val = p.val := by
  obtain ⟨z, hz, hzu⟩ := elliptic_disc_existsUnique_fixed f hf D.isDisc (D.image_eq ⟨f, hKH hfK⟩)
  have hpz : p = z := hzu p hfp
  intro g hg
  have hc := cyclic_mobius_commute K hK f g hfK hg
  have he := congrArg (fun k : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => k.val p.val) hc.eq
  change f.val (g.val p.val) = g.val (f.val p.val) at he
  rw [hfp] at he
  have hgpD := D.invariant ⟨g, hKH hg⟩ p.val p.property
  exact (congrArg Subtype.val (hzu ⟨g.val p.val, hgpD⟩ he)).trans
    (congrArg Subtype.val hpz).symm

/-- The stabilizer of a parabolic fixed point is a maximal actual cyclic subgroup. -/
theorem parabolic_stabilizer_isMaximalCyclic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfH : f ∈ H) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfp : f.val p = p) :
    IsMaximalCyclicIn H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p) := by
  have hle : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p ≤ H :=
    fun g hg => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mp hg).1
  refine ⟨hle, D.stabilizer_isCyclic p, ?_⟩
  intro L hLH hL hKL
  apply le_antisymm _ hKL
  intro g hg
  apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mpr
  refine ⟨hLH hg, ?_⟩
  exact cyclic_parabolic_fixes L hL f
    (hKL ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p f).mpr ⟨hfH,
      hfp⟩)) hf p hfp g hg

/-- The stabilizer of an elliptic interior fixed point is a maximal actual cyclic subgroup. -/
theorem elliptic_stabilizer_isMaximalCyclic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfH : f ∈ H) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (p : D.carrier) (hfp : f.val p.val = p.val) :
    IsMaximalCyclicIn H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val) := by
  have hle : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val ≤ H :=
    fun g hg => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val g).mp hg).1
  refine ⟨hle, D.stabilizer_isCyclic p.val, ?_⟩
  intro L hLH hL hKL
  apply le_antisymm _ hKL
  intro g hg
  apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val g).mpr
  refine ⟨hLH hg, ?_⟩
  exact cyclic_elliptic_disc_fixes D L hLH hL f
    (hKL ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val f).mpr ⟨hfH,
      hfp⟩)) hf p hfp g hg

/-- Every actual maximal parabolic cyclic subgroup is the stabilizer of its unique fixed point. -/
theorem maximal_parabolic_cyclic_eq_stabilizer {H K : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hK : IsMaximalCyclicIn H K)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfK : f ∈ K) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfp : f.val p = p) : K = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p := by
  have hle : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p ≤ H :=
    fun g hg => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mp hg).1
  apply Eq.symm
  apply hK.2.2 _ hle (D.stabilizer_isCyclic p)
  intro g hg
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mpr
    ⟨hK.1 hg, cyclic_parabolic_fixes K hK.2.1 f hfK hf p hfp g hg⟩

/-- Every actual maximal elliptic cyclic subgroup is the stabilizer of its unique interior fixed point. -/
theorem maximal_elliptic_cyclic_eq_stabilizer {H K : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hK : IsMaximalCyclicIn H K)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfK : f ∈ K) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (p : D.carrier) (hfp : f.val p.val = p.val) : K = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val := by
  have hle : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val ≤ H :=
    fun g hg => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val g).mp hg).1
  apply Eq.symm
  apply hK.2.2 _ hle (D.stabilizer_isCyclic p.val)
  intro g hg
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val g).mpr
    ⟨hK.1 hg, cyclic_elliptic_disc_fixes D K hK.1 hK.2.1 f hfK hf p hfp g hg⟩

/-- The two finite-index class-counting types. -/
inductive FuchsianCyclicKind
  | elliptic
  | parabolic

def MobiusCyclicType (kind : FuchsianCyclicKind) (f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Prop :=
  match kind with
  | .elliptic => _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f
  | .parabolic => _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f

/-- Actual fixed points, choosing the interior point for elliptics. -/
def fuchsianCyclicFixedPoints {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind :
      FuchsianCyclicKind) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  {p | (kind = .elliptic → p ∈ D.carrier) ∧
    ∃ f ∈ H, MobiusCyclicType kind f ∧ f.val p = p}

/-- The actual maximal cyclic subgroups, with a witness of the required geometric type. -/
def fuchsianMaximalCyclicSubgroups (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (kind : FuchsianCyclicKind) : Set (Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
  {K | IsMaximalCyclicIn H K ∧ ∃ f ∈ K, MobiusCyclicType kind f}

/-- The actual point-stabilizer map, with maximal cyclicity proved geometrically. -/
def fuchsianCyclicPointStabilizer {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind) :
    fuchsianCyclicFixedPoints D kind → fuchsianMaximalCyclicSubgroups H kind :=
  fun p => ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val, by
    obtain ⟨f, hfH, hft, hfp⟩ := p.property.2
    refine ⟨?_, f, ?_, hft⟩
    · cases kind with
      | elliptic =>
        exact elliptic_stabilizer_isMaximalCyclic D f hfH hft
          ⟨p.val, p.property.1 rfl⟩ hfp
      | parabolic => exact parabolic_stabilizer_isMaximalCyclic D f hfH hft p.val hfp
    · exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val f).mpr ⟨hfH,
      hfp⟩⟩

theorem fuchsianCyclicPointStabilizer_injective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind) :
    Function.Injective (fuchsianCyclicPointStabilizer D kind) := by
  intro p q he
  have hK : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H q.val :=
    congrArg Subtype.val he
  obtain ⟨f, hfH, hft, hfp⟩ := p.property.2
  have hfq : f.val q.val = q.val := by
    have hmem := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val
      f).mpr ⟨hfH, hfp⟩
    rw [hK] at hmem
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H q.val f).mp hmem).2
  apply Subtype.ext
  cases kind with
  | elliptic =>
    obtain ⟨z, hz, hzu⟩ := elliptic_disc_existsUnique_fixed f hft D.isDisc (D.image_eq ⟨f, hfH⟩)
    exact (congrArg Subtype.val (hzu ⟨p.val, p.property.1 rfl⟩ hfp)).trans
      (congrArg Subtype.val (hzu ⟨q.val, q.property.1 rfl⟩ hfq)).symm
  | parabolic =>
    obtain ⟨w, hw⟩ := hft.2
    exact ((hw p.val).mp hfp).trans ((hw q.val).mp hfq).symm

theorem fuchsianCyclicPointStabilizer_surjective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind) :
    Function.Surjective (fuchsianCyclicPointStabilizer D kind) := by
  intro K
  obtain ⟨hK, f, hfK, hft⟩ := K.property
  cases kind with
  | elliptic =>
    obtain ⟨p, hp, _hu⟩ := elliptic_disc_existsUnique_fixed f hft D.isDisc
      (D.image_eq ⟨f, hK.1 hfK⟩)
    refine ⟨⟨p.val, (fun _ => p.property), f, hK.1 hfK, hft, hp⟩, ?_⟩
    apply Subtype.ext
    exact (maximal_elliptic_cyclic_eq_stabilizer D hK f hfK hft p hp).symm
  | parabolic =>
    obtain ⟨p, hp⟩ := hft.2
    have hfp := (hp p).mpr rfl
    refine ⟨⟨p, (by intro h; cases h), f, hK.1 hfK, hft, hfp⟩, ?_⟩
    apply Subtype.ext
    exact (maximal_parabolic_cyclic_eq_stabilizer D hK f hfK hft p hfp).symm

/-- Literal maximal cyclic subgroups are in bijection with the appropriate actual fixed points. -/
def fuchsianCyclicPointStabilizerEquiv {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind) :
    fuchsianCyclicFixedPoints D kind ≃ fuchsianMaximalCyclicSubgroups H kind :=
  Equiv.ofBijective (fuchsianCyclicPointStabilizer D kind)
    ⟨fuchsianCyclicPointStabilizer_injective D kind, fuchsianCyclicPointStabilizer_surjective D kind⟩

theorem MobiusCyclicType.conjugate {kind : FuchsianCyclicKind} {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hf : MobiusCyclicType kind f) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    MobiusCyclicType kind (q * f * q⁻¹) := by
  cases kind with
  | elliptic =>
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  | parabolic =>
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf

theorem fuchsianCyclicFixedPoints_invariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind) (g : H) (p :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hp : p ∈ fuchsianCyclicFixedPoints D kind) : g • p ∈ fuchsianCyclicFixedPoints D kind := by
  obtain ⟨f, hfH, hft, hfp⟩ := hp.2
  refine ⟨fun he => D.invariant g p (hp.1 he), g.val * f * g.val⁻¹,
    H.mul_mem (H.mul_mem g.property hfH) (H.inv_mem g.property), hft.conjugate g.val, ?_⟩
  change (g.val * f * g.val⁻¹).val (g.val.val p) = g.val.val p
  rwa [_root_.LowDimensionalTopology.Geometry.Mobius.mobius_conjugate_boundary_fixed_iff, Equiv.symm_apply_apply]

instance fuchsianCyclicFixedPointAction {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind) :
    MulAction H (fuchsianCyclicFixedPoints D kind) where
  smul g p := ⟨g • p.val, fuchsianCyclicFixedPoints_invariant D kind g p.val p.property⟩
  one_smul p := Subtype.ext (one_smul H p.val)
  mul_smul g h p := Subtype.ext (mul_smul g h p.val)

/-- Stabilizer transport is literal conjugation of actual Mobius subgroups. -/
theorem mobiusBoundaryStabilizer_conjugation (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (g : H) (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H (g • p) =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate g.val (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p) := by
  unfold _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map, Subgroup.map_map]
  rfl

/-- Conjugacy of the literal maximal subgroups is exactly the original group orbit relation. -/
theorem fuchsianCyclicPointStabilizer_conjugacy_iff {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind)
    (p q : fuchsianCyclicFixedPoints D kind) :
    (∃ g : H, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate g.val
      (fuchsianCyclicPointStabilizer D kind p).val =
        (fuchsianCyclicPointStabilizer D kind q).val) ↔
      MulAction.orbitRel H (fuchsianCyclicFixedPoints D kind) p q := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g⁻¹, ?_⟩
    have hpq : g • p = q := by
      apply fuchsianCyclicPointStabilizer_injective D kind
      apply Subtype.ext
      exact (mobiusBoundaryStabilizer_conjugation H g p.val).trans hg
    rw [← hpq, inv_smul_smul]
  · rintro ⟨g, hg⟩
    refine ⟨g⁻¹, ?_⟩
    have hpq : g⁻¹ • p = q := by rw [← hg, inv_smul_smul]
    exact (mobiusBoundaryStabilizer_conjugation H g⁻¹ p.val).symm.trans
      (congrArg (fun r => _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H r.val) hpq)

/-- The setoid on literal maximal cyclic subgroups, identified below with actual conjugacy. -/
def fuchsianMaximalCyclicConjugacySetoid {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind) :
    Setoid (fuchsianMaximalCyclicSubgroups H kind) :=
  Setoid.comap (fuchsianCyclicPointStabilizerEquiv D kind).symm
    (MulAction.orbitRel H (fuchsianCyclicFixedPoints D kind))

def FuchsianCyclicConjugacyClasses {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind) :=
  Quotient (fuchsianMaximalCyclicConjugacySetoid D kind)

/-- The defining relation is actual subgroup conjugacy, rather than an unproved model relation. -/
theorem fuchsianMaximalCyclicConjugacySetoid_iff {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind)
    (K L : fuchsianMaximalCyclicSubgroups H kind) :
    (fuchsianMaximalCyclicConjugacySetoid D kind).r K L ↔
      ∃ g : H, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate g.val K.val = L.val := by
  change MulAction.orbitRel H (fuchsianCyclicFixedPoints D kind)
    ((fuchsianCyclicPointStabilizerEquiv D kind).symm K)
    ((fuchsianCyclicPointStabilizerEquiv D kind).symm L) ↔ _
  have h := (fuchsianCyclicPointStabilizer_conjugacy_iff D kind
    ((fuchsianCyclicPointStabilizerEquiv D kind).symm K)
    ((fuchsianCyclicPointStabilizerEquiv D kind).symm L)).symm
  change _ ↔ _ at h
  simpa only [show fuchsianCyclicPointStabilizer D kind =
      fuchsianCyclicPointStabilizerEquiv D kind from rfl, Equiv.apply_symm_apply] using h

/-- The actual maximal-cyclic conjugacy classes and actual fixed-point orbits are equivalent. -/
def fuchsianCyclicConjugacyClassesEquiv {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind) :
    FuchsianCyclicConjugacyClasses D kind ≃
      MulAction.orbitRel.Quotient H (fuchsianCyclicFixedPoints D kind) :=
  Quotient.congr (fuchsianCyclicPointStabilizerEquiv D kind).symm (fun _ _ => Iff.rfl)

/-- An injective equivariant map reflects as well as preserves actual orbit relations. -/
theorem orbitRel_iff_of_equivariant_injective {G X Y : Type*} [Group G]
    [MulAction G X] [MulAction G Y] (f : X → Y) (hi : Function.Injective f)
    (he : ∀ (g : G) (x : X), f (g • x) = g • f x) (x y : X) :
    MulAction.orbitRel G X x y ↔ MulAction.orbitRel G Y (f x) (f y) := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, (he g y).symm.trans (congrArg f hg)⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, hi ((he g y).trans hg)⟩

/-- Actual subgroup-orbit classes inject along an injective equivariant map. -/
def orbitQuotientEmbedding {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (f : X → Y) (hi : Function.Injective f) (he : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    MulAction.orbitRel.Quotient G X ↪ MulAction.orbitRel.Quotient G Y where
  toFun := Quotient.map' f (fun x y h => (orbitRel_iff_of_equivariant_injective f hi he x y).mp h)
  inj' := by
    intro a b h
    induction a using Quotient.inductionOn' with | h a =>
      induction b using Quotient.inductionOn' with | h b =>
        exact Quotient.sound ((orbitRel_iff_of_equivariant_injective f hi he a b).mpr
          (Quotient.exact h))

/-- Relabeling an acting group by a genuine group isomorphism preserves its actual orbit quotient. -/
def orbitQuotientEquivOfMulEquiv {G K X : Type*} [Group G] [Group K]
    [MulAction G X] [MulAction K X] (e : G ≃* K)
    (he : ∀ (g : G) (x : X), g • x = e g • x) :
    MulAction.orbitRel.Quotient G X ≃ MulAction.orbitRel.Quotient K X :=
  Quotient.congr (Equiv.refl X) (by
    intro x y
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨e g, (he g y).symm.trans hg⟩
    · rintro ⟨k, hk⟩
      refine ⟨e.symm k, ?_⟩
      rw [he, e.apply_symm_apply]
      exact hk)

/-- The original disc and discontinuity condition restrict to an actual subgroup. -/
def fuchsianDiscRestrict {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K ≤ H) : FuchsianDisc K where
  carrier := D.carrier
  isDisc := D.isDisc
  invariant g p hp := D.invariant ⟨g.val, hKH g.property⟩ p hp
  discontinuous := by
    intro B hB hBD
    let i : K → H := fun g => ⟨g.val, hKH g.property⟩
    have hi : Function.Injective i := by
      intro a b h
      exact Subtype.ext (congrArg (fun g : H => g.val) h)
    exact Set.Finite.preimage (f := i) hi.injOn (D.discontinuous B hB hBD)

/-- The actual smaller group's fixed points sit inside the original group's fixed points. -/
def fuchsianCyclicFixedPointsInclusion {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (kind : FuchsianCyclicKind) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K
      ≤ H) :
    fuchsianCyclicFixedPoints (fuchsianDiscRestrict D K hKH) kind ↪
      fuchsianCyclicFixedPoints D kind where
  toFun p := ⟨p.val, p.property.1, by
    obtain ⟨f, hfK, hft, hfp⟩ := p.property.2
    exact ⟨f, hKH hfK, hft, hfp⟩⟩
  inj' a b h := Subtype.ext
    (congrArg (fun p : fuchsianCyclicFixedPoints D kind => p.val) h)

/-- Orbit counting for an actual inclusion of Mobius subgroups, preserving the literal action. -/
theorem subgroupInclusion_orbit_finite_and_card_le
    (H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K ≤ H) (X :
      Type*) [MulAction H X]
    [Finite (H ⧸ K.subgroupOf H)] [Finite (MulAction.orbitRel.Quotient H X)] :
    let _ : MulAction K X := MulAction.compHom X (Subgroup.inclusion hKH)
    Finite (MulAction.orbitRel.Quotient K X) ∧
      Nat.card (MulAction.orbitRel.Quotient K X) ≤
        (K.subgroupOf H).index * Nat.card (MulAction.orbitRel.Quotient H X) := by
  let J := K.subgroupOf H
  let _ : MulAction K X := MulAction.compHom X (Subgroup.inclusion hKH)
  let e : J ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  let E := orbitQuotientEquivOfMulEquiv (X := X) e (by intro g x; rfl)
  have : Finite (MulAction.orbitRel.Quotient J X) := inferInstance
  refine ⟨Finite.of_equiv _ E, ?_⟩
  rw [← Nat.card_congr E]
  exact subgroup_orbit_card_le_index_mul J

/-- For actual maximal cyclic subgroups, both parabolic and elliptic. -/
theorem fuchsian_cyclic_conjugacy_card_le_index_mul
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K ≤ H) (kind :
      FuchsianCyclicKind)
    [Finite (H ⧸ K.subgroupOf H)] [Finite (FuchsianCyclicConjugacyClasses D kind)] :
    Finite (FuchsianCyclicConjugacyClasses (fuchsianDiscRestrict D K hKH) kind) ∧
      Nat.card (FuchsianCyclicConjugacyClasses (fuchsianDiscRestrict D K hKH) kind) ≤
        (K.subgroupOf H).index * Nat.card (FuchsianCyclicConjugacyClasses D kind) := by
  let X := fuchsianCyclicFixedPoints D kind
  let Y := fuchsianCyclicFixedPoints (fuchsianDiscRestrict D K hKH) kind
  let eH := fuchsianCyclicConjugacyClassesEquiv D kind
  have : Finite (MulAction.orbitRel.Quotient H X) := Finite.of_equiv _ eH
  let _ : MulAction K X := MulAction.compHom X (Subgroup.inclusion hKH)
  obtain ⟨hfinite, hbound⟩ := subgroupInclusion_orbit_finite_and_card_le H K hKH X
  have : Finite (MulAction.orbitRel.Quotient K X) := hfinite
  let i : Y ↪ X := fuchsianCyclicFixedPointsInclusion D kind K hKH
  have he : ∀ (g : K) (p : Y), i (g • p) = g • i p := by intro g p; rfl
  let E := orbitQuotientEmbedding i i.injective he
  have : Finite (MulAction.orbitRel.Quotient K Y) := Finite.of_injective E E.injective
  let eK := fuchsianCyclicConjugacyClassesEquiv (fuchsianDiscRestrict D K hKH) kind
  refine ⟨Finite.of_equiv _ eK.symm, ?_⟩
  rw [Nat.card_congr eK, Nat.card_congr eH]
  exact (Nat.card_le_card_of_injective E E.injective).trans hbound

/-- The parabolic assertion. -/
theorem fuchsian_parabolic_conjugacy_card_le_index_mul
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K ≤ H)
    [Finite (H ⧸ K.subgroupOf H)] [Finite (FuchsianCyclicConjugacyClasses D .parabolic)] :
    Nat.card (FuchsianCyclicConjugacyClasses (fuchsianDiscRestrict D K hKH) .parabolic) ≤
      (K.subgroupOf H).index * Nat.card (FuchsianCyclicConjugacyClasses D .parabolic) :=
  (fuchsian_cyclic_conjugacy_card_le_index_mul D K hKH .parabolic).2

/-- The elliptic assertion, permitting trivial intersections in the smaller group. -/
theorem fuchsian_elliptic_conjugacy_card_le_index_mul
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K ≤ H)
    [Finite (H ⧸ K.subgroupOf H)] [Finite (FuchsianCyclicConjugacyClasses D .elliptic)] :
    Nat.card (FuchsianCyclicConjugacyClasses (fuchsianDiscRestrict D K hKH) .elliptic) ≤
      (K.subgroupOf H).index * Nat.card (FuchsianCyclicConjugacyClasses D .elliptic) :=
  (fuchsian_cyclic_conjugacy_card_le_index_mul D K hKH .elliptic).2

end LowDimensionalTopology.Geometry.Fuchsian
