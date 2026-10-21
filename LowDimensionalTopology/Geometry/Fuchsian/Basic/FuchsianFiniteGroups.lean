/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianLimitSets
public import LowDimensionalTopology.Geometry.Mobius.Circle.ComplexReflections
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteCyclicGroups
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology OnePoint ComplexConjugate BigOperators
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Actual circle-inverse points occupy opposite complementary sides of the unit circle. -/
theorem unitCircle_inverse_pair_disc_exterior {a b : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (h : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexInversePair
      (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle 0 1) a b) :
    a ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ↔ b ∈ _root_.LowDimensionalTopology.Geometry.Mobius.extendedUnitDiscExterior := by
  let e := _root_.LowDimensionalTopology.Geometry.Mobius.extendedComplexEuclideanHomeomorph
  let R := _root_.LowDimensionalTopology.Geometry.Inversive.sphereInversionHomeomorph (0 :
    _root_.LowDimensionalTopology.Geometry.Inversive.Euclidean 2) 1 one_ne_zero
  have hR : _root_.LowDimensionalTopology.Geometry.Inversive.IsReflection R := _root_.LowDimensionalTopology.Geometry.Inversive.sphereInversion_isReflection 0 1 zero_lt_one
  have hRfix : Function.fixedPoints R = e '' _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle 0 1 := by
    have he := congrArg (fun S : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex => e ''
      S) (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_reflection 0 1 zero_lt_one)
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.complexReflection_fixedPoints,
      _root_.LowDimensionalTopology.Geometry.Mobius.complexChart_image_preimage] at he
    simpa only [R, map_zero] using he
  obtain ⟨r,hr,hrS,hrab⟩ := h
  have hrR : r = R := hr.eq_of_fixedPoints hR (hrS.trans hRfix.symm)
  have hab : _root_.LowDimensionalTopology.Geometry.Mobius.ReflectionBridge.toComplex R a = b := by
    change e.symm (R (e a)) = b
    rw [← hrR, hrab, Homeomorph.symm_apply_apply]
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.ReflectionBridge.unitSphere_eq_reciprocal_conjugation] at hab
  change _root_.LowDimensionalTopology.Geometry.Mobius.reciprocal (_root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation a) = b at hab
  rw [← hab, _root_.LowDimensionalTopology.Geometry.Mobius.reciprocal_mem_exterior_iff_disc]
  induction a using OnePoint.rec with
  | infty => simp only [_root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation_infty]
  | coe z => simp only [_root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc, Complex.norm_conj]

/-- A disc-preserving elliptic has exactly one fixed point in the actual unit disc. -/
theorem elliptic_unitDisc_existsUnique_fixed (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf
  : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (hp : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    ∃! z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc, f.val z.val = z.val := by
  obtain ⟨a,b,_,ha,_,hab,hfix⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_fixed_pair_of_preserved_disc f hf
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc hp
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle] at ha hab
  change _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexInversePair (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle 0 1) a b at hab
  have haCase : a ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ∨ a ∈ _root_.LowDimensionalTopology.Geometry.Mobius.extendedUnitDiscExterior := by
    change a ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ∪ _root_.LowDimensionalTopology.Geometry.Mobius.extendedUnitDiscExterior
    rw [← _root_.LowDimensionalTopology.Geometry.Mobius.unitCircle_compl_eq_disc_union_exterior]
    exact ha
  rcases haCase with haD | haE
  · have hbE := (unitCircle_inverse_pair_disc_exterior hab).mp haD
    have hbnot : b ∉ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := fun hbD =>
      Set.disjoint_left.mp _root_.LowDimensionalTopology.Geometry.Mobius.disjoint_extendedUnitDisc_exterior hbD hbE
    refine ⟨⟨a,haD⟩, (hfix a).mpr (Or.inl rfl), ?_⟩
    intro z hz
    rcases (hfix z.val).mp hz with hza | hzb
    · exact Subtype.ext hza
    · exact False.elim (hbnot (hzb ▸ z.property))
  · have hbD := (unitCircle_inverse_pair_disc_exterior hab.symm).mpr haE
    have hanot : a ∉ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := fun haD =>
      Set.disjoint_left.mp _root_.LowDimensionalTopology.Geometry.Mobius.disjoint_extendedUnitDisc_exterior haD haE
    refine ⟨⟨b,hbD⟩, (hfix b).mpr (Or.inr rfl), ?_⟩
    intro z hz
    rcases (hfix z.val).mp hz with hza | hzb
    · exact False.elim (hanot (hza ▸ z.property))
    · exact Subtype.ext hzb

/-- The finite actual elliptic vertices lying inside the invariant unit disc. -/
def fuchsianDiscVertexSubaction (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    SubMulAction H _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex where
  carrier := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusVertices H ∩ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
  smul_mem' := by
    intro f z hz
    refine ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusVertices_smul H f hz.1, ?_⟩
    rw [← hp f]
    exact ⟨z,hz.2,rfl⟩

abbrev FuchsianDiscVertex (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :=
  fuchsianDiscVertexSubaction H hp

instance finiteFuchsianDiscVertex (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    Finite (FuchsianDiscVertex H hp) :=
  ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusVertices_finite H).inter_of_left
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc).to_subtype

theorem finiteFuchsianDiscVertex_fixedBy_card (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (g : H) (hg : g ≠ 1) : Nat.card (MulAction.fixedBy (FuchsianDiscVertex H hp) g) = 1 := by
  have hE := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.finite_H3_orbit_all_elliptic H _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
    (show (MulAction.orbit H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).Finite from
      Set.finite_range (fun f : H => f •
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ))
    g.val g.property (fun he => hg (Subtype.ext he))
  obtain ⟨z,hz,huniq⟩ := elliptic_unitDisc_existsUnique_fixed g.val hE (hp g)
  let v : FuchsianDiscVertex H hp := ⟨z.val, ⟨⟨g,hg,hz⟩,z.property⟩⟩
  have hset : MulAction.fixedBy (FuchsianDiscVertex H hp) g = {v} := by
    ext w
    change g • w = w ↔ w = v
    constructor
    · intro hw
      have he : (⟨w.val,w.property.2⟩ :
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) = z := huniq _ (congrArg Subtype.val hw)
      exact Subtype.ext (congrArg (fun u : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc => u.val)
        he)
    · rintro rfl
      exact Subtype.ext hz
  change (MulAction.fixedBy (FuchsianDiscVertex H hp) g).ncard = 1
  rw [hset,Set.ncard_singleton]

theorem finiteFuchsianDiscVertex_stabilizer_card (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (z : FuchsianDiscVertex H hp) : 2 ≤ Nat.card (MulAction.stabilizer H z) := by
  obtain ⟨g,hg,hfix⟩ := z.property.1
  have hm : g ∈ MulAction.stabilizer H z := Subtype.ext hfix
  have hn : (⟨g,hm⟩ : MulAction.stabilizer H z) ≠ 1 := by
    intro he
    exact hg (congrArg Subtype.val he)
  let : Nontrivial (MulAction.stabilizer H z) := ⟨⟨_,_,hn⟩⟩
  let : Fintype (MulAction.stabilizer H z) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using
    (Nat.succ_le_of_lt (Fintype.one_lt_card : 1 < Fintype.card (MulAction.stabilizer H z)))


abbrev FuchsianDiscVertexOrbit (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :=
  MulAction.orbitRel.Quotient H (FuchsianDiscVertex H hp)

instance fintypeFuchsianDiscVertexOrbit (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    Fintype (FuchsianDiscVertexOrbit H hp) := Fintype.ofFinite _

theorem finiteFuchsianDiscVertex_burnside (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    Nat.card (FuchsianDiscVertexOrbit H hp) * Nat.card H =
      Nat.card (FuchsianDiscVertex H hp) + (Nat.card H - 1) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  let : Fintype (FuchsianDiscVertex H hp) := Fintype.ofFinite _
  let : Fintype (FuchsianDiscVertexOrbit H hp) := Fintype.ofFinite _
  let (g : H) : Fintype (MulAction.fixedBy (FuchsianDiscVertex H hp) g) := Fintype.ofFinite _
  have hfix (g : H) : Fintype.card (MulAction.fixedBy (FuchsianDiscVertex H hp) g) =
      if g = 1 then Fintype.card (FuchsianDiscVertex H hp) else 1 := by
    split_ifs with hg
    · subst g
      have he : MulAction.fixedBy (FuchsianDiscVertex H hp) (1 : H) = Set.univ := by
        ext z
        exact ⟨fun _ => mem_univ _, fun _ => one_smul H z⟩
      have hc : Nat.card (MulAction.fixedBy (FuchsianDiscVertex H hp) (1 : H)) =
          Nat.card (FuchsianDiscVertex H hp) := by
        rw [he]
        exact Nat.card_congr (Equiv.Set.univ _)
      simpa only [Nat.card_eq_fintype_card] using hc
    · simpa only [Nat.card_eq_fintype_card] using finiteFuchsianDiscVertex_fixedBy_card H hp g hg
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H (FuchsianDiscVertex H hp)
  simp only [Nat.card_eq_fintype_card]
  rw [← hb]
  simp_rw [hfix]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : H))]
  have he : ∑ g ∈ Finset.univ.erase (1 : H),
      (if g = 1 then Fintype.card (FuchsianDiscVertex H hp) else 1) =
      Fintype.card H - 1 := by
    have hval : ∀ g ∈ Finset.univ.erase (1 : H),
        (if g = 1 then Fintype.card (FuchsianDiscVertex H hp) else 1) = 1 := by
      intro g hg
      exact ite_eq_right (Finset.ne_of_mem_erase hg)
    rw [Finset.sum_congr rfl hval]
    simp
  rw [he]
  simp only [ite_true]
  omega

theorem finiteFuchsianDiscVertex_card_sum_orbits (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    Nat.card (FuchsianDiscVertex H hp) =
      ∑ o : FuchsianDiscVertexOrbit H hp, Nat.card (MulAction.orbit H o.out) := by
  classical
  let : Fintype (FuchsianDiscVertex H hp) := Fintype.ofFinite _
  let (o : FuchsianDiscVertexOrbit H hp) : Fintype (MulAction.orbit H o.out) := Fintype.ofFinite _
  simpa only [Fintype.card_sigma, Nat.card_eq_fintype_card] using
    Fintype.card_congr (MulAction.selfEquivSigmaOrbits H (FuchsianDiscVertex H hp))

theorem finiteFuchsianDiscVertex_card_twice_le (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    2 * Nat.card (FuchsianDiscVertex H hp) ≤ Nat.card (FuchsianDiscVertexOrbit H hp) * Nat.card H := by
  classical
  rw [finiteFuchsianDiscVertex_card_sum_orbits, Finset.mul_sum]
  calc
    ∑ o : FuchsianDiscVertexOrbit H hp, 2 * Nat.card (MulAction.orbit H o.out) ≤
        ∑ _ : FuchsianDiscVertexOrbit H hp, Nat.card H := by
      apply Finset.sum_le_sum
      intro o _
      have hs := finiteFuchsianDiscVertex_stabilizer_card H hp o.out
      have he : Nat.card (MulAction.orbit H o.out) * Nat.card (MulAction.stabilizer H o.out) = Nat.card H := by
        rw [← Nat.card_prod]
        exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H o.out)
      nlinarith
    _ = Nat.card (FuchsianDiscVertexOrbit H hp) * Nat.card H := by
      simp [Nat.card_eq_fintype_card]


theorem finiteFuchsianDiscVertex_card_one (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    [Nontrivial H] (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    Nat.card (FuchsianDiscVertex H hp) = 1 := by
  obtain ⟨g,hg⟩ := exists_ne (1 : H)
  have hE := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.finite_H3_orbit_all_elliptic H _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
    (show (MulAction.orbit H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).Finite from
      Set.finite_range (fun f : H => f •
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ))
    g.val g.property (fun he => hg (Subtype.ext he))
  obtain ⟨z,hz,_⟩ := elliptic_unitDisc_existsUnique_fixed g.val hE (hp g)
  let : Nonempty (FuchsianDiscVertex H hp) := ⟨⟨z.val, ⟨⟨g,hg,hz⟩,z.property⟩⟩⟩
  have hx : 0 < Nat.card (FuchsianDiscVertex H hp) := Nat.card_pos
  have hN : 2 ≤ Nat.card H := by
    let : Fintype H := Fintype.ofFinite H
    simpa only [Nat.card_eq_fintype_card] using (Nat.succ_le_of_lt (Fintype.one_lt_card : 1 < Fintype.card H))
  have hb := finiteFuchsianDiscVertex_burnside H hp
  have hu := finiteFuchsianDiscVertex_card_twice_le H hp
  have hsub : Nat.card H - 1 + 1 = Nat.card H := Nat.sub_add_cancel (by omega)
  have hm : Nat.card (FuchsianDiscVertexOrbit H hp) = 1 := by
    have hml : 1 ≤ Nat.card (FuchsianDiscVertexOrbit H hp) := by
      by_contra hn
      have he : Nat.card (FuchsianDiscVertexOrbit H hp) = 0 := by omega
      rw [he,zero_mul] at hb
      omega
    have hmu : Nat.card (FuchsianDiscVertexOrbit H hp) < 2 := by
      by_contra hn
      have he : 2 ≤ Nat.card (FuchsianDiscVertexOrbit H hp) := by omega
      nlinarith
    omega
  rw [hm,one_mul] at hb
  omega

/-- A finite group preserving the actual unit disc has a common interior fixed point and is cyclic. -/
theorem finiteMobius_preserves_unitDisc_isCyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hp : ∀ f : H, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) : IsCyclic H := by
  cases subsingleton_or_nontrivial H with
  | inl hs =>
    let : Subsingleton H := hs
    infer_instance
  | inr hn =>
    let : Nontrivial H := hn
    obtain ⟨v,hv⟩ := Nat.card_eq_one_iff_exists.mp (finiteFuchsianDiscVertex_card_one H hp)
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.finiteMobius_fix_boundary_isCyclic H v.val (by
      intro g hg
      exact congrArg Subtype.val (hv ((⟨g,hg⟩ : H) • v)))


/-- Disc normalization transports the finite cyclic result to every actual geometric disc. -/
theorem finiteMobius_preserves_disc_isCyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    {D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (hp : ∀ f : H, f.val.val '' D = D) : IsCyclic H := by
  obtain ⟨q,hq⟩ := hD.normalize
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  let e : H ≃* K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  let : Finite K := Finite.of_surjective e e.surjective
  have hKp : ∀ f : K, f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    intro f
    obtain ⟨g,hg,hgf⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
      q H f.val).mp f.property
    rw [← hgf]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobius_disc_conjugate_preserves g q hq (hp ⟨g,hg⟩)
  let : IsCyclic K := finiteMobius_preserves_unitDisc_isCyclic K hKp
  exact e.isCyclic.mpr inferInstance

/-- Finite Fuchsian groups are cyclic, with no restriction on the chosen invariant disc. -/
theorem finiteFuchsianGroup_isCyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (hH : _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup H) : IsCyclic H := by
  obtain ⟨D⟩ := (fuchsianDisc_exists_iff H).mpr hH
  exact finiteMobius_preserves_disc_isCyclic H D.isDisc D.image_eq

/-- The all-elliptic assertion uses genuine H3 common fixed points and actual discreteness. -/
theorem FuchsianDisc.all_elliptic_finite_cyclic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hE : ∀ f ∈ H, f ≠ 1 → _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) :
    Finite H ∧ IsCyclic H := by
  obtain ⟨q,hq⟩ := (_root_.LowDimensionalTopology.Geometry.Mobius.all_nonidentity_elliptic_iff_common_halfSpace_fixedPoint H).mp hE
  let : Finite H := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_finite_of_common_H3_fixed H D.discrete q hq
  exact ⟨inferInstance,finiteMobius_preserves_disc_isCyclic H D.isDisc D.image_eq⟩

theorem fuchsianGroup_all_elliptic_finite_cyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup H) (hE : ∀ f ∈ H, f ≠ 1 →
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) :
    Finite H ∧ IsCyclic H := by
  obtain ⟨D⟩ := (fuchsianDisc_exists_iff H).mpr hH
  exact D.all_elliptic_finite_cyclic hE

/-- Every Fuchsian subgroup with a common boundary-sphere point is itself cyclic. -/
theorem FuchsianDisc.common_fixed_isCyclic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz : ∀ f ∈ H, f.val z = z) : IsCyclic H := by
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H z
  let : IsCyclic K := D.stabilizer_isCyclic z
  let e : H →* K :=
    { toFun := fun f => ⟨f.val,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H z
      f.val).mpr ⟨f.property,hz f.val f.property⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact isCyclic_of_injective e (fun a b h =>
    Subtype.ext (congrArg (fun k : K => k.val) h))

end LowDimensionalTopology.Geometry.Fuchsian
