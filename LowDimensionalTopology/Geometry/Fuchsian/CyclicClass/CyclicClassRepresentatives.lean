module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FinitePolygonParabolicClasses
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.BoundaryCyclicRepresentatives
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Any two actual nonidentity members of one genuine cyclic Mobius subgroup have the
same full actual sphere fixed-point set. -/
theorem cyclic_nonidentity_same_fixedPoints (K : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hK : IsCyclic K)
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ∈ K) (hg : g ∈ K) (hfn : f ≠
      1) (hgn : g ≠ 1) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusSameFixedPoints f g := by
  have := hK
  obtain ⟨a,ha⟩ := exists_zpow_surjective K
  obtain ⟨m,hm⟩ := ha ⟨f,hf⟩
  obtain ⟨n,hn⟩ := ha ⟨g,hg⟩
  have hm' : a.val^m = f := congrArg Subtype.val hm
  have hn' : a.val^n = g := congrArg Subtype.val hn
  have han : a.val ≠ 1 := by intro he; exact hfn (by rw [←hm',he,one_zpow])
  have hfm : a.val^m ≠ 1 := hm'.symm ▸ hfn
  have hgn' : a.val^n ≠ 1 := hn'.symm ▸ hgn
  intro p
  have h1 := mobius_zpow_same_fixedPoints a.val han m hfm p
  have h2 := mobius_zpow_same_fixedPoints a.val han n hgn' p
  rw [hm'] at h1
  rw [hn'] at h2
  exact h1.symm.trans h2

/-- Every nonidentity member of the genuine stabilizer has the same required unique
fixed point, in the actual disc for elliptics and in the sphere for parabolics. -/
theorem fuchsianCyclicFixedPoint_unique_of_nonidentity_mem
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (kind :
      FuchsianCyclicKind)
    (p : fuchsianCyclicFixedPoints D kind) (g : H) (hgn : g ≠ 1)
    (hgp : g.val.val p.val = p.val) (q : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hgq : g.val.val
      q = q)
    (hqD : kind = .elliptic → q ∈ D.carrier) : q = p.val := by
  obtain ⟨f,hfH,hft,hfp⟩ := p.property.2
  have hfK : f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val f).mpr ⟨hfH,hfp⟩
  have hgK : g.val ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val
      g.val).mpr ⟨g.property,hgp⟩
  have hfn : f ≠ 1 := by cases kind <;> exact hft.1
  have hsame := cyclic_nonidentity_same_fixedPoints (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val)
    (D.stabilizer_isCyclic p.val) f g.val hfK hgK hfn
    (fun he => hgn (Subtype.ext he)) q
  have hfq := hsame.mpr hgq
  cases kind with
  | elliptic =>
    obtain ⟨x,hx,hunique⟩ := elliptic_disc_existsUnique_fixed f hft D.isDisc (D.image_eq ⟨f,hfH⟩)
    have hp := hunique ⟨p.val,p.property.1 rfl⟩ hfp
    have hq := hunique ⟨q,hqD rfl⟩ hfq
    exact congrArg Subtype.val (hq.trans hp.symm)
  | parabolic =>
    obtain ⟨x,hx⟩ := hft.2
    exact ((hx q).mp hfq).trans ((hx p.val).mp hfp).symm

/-- A conjugator between two actual nonidentity stabilizer members transports the
actual geometric fixed point into the other original-group fixed-point orbit. -/
theorem typed_fixed_points_orbit_of_conjugate_nonidentity
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (kind :
      FuchsianCyclicKind)
    (p q : fuchsianCyclicFixedPoints D kind) (f g : H) (_hfn : f ≠ 1) (hgn : g ≠ 1)
    (hfp : f.val.val p.val = p.val) (hgq : g.val.val q.val = q.val) (hfg : IsConj f g) :
    MulAction.orbitRel H (fuchsianCyclicFixedPoints D kind) p q := by
  obtain ⟨h,hh⟩ := isConj_iff.mp hfg
  have hgp : g.val.val (h.val.val p.val) = h.val.val p.val := by
    rw [←hh]
    change h.val.val (f.val.val (h.val.val.symm (h.val.val p.val))) = _
    rw [Equiv.symm_apply_apply,hfp]
  have hpq : h • p = q := by
    apply Subtype.ext
    exact fuchsianCyclicFixedPoint_unique_of_nonidentity_mem D kind q g hgn hgq _ hgp
      (fun he => D.invariant h p.val (p.property.1 he))
  apply (MulAction.orbitRel_apply).mpr
  apply MulAction.mem_orbit_iff.mpr
  exact ⟨h⁻¹,by rw [←hpq,inv_smul_smul]⟩

/-- Inside one genuine elliptic or parabolic fixed-point stabilizer, nonidentity
conjugacy inside the original Fuchsian group is literal element equality. -/
theorem typed_stabilizer_nonidentity_isConj_iff_eq
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (kind :
      FuchsianCyclicKind)
    (p : fuchsianCyclicFixedPoints D kind) (f g : H) (_hfn : f ≠ 1) (hgn : g ≠ 1)
    (hfp : f.val.val p.val = p.val) (hgp : g.val.val p.val = p.val) : IsConj f g ↔ f = g := by
  constructor
  · intro hfg
    obtain ⟨h,hh⟩ := isConj_iff.mp hfg
    have hghp : g.val.val (h.val.val p.val) = h.val.val p.val := by
      rw [←hh]
      change h.val.val (f.val.val (h.val.val.symm (h.val.val p.val))) = _
      rw [Equiv.symm_apply_apply,hfp]
    have hhp : h.val.val p.val = p.val :=
      fuchsianCyclicFixedPoint_unique_of_nonidentity_mem D kind p g hgn hgp _ hghp
        (fun he => D.invariant h p.val (p.property.1 he))
    have hc := fuchsian_fixed_stabilizer_commute D p.val h f hhp hfp
    rw [hc.eq,mul_assoc,mul_inv_cancel,mul_one] at hh
    exact hh
  · rintro rfl
    exact IsConj.refl _


/-- Nonidentity actual members of two geometric maximal cyclic subgroups can be
conjugate only when the actual maximal subgroups represent the same original class. -/
theorem maximal_cyclic_classes_eq_of_nonidentity_isConj
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (kind :
      FuchsianCyclicKind)
    (K L : fuchsianMaximalCyclicSubgroups H kind) (f g : H)
    (hfK : f.val ∈ K.val) (hgL : g.val ∈ L.val) (hfn : f ≠ 1) (hgn : g ≠ 1)
    (hfg : IsConj f g) :
    (Quotient.mk (fuchsianMaximalCyclicConjugacySetoid D kind) K : FuchsianCyclicConjugacyClasses D kind) =
      Quotient.mk (fuchsianMaximalCyclicConjugacySetoid D kind) L := by
  let E := fuchsianCyclicPointStabilizerEquiv D kind
  let p := E.symm K
  let q := E.symm L
  have hpK : fuchsianCyclicPointStabilizer D kind p = K := E.apply_symm_apply K
  have hqL : fuchsianCyclicPointStabilizer D kind q = L := E.apply_symm_apply L
  have hfp : f.val.val p.val = p.val := by
    have hh : f.val ∈ (fuchsianCyclicPointStabilizer D kind p).val := hpK.symm ▸ hfK
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val f.val).mp hh).2
  have hgq : g.val.val q.val = q.val := by
    have hh : g.val ∈ (fuchsianCyclicPointStabilizer D kind q).val := hqL.symm ▸ hgL
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H q.val g.val).mp hh).2
  apply Quotient.sound
  exact typed_fixed_points_orbit_of_conjugate_nonidentity D kind p q f g hfn hgn hfp hgq hfg


/-- A chosen representative is an actual geometric maximal cyclic subgroup in the original group. -/
def chosenFuchsianMaximalCyclic {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind) (c : FuchsianCyclicConjugacyClasses D kind) :
    fuchsianMaximalCyclicSubgroups H kind := Quotient.out c

/-- The actual nonidentity original-group members of the chosen actual maximal subgroup family. -/
def FuchsianCyclicRepresentativeMembers {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (kind : FuchsianCyclicKind) :=
  Σ c : FuchsianCyclicConjugacyClasses D kind,
    {f : H // f ≠ 1 ∧ f.val ∈ (chosenFuchsianMaximalCyclic D kind c).val}

/-- Every actual element of a specified geometric type is conjugate to exactly one
actual nonidentity member in exactly one chosen genuine maximal cyclic subgroup.
The assertion does not assume a finite class set; actual finite-sidedness supplies
that independent finiteness when required. -/
theorem fuchsianCyclicRepresentativeMembers_unique_conjugate
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (kind :
      FuchsianCyclicKind)
    (f : H) (hf : MobiusCyclicType kind f.val) :
    ∃! r : FuchsianCyclicRepresentativeMembers D kind, IsConj f r.2.val := by
  classical
  have hfn : f ≠ 1 := by cases kind <;> exact fun he => hf.1 (congrArg Subtype.val he)
  have hp_exists : ∃ p : fuchsianCyclicFixedPoints D kind, f.val.val p.val = p.val := by
    cases kind with
    | elliptic =>
      obtain ⟨p,hp,_hu⟩ := elliptic_disc_existsUnique_fixed f.val hf D.isDisc (D.image_eq f)
      exact ⟨⟨p.val,⟨fun _ => p.property,f.val,f.property,hf,hp⟩⟩,hp⟩
    | parabolic =>
      obtain ⟨p,hp⟩ := hf.2
      have hpf := (hp p).mpr rfl
      refine ⟨⟨p,⟨?_,f.val,f.property,hf,hpf⟩⟩,hpf⟩
      intro he
      cases he
  obtain ⟨p,hfp⟩ := hp_exists
  let K := fuchsianCyclicPointStabilizer D kind p
  let c : FuchsianCyclicConjugacyClasses D kind := Quotient.mk (fuchsianMaximalCyclicConjugacySetoid D kind) K
  let L := chosenFuchsianMaximalCyclic D kind c
  have hcL : Quotient.mk (fuchsianMaximalCyclicConjugacySetoid D kind) L = c := Quotient.out_eq c
  have hKL : (fuchsianMaximalCyclicConjugacySetoid D kind).r K L := Quotient.exact hcL.symm
  obtain ⟨h,hh⟩ := (fuchsianMaximalCyclicConjugacySetoid_iff D kind K L).mp hKL
  have hfK : f.val ∈ K.val := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H
    p.val f.val).mpr ⟨f.property,hfp⟩
  let F := h*f*h⁻¹
  have hfr : IsConj f F := isConj_iff.mpr ⟨h,rfl⟩
  have hFn : F ≠ 1 := by
    intro he
    exact hfn (isConj_one_left.mp (he ▸ hfr))
  have hFL : F.val ∈ L.val := by
    rw [←hh]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff h.val K.val
      F.val).mpr ⟨f.val,hfK,rfl⟩
  let r : FuchsianCyclicRepresentativeMembers D kind := ⟨c,⟨F,hFn,hFL⟩⟩
  refine ⟨r,hfr,?_⟩
  rintro ⟨c',G⟩ hG
  have hc : c' = c := by
    have he := maximal_cyclic_classes_eq_of_nonidentity_isConj D kind
      (chosenFuchsianMaximalCyclic D kind c') L G.val F G.property.2 hFL G.property.1 hFn
      (hG.symm.trans hfr)
    change Quotient.mk (fuchsianMaximalCyclicConjugacySetoid D kind) (Quotient.out c') =
      Quotient.mk (fuchsianMaximalCyclicConjugacySetoid D kind) (Quotient.out c) at he
    simpa only [Quotient.out_eq] using he
  subst c'
  let pL := (fuchsianCyclicPointStabilizerEquiv D kind).symm L
  have hpL : fuchsianCyclicPointStabilizer D kind pL = L :=
    (fuchsianCyclicPointStabilizerEquiv D kind).apply_symm_apply L
  have hGfix : G.val.val.val pL.val = pL.val := by
    have hhG : G.val.val ∈ (fuchsianCyclicPointStabilizer D kind pL).val := by
      rw [hpL]
      exact G.property.2
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H pL.val G.val.val).mp
      hhG).2
  have hFfix : F.val.val pL.val = pL.val := by
    have hhF : F.val ∈ (fuchsianCyclicPointStabilizer D kind pL).val := by
      rw [hpL]
      exact hFL
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H pL.val F.val).mp hhF).2
  have hGF : G.val = F :=
    (typed_stabilizer_nonidentity_isConj_iff_eq D kind pL G.val F G.property.1 hFn hGfix hFfix).mp
      (hG.symm.trans hfr)
  exact congrArg (fun v : {g : H // g ≠ 1 ∧ g.val ∈ L.val} =>
    (⟨c,v⟩ : FuchsianCyclicRepresentativeMembers D kind)) (Subtype.ext hGF)


/-- Under literal actual finite-sidedness the chosen original maximal cyclic subgroup
family is finite and supplies the actual unique representatives of each specified type.
This is an auxiliary finite-polygon form, without claiming finite generation implies it. -/
theorem finite_sided_polygon_cyclic_unique_representatives
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hFin : Finite (FuchsianPolygonSides P D))
    (kind : FuchsianCyclicKind) :
    Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc kind) ∧
    ∀ f : H, MobiusCyclicType kind f.val →
      ∃! r : FuchsianCyclicRepresentativeMembers P.asFuchsianDisc kind, IsConj f r.2.val := by
  exact ⟨finite_sided_polygon_elliptic_parabolic_classes_finite hD hFin kind,
    fuchsianCyclicRepresentativeMembers_unique_conjugate P.asFuchsianDisc kind⟩

end LowDimensionalTopology.Geometry.Fuchsian
