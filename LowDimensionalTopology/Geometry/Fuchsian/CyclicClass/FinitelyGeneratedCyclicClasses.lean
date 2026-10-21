module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.FinitelySidedDirichlet
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.CyclicClassRepresentatives
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeometricFuchsianModels
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Original finite generation supplies a genuinely finite actual maximal
cyclic class space of either type, through the proved finite original
Dirichlet polygon rather than a finite-sidedness assumption. -/
theorem finitelyGenerated_unitDisc_cyclic_classes_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hFG : H.FG) (kind :
      FuchsianCyclicKind) :
    Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc kind) := by
  obtain ⟨z,hz,hfree⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_open_free_point H P.discrete P.domain.carrier
    P.domain.isOpen P.domain.isConnected.nonempty
  let w : P.domain.carrier := ⟨z,hz⟩
  have hw : IsDirichletCenter P w := by
    intro g hg
    exact hfree g (congrArg Subtype.val hg)
  have hS := finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  exact finite_sided_polygon_elliptic_parabolic_classes_finite
    (dirichletDomain_isConvexFuchsianPolygon P w hw) hS.to_subtype kind

/-- Conjugating actual maps preserves their elliptic or parabolic type. -/
theorem mobiusCyclicType_isConj (kind : FuchsianCyclicKind)
    {f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (h : IsConj f g) :
    MobiusCyclicType kind f ↔ MobiusCyclicType kind g := by
  cases kind with
  | elliptic => exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_isConj h
  | parabolic => exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj h

/-- Exact whole-domain conjugacy transports the actual typed fixed-point sets,
including the original interior choice for elliptics. -/
theorem fuchsianCyclicFixedPoints_conjugation_mem_iff
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (D' : FuchsianDisc
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H))
    (hDomain : D'.carrier = q.val '' D.carrier) (kind : FuchsianCyclicKind)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    p ∈ fuchsianCyclicFixedPoints D kind ↔ q.val p ∈ fuchsianCyclicFixedPoints D' kind := by
  constructor
  · rintro ⟨hp,f,hfH,hft,hfp⟩
    refine ⟨?_,q*f*q⁻¹,?_,?_,?_⟩
    · intro hk
      rw [hDomain]
      exact ⟨p,hp hk,rfl⟩
    · exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨f,hfH,rfl⟩
    · exact (mobiusCyclicType_isConj kind (isConj_iff.mpr ⟨q,rfl⟩)).mp hft
    · change q.val (f.val (q.val.symm (q.val p))) = q.val p
      rw [Equiv.symm_apply_apply,hfp]
  · rintro ⟨hp,f',hf'H,hf't,hf'p⟩
    obtain ⟨f,hfH,hfeq⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f').mp hf'H
    refine ⟨?_,f,hfH,?_,?_⟩
    · intro hk
      have hpD : q.val p ∈ q.val '' D.carrier := hDomain ▸ hp hk
      obtain ⟨u,hu,hup⟩ := hpD
      exact q.val.injective hup ▸ hu
    · have hft : MobiusCyclicType kind (q*f*q⁻¹) := hfeq.symm ▸ hf't
      exact (mobiusCyclicType_isConj kind (isConj_iff.mpr ⟨q,rfl⟩)).mpr hft
    · apply q.val.injective
      rw [←hfeq] at hf'p
      change q.val (f.val (q.val.symm (q.val p))) = q.val p at hf'p
      simpa only [Equiv.symm_apply_apply] using hf'p

/-- The exact actual point-set equivalence induced by the specified whole-group
and whole-domain conjugacy. -/
def fuchsianCyclicFixedPointsConjugationEquiv
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (D' : FuchsianDisc
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H))
    (hDomain : D'.carrier = q.val '' D.carrier) (kind : FuchsianCyclicKind) :
    fuchsianCyclicFixedPoints D kind ≃ fuchsianCyclicFixedPoints D' kind where
  toFun p := ⟨q.val p.val,(fuchsianCyclicFixedPoints_conjugation_mem_iff D q D' hDomain kind p.val).mp p.property⟩
  invFun p := ⟨q.val.symm p.val,(fuchsianCyclicFixedPoints_conjugation_mem_iff D q D' hDomain kind _).mpr
    (by simpa only [Equiv.apply_symm_apply] using p.property)⟩
  left_inv p := Subtype.ext (q.val.symm_apply_apply p.val)
  right_inv p := Subtype.ext (q.val.apply_symm_apply p.val)

/-- Actual point orbits are preserved and reflected when both the original
group and its point set are transported by specified genuine equivalences. -/
theorem orbitRel_iff_of_equivariant_groupEquiv
    {G G' X Y : Type*} [Group G] [Group G'] [MulAction G X] [MulAction G' Y]
    (e : G ≃* G') (f : X ≃ Y) (h : ∀ (g : G) (x : X), f (g • x) = e g • f x)
    (x y : X) : MulAction.orbitRel G X x y ↔ MulAction.orbitRel G' Y (f x) (f y) := by
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff,
    MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨e g,(h g y).symm.trans (congrArg f hg)⟩
  · rintro ⟨g',hg'⟩
    obtain ⟨g,rfl⟩ := e.surjective g'
    exact ⟨g,f.injective ((h g y).trans hg')⟩

/-- The true fixed-point equivalence intertwines the same actual subgroup
conjugacy used for the original group elements. -/
theorem fuchsianCyclicFixedPointsConjugationEquiv_smul
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (D' : FuchsianDisc
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H))
    (hDomain : D'.carrier = q.val '' D.carrier) (kind : FuchsianCyclicKind)
    (g : H) (p : fuchsianCyclicFixedPoints D kind) :
    fuchsianCyclicFixedPointsConjugationEquiv D q D' hDomain kind (g • p) =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g •
        fuchsianCyclicFixedPointsConjugationEquiv D q D' hDomain kind p := by
  apply Subtype.ext
  change q.val (g.val.val p.val) = q.val (g.val.val (q.val.symm (q.val p.val)))
  rw [Equiv.symm_apply_apply]

/-- Genuine conjugacy of the whole original model induces an equivalence of
the literal maximal cyclic subgroup conjugacy classes of each actual type. -/
def fuchsianCyclicConjugacyClassesConjugationEquiv
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (D' : FuchsianDisc
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H))
    (hDomain : D'.carrier = q.val '' D.carrier) (kind : FuchsianCyclicKind) :
    FuchsianCyclicConjugacyClasses D kind ≃ FuchsianCyclicConjugacyClasses D' kind :=
  (fuchsianCyclicConjugacyClassesEquiv D kind).trans
    ((Quotient.congr (fuchsianCyclicFixedPointsConjugationEquiv D q D' hDomain kind)
      (orbitRel_iff_of_equivariant_groupEquiv
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H)
        (fuchsianCyclicFixedPointsConjugationEquiv D q D' hDomain kind)
        (fuchsianCyclicFixedPointsConjugationEquiv_smul D q D' hDomain kind))).trans
      (fuchsianCyclicConjugacyClassesEquiv D' kind).symm)

/-- For an arbitrary original non-elementary finitely generated Fuchsian
group and its actual geometric disc, the true maximal elliptic or parabolic
cyclic conjugacy-class space is finite. Standard-disc normalization is proved
and transported back; it is not an additional model hypothesis. -/
theorem finitelyGenerated_cyclic_classes_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hFG : H.FG) (kind :
      FuchsianCyclicKind) :
    Finite (FuchsianCyclicConjugacyClasses D kind) := by
  let q := geometricDiscNormalizer D
  let P := geometricDiscData D
  let e := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have hNE' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (geometricDiscGroup
    D) := hNE.conjugation q
  have : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hFG
  have : Group.FG (geometricDiscGroup D) := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  have hFG' : (geometricDiscGroup D).FG := (Group.fg_iff_subgroup_fg _).mp inferInstance
  have hFin : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc kind) :=
    finitelyGenerated_unitDisc_cyclic_classes_finite P hNE' hFG' kind
  let := hFin
  have hDomain : P.asFuchsianDisc.carrier = q.val '' D.carrier :=
    (geometricDiscNormalizer_image D).symm
  exact Finite.of_equiv _ (fuchsianCyclicConjugacyClassesConjugationEquiv D q P.asFuchsianDisc hDomain kind).symm

/-- The original finite-generation hypothesis supplies both finiteness of the
actual class index and the genuine unique nonidentity conjugacy representatives
in the chosen original maximal cyclic subgroup family. -/
theorem finitelyGenerated_cyclic_unique_representatives
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hFG : H.FG) (kind :
      FuchsianCyclicKind) :
    Finite (FuchsianCyclicConjugacyClasses D kind) ∧
      ∀ f : H, MobiusCyclicType kind f.val →
        ∃! r : FuchsianCyclicRepresentativeMembers D kind, IsConj f r.2.val :=
  ⟨finitelyGenerated_cyclic_classes_finite D hNE hFG kind,
    fuchsianCyclicRepresentativeMembers_unique_conjugate D kind⟩

end LowDimensionalTopology.Geometry.Fuchsian
