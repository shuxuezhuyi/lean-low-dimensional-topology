/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeneralizedReflectionGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenConjugation
@[expose] public section
open Set
open scoped Topology OnePoint Pointwise UpperHalfPlane MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- The genuine complementary geometric disc on the chosen side of a complete mirror. -/
def geometricContainingSide (S : _root_.LowDimensionalTopology.Geometry.Mobius.ComplexGeneralizedCircle) (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  connectedComponentIn S.valᶜ ξ

theorem geometricContainingSide_isDisc (S : _root_.LowDimensionalTopology.Geometry.Mobius.ComplexGeneralizedCircle) (ξ :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hξ : ξ∉S.val) : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc (geometricContainingSide S ξ):=
  ⟨S.val,S.property,ξ,hξ,rfl⟩

theorem geometricContainingSide_isOpen (S : _root_.LowDimensionalTopology.Geometry.Mobius.ComplexGeneralizedCircle) (ξ :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hξ : ξ∉S.val) : IsOpen (geometricContainingSide S ξ):=
  (geometricContainingSide_isDisc S ξ hξ).isOpen

theorem mem_geometricContainingSide (S : _root_.LowDimensionalTopology.Geometry.Mobius.ComplexGeneralizedCircle) (ξ :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hξ : ξ∉S.val) : ξ∈geometricContainingSide S ξ:=mem_connectedComponentIn hξ

theorem geometricContainingSide_disjoint (S : _root_.LowDimensionalTopology.Geometry.Mobius.ComplexGeneralizedCircle) (ξ
  : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    Disjoint (geometricContainingSide S ξ) S.val:=by
  apply Set.disjoint_left.mpr
  intro z hz hzS
  exact connectedComponentIn_subset S.valᶜ ξ hz hzS

/-- Actual sphere homeomorphisms carry the entire containing component to its corresponding component. -/
theorem geometricContainingSide_image (S : _root_.LowDimensionalTopology.Geometry.Mobius.ComplexGeneralizedCircle) (ξ :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hξ : ξ∉S.val) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    q.val '' geometricContainingSide S ξ=geometricContainingSide (S.image q) (q.val ξ):=by
  have h:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).image_connectedComponentIn (show
    ξ∈S.valᶜ from hξ)
  change q.val '' connectedComponentIn S.valᶜ ξ=
    connectedComponentIn (q.val '' S.valᶜ) (q.val ξ) at h
  rw [q.val.image_compl] at h
  exact h

theorem geometricContainingSide_mem_conjugation (S :
  _root_.LowDimensionalTopology.Geometry.Mobius.ComplexGeneralizedCircle) (ξ z :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hξ : ξ∉S.val) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    q.val z∈geometricContainingSide (S.image q) (q.val ξ) ↔ z∈geometricContainingSide S ξ:=by
  rw [←geometricContainingSide_image S ξ hξ q]
  constructor
  · rintro ⟨w,hw,he⟩
    exact q.val.injective he ▸ hw
  · exact fun hz=>⟨z,hz,rfl⟩

/-- The source's actual hyperbolic half-plane, obtained by cutting the original model with its normalized complete mirror. -/
def normalizedDirichletHalfPlane (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP :
  _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc P)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hmoved : g.val
      ξ≠ξ) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  P∩geometricContainingSide (_root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors P hP g hpres ξ
    hmoved).1 ξ

theorem normalizedDirichletHalfPlane_isOpen (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP
  : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc P)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hmoved : g.val ξ≠ξ) :
    IsOpen (normalizedDirichletHalfPlane P hP g hpres ξ hmoved):=
  hP.isOpen.inter (geometricContainingSide_isOpen _ _
    (_root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors_first_avoids P hP g hpres ξ hmoved))

/-- The actual half-plane is conjugation-covariant, for every finite, exterior or ideal center. -/
theorem normalizedDirichletHalfPlane_image (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP :
  _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc P)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hmoved : g.val ξ≠ξ) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    q.val '' normalizedDirichletHalfPlane P hP g hpres ξ hmoved=
      normalizedDirichletHalfPlane (q.val '' P) (hP.image q) (q*g*q⁻¹)
        (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_conjugate_preserves_model P g hpres q) (q.val ξ)
        (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_conjugate_moves_center g q ξ hmoved):=by
  unfold normalizedDirichletHalfPlane
  rw [image_inter q.val.injective,geometricContainingSide_image _ _
    (_root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors_first_avoids P hP g hpres ξ
      hmoved),_root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors_conjugation]

theorem freeMobiusCenter_moved {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g • ξ=ξ→g=1) (g : H) (hg :
      g≠1) :
    g.val.val ξ≠ξ:=fun he=>hg (hfree g he)

/-- The literal intersection of the true normalized half-planes in the original model. -/
def generalizedDirichletPolygon {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g •
      ξ=ξ→g=1) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  {z | z∈D.carrier ∧ ∀g : H,∀hg : g≠1,
    z∈normalizedDirichletHalfPlane D.carrier D.isDisc g.val (D.image_eq g) ξ
      (freeMobiusCenter_moved ξ hfree g hg)}

theorem generalizedDirichletPolygon_subset {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g • ξ=ξ→g=1) :
    generalizedDirichletPolygon D ξ hfree⊆D.carrier:=fun _ hz=>hz.1

theorem generalizedDirichletPolygon_mem_iff {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g • ξ=ξ→g=1) (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    z∈generalizedDirichletPolygon D ξ hfree ↔ z∈D.carrier ∧ ∀g : H,∀hg : g≠1,
      z∈geometricContainingSide (_root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors D.carrier
        D.isDisc g.val (D.image_eq g) ξ
        (freeMobiusCenter_moved ξ hfree g hg)).1 ξ := by
  constructor
  · intro hz
    exact ⟨hz.1,fun g hg=>(hz.2 g hg).2⟩
  · rintro ⟨hz,h⟩
    exact ⟨hz,fun g hg=>⟨hz,h g hg⟩⟩

/-- Conjugation preserves each original nonidentity label. -/
theorem subgroupConjugate_nonidentity (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (q
  : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (g : H) (hg : g≠1) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g≠1:=by
  intro he
  exact hg ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
    H).injective (he.trans (map_one _).symm))

theorem normalizedDirichletHalfPlane_conjugate_group
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g • ξ=ξ→g=1) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (g : H) (hg : g≠1) :
    q.val '' normalizedDirichletHalfPlane D.carrier D.isDisc g.val (D.image_eq g) ξ
      (freeMobiusCenter_moved ξ hfree g hg)=
    normalizedDirichletHalfPlane (D.nielsenConjugate q).carrier (D.nielsenConjugate q).isDisc
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g).val
      ((D.nielsenConjugate q).image_eq
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
        g)) (q.val ξ)
      (freeMobiusCenter_moved (q.val ξ) (subgroupConjugate_point_free H q ξ hfree)
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
          g) (subgroupConjugate_nonidentity H q g hg)):=
  normalizedDirichletHalfPlane_image D.carrier D.isDisc g.val (D.image_eq g) ξ
    (freeMobiusCenter_moved ξ hfree g hg) q

/-- The actual normalized-half-plane intersection has the full source conjugation law. -/
theorem generalizedDirichletPolygon_mem_conjugation
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g • ξ=ξ→g=1) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    q.val z∈generalizedDirichletPolygon (D.nielsenConjugate q) (q.val ξ)
      (subgroupConjugate_point_free H q ξ hfree) ↔ z∈generalizedDirichletPolygon D ξ hfree:=by
  constructor
  · intro hz
    have hzP : z∈D.carrier:=by
      obtain ⟨w,hw,he⟩:=hz.1
      exact q.val.injective he ▸ hw
    refine ⟨hzP,?_⟩
    intro g hg
    have hzg:=hz.2 (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      H g) (subgroupConjugate_nonidentity H q g hg)
    rw [←normalizedDirichletHalfPlane_conjugate_group D ξ hfree q g hg] at hzg
    obtain ⟨w,hw,he⟩:=hzg
    exact q.val.injective he ▸ hw
  · intro hz
    refine ⟨⟨z,hz.1,rfl⟩,?_⟩
    intro k hk
    obtain ⟨g,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      H).surjective k
    have hg : g≠1:=by intro he;apply hk;rw [he,map_one]
    rw [←normalizedDirichletHalfPlane_conjugate_group D ξ hfree q g hg]
    exact ⟨z,hz.2 g hg,rfl⟩

/-- exact whole-group and whole-model conjugation clause. -/
theorem generalizedDirichletPolygon_conjugation
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g • ξ=ξ→g=1) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    q.val '' generalizedDirichletPolygon D ξ hfree=
      generalizedDirichletPolygon (D.nielsenConjugate q) (q.val ξ)
        (subgroupConjugate_point_free H q ξ hfree):=by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (generalizedDirichletPolygon_mem_conjugation D ξ hfree q w).mpr hw
  · intro hz
    obtain ⟨w,rfl⟩:=q.val.surjective z
    exact ⟨w,(generalizedDirichletPolygon_mem_conjugation D ξ hfree q w).mp hz,rfl⟩

end
end LowDimensionalTopology.Geometry.Fuchsian
