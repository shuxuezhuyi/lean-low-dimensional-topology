module
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.FiniteIndexConjugacy
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSelfPairedSides
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletCenters
/-!
# Finitely many elliptic classes from finitely many sides

A finite-sided polygon has finitely many vertices and elliptic centers,
including order-two centers inside self-paired sides. These centers meet every
elliptic orbit and hence give finitely many maximal elliptic cyclic classes.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Pointwise OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance finiteEllipseSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance finiteEllipseSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Finitely many literal genuine sides force finitely many actual finite vertices. -/
theorem finite_sided_polygon_vertices_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hFin : Finite (FuchsianPolygonSides P D)) :
    {x | IsFuchsianPolygonVertex P D x}.Finite := by
  classical
  have : Finite (FuchsianPolygonSides P D) := hFin
  let F (s t : FuchsianPolygonSides P D) : Set P.domain.carrier :=
    {x | s ≠ t ∧ x ∈ s.val ∩ t.val}
  have hF (s t : FuchsianPolygonSides P D) : (F s t).Finite := by
    by_cases hst : s = t
    · simp [F,hst]
    · apply (hD.distinct_sides_inter_subsingleton s.property t.property
        (fun he => hst (Subtype.ext he))).finite.subset
      exact fun x hx => hx.2
  apply (Set.finite_iUnion (fun s => Set.finite_iUnion (hF s))).subset
  intro x hx
  obtain ⟨S,T,hS,hT,hST,hxS,hxT⟩ := hD.vertex_exists_two_sides hx
  refine mem_iUnion.mpr ⟨⟨S,hS⟩,mem_iUnion.mpr ⟨⟨T,hT⟩,?_,hxS,hxT⟩⟩
  exact fun he => hST (congrArg Subtype.val he)

/-- A genuine fixed point in the polygon closure belongs to its actual frontier. -/
theorem polygon_fixed_point_mem_frontier {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (x : P.domain.carrier) (hx : x ∈ closure D)
    (g : H) (hg : g ≠ 1) (hfix : g • x = x) : x ∈ frontier D := by
  refine ⟨hx,?_⟩
  rw [hD.isOpen.interior_eq]
  intro hxin
  exact Set.disjoint_left.mp (hD.disjoint_image hg) ⟨x,hxin,hfix⟩ hxin

/-- All actual elliptic centers in a finite-sided polygon closure form a genuine finite set,
including the order-two centers inside self-paired sides. -/
theorem finite_sided_polygon_elliptic_centers_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hFin : Finite (FuchsianPolygonSides P D)) :
    (closure D ∩ fuchsianEllipticPoints P).Finite := by
  classical
  have : Finite (FuchsianPolygonSides P D) := hFin
  let F (s : FuchsianPolygonSides P D) : Set P.domain.carrier :=
    {x | fuchsianSideElement hD s • x = x}
  have hF (s : FuchsianPolygonSides P D) : (F s).Finite := by
    have hg : (fuchsianSideElement hD s).val ≠ 1 :=
      fun he => (fuchsianSideElement_spec hD s).1 (Subtype.ext he)
    apply ((mobius_boundary_fixed_finite (fuchsianSideElement hD s).val hg).preimage
      Subtype.val_injective.injOn).subset
    intro x hx
    exact congrArg Subtype.val hx
  apply ((finite_sided_polygon_vertices_finite hD hFin).union
    (Set.finite_iUnion hF)).subset
  rintro x ⟨hx,hell⟩
  change ¬(∀ g : H, g • x = x → g = 1) at hell
  push Not at hell
  obtain ⟨g,hfix,hg⟩ := hell
  have hxfront := polygon_fixed_point_mem_frontier hD.locallyFinite.fundamental x hx g hg hfix
  by_cases hv : IsFuchsianPolygonVertex P D x
  · exact Or.inl hv
  · obtain ⟨S,hS,hxS⟩ := hD.boundary_mem_side hxfront
    let s : FuchsianPolygonSides P D := ⟨S,hS⟩
    have hi := hD.nonvertex_is_side_interior hxfront hv
    have he := hD.side_interior_fixing_eq_pairing s hxS hi g hg hfix
    apply Or.inr
    apply mem_iUnion.mpr
    refine ⟨s,?_⟩
    change fuchsianSideElement hD s • x = x
    exact he ▸ hfix

/-- A true finite set meeting every actual orbit gives a finite actual orbit quotient. -/
theorem finite_orbitQuotient_of_finite_representatives {G X : Type*} [Group G] [MulAction G X]
    (S : Set X) (hS : S.Finite) (hrep : ∀ x : X, ∃ g : G, g • x ∈ S) :
    Finite (MulAction.orbitRel.Quotient G X) := by
  have : Finite S := hS.to_subtype
  apply Finite.of_surjective (fun s : S => (Quotient.mk'' s.val : MulAction.orbitRel.Quotient G X))
  intro q
  induction q using Quotient.inductionOn' with
  | h x =>
    obtain ⟨g,hgx⟩ := hrep x
    refine ⟨⟨g • x,hgx⟩,Quotient.sound ?_⟩
    exact MulAction.mem_orbit_iff.mpr ⟨g,rfl⟩

/-- Genuine finite-sided polygons have only finitely many actual maximal elliptic cyclic
subgroup conjugacy classes, with order-two side-center classes retained. -/
theorem finite_sided_polygon_elliptic_classes_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hFin : Finite (FuchsianPolygonSides P D)) :
    Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic) := by
  let X := fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic
  let ι : X → P.domain.carrier := fun p => ⟨p.val,p.property.1 rfl⟩
  have hi : Function.Injective ι := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : P.domain.carrier => z.val) h
  let S : Set X := ι ⁻¹' closure D
  have hS : S.Finite := by
    apply ((finite_sided_polygon_elliptic_centers_finite hD hFin).preimage hi.injOn).subset
    intro p hp
    refine ⟨hp,?_⟩
    change ¬(∀ g : H, g • ι p = ι p → g = 1)
    intro hc
    obtain ⟨f,hfH,hf,hfix⟩ := p.property.2
    let g : H := ⟨f,hfH⟩
    have hg : g • ι p = ι p := Subtype.ext hfix
    have he := hc g hg
    exact hf.1 (congrArg Subtype.val he)
  have hrep (p : X) : ∃ g : H, g • p ∈ S := by
    have hp : ι p ∈ (⋃ g : H,(fun x : P.domain.carrier => g • x) '' closure D) := by
      rw [hD.locallyFinite.fundamental.closure_cover]
      trivial
    obtain ⟨g,y,hy,hey⟩ := mem_iUnion.mp hp
    refine ⟨g⁻¹,?_⟩
    change ι (g⁻¹ • p) ∈ closure D
    have hι : ι (g⁻¹ • p) = g⁻¹ • ι p := rfl
    rw [hι,←hey,inv_smul_smul]
    exact hy
  have : Finite (MulAction.orbitRel.Quotient H X) :=
    finite_orbitQuotient_of_finite_representatives S hS hrep
  exact Finite.of_equiv _ (fuchsianCyclicConjugacyClassesEquiv P.asFuchsianDisc .elliptic).symm

end LowDimensionalTopology.Geometry.Fuchsian
