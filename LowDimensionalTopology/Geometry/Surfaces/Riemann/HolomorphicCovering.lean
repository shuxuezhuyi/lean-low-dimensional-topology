module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.AnalyticLifting

/-!
# Holomorphic coverings in the given surface structures

The projection is an actual surjective topological covering and is analytic in
both original complex atlases. The connectedness and Hausdorff conditions belong
to the two supplied Riemann surfaces. No replacement of either atlas is made.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Surfaces

/-- A holomorphic covering of the two actual Riemann surfaces. Surjectivity is
recorded explicitly, as in the usual covering-surface definition. -/
def IsRiemannCovering {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (A : RiemannSurface E) (B : RiemannSurface X) (p : E → X) : Prop :=
  Function.Surjective p ∧ IsCoveringMap p ∧
    RiemannAnalyticMap A.toRiemannAtlas B.toRiemannAtlas p

/-- Any topological deck homeomorphism of a holomorphic covering is analytic in
both directions in the original source atlas. The analytic hypothesis is imposed
on the covering projection, never on the deck homeomorphism. -/
theorem IsRiemannCovering.analytic_deck_homeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {A : RiemannSurface E} {B : RiemannSurface X} {p : E → X}
    (hp : IsRiemannCovering A B p) (g : E ≃ₜ E)
    (hg : p ∘ (g : E → E) = p) :
    RiemannAnalyticMap A.toRiemannAtlas A.toRiemannAtlas g ∧
      RiemannAnalyticMap A.toRiemannAtlas A.toRiemannAtlas g.symm := by
  have hgs : p ∘ (g.symm : E → E) = p := by
    funext x
    have hx := congrFun hg (g.symm x)
    simpa only [Function.comp_apply, g.apply_symm_apply] using hx.symm
  constructor
  · apply RiemannAnalyticMap.of_comp_localHomeomorph hp.2.2
      hp.2.1.isLocalHomeomorph g.continuous
    simpa only [hg] using hp.2.2
  · apply RiemannAnalyticMap.of_comp_localHomeomorph hp.2.2
      hp.2.1.isLocalHomeomorph g.symm.continuous
    simpa only [hgs] using hp.2.2

/-- The actual covering-transformation group therefore consists of analytic
homeomorphisms with analytic inverses, without a simply-connectedness premise. -/
theorem IsRiemannCovering.deck_analytic
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {A : RiemannSurface E} {B : RiemannSurface X} {p : E → X}
    (hp : IsRiemannCovering A B p) (g : deck p) :
    RiemannAnalyticMap A.toRiemannAtlas A.toRiemannAtlas g.val ∧
      RiemannAnalyticMap A.toRiemannAtlas A.toRiemannAtlas g.val.symm :=
  hp.analytic_deck_homeomorph g.val g.property

/-- An actual universal covering surface is a holomorphic covering in this
general definition, with its already constructed source surface and topology. -/
theorem RiemannUniversalCover.isRiemannCovering
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (C : RiemannUniversalCover R) :
    @IsRiemannCovering C.space X C.topology _ C.surface R C.projection :=
  ⟨C.surjective, C.covering, C.analytic_projection⟩

end LowDimensionalTopology.Geometry.Surfaces
