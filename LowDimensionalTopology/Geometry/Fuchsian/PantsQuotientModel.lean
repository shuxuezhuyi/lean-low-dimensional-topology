module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSignature
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.QuotientMetric

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- The empty list enumerating the genuine elliptic classes excludes elliptic
elements of this same group. -/
theorem noElliptic_of_threeBoundarySignature
    {H : Subgroup Mobius.complexMobiusGroup}
    {G : UnitDiscFuchsianGroup H}
    {hNE : DiscreteGroups.IsNonElementary H} {hFG : H.FG}
    (h : HasNielsenFuchsianSignature G hNE hFG 0 [] 0 3) :
    ∀ f ∈ H, f ≠ 1 → ¬ Mobius.MobiusElliptic f := by
  obtain ⟨w, hw, _hwN, _J, _hc, _hv, _n, _S, _hr, _hg, ho, _hp, _ht⟩ := h
  let : Finite (FuchsianCyclicConjugacyClasses G.asFuchsianDisc .elliptic) :=
    finite_sided_polygon_elliptic_classes_finite
      (dirichletDomain_isConvexFuchsianPolygon G w hw)
      (finitelyGenerated_dirichlet_sides_finite G hNE hFG w hw)
  have hnil : fuchsianEllipticOrderList G.asFuchsianDisc = [] :=
    List.eq_nil_of_length_eq_zero (by rw [← ho.length_eq]; rfl)
  intro f hf _hne
  exact (fuchsianEllipticOrderList_eq_nil_iff G.asFuchsianDisc).mp hnil f hf

/-- The actual quotient Riemann surface of the original unit-disc group. -/
def threeBoundaryQuotientRiemannSurface
    {H : Subgroup Mobius.complexMobiusGroup} (G : UnitDiscFuchsianGroup H) :
    Surfaces.RiemannSurface (Surfaces.MobiusDomainQuotient G.domain) :=
  Surfaces.mobiusQuotientRiemannSurface G.domain G.discontinuous

/-- The original group and identity presentation give a hyperbolic model on
its own quotient, once its nonidentity elliptics have been excluded. -/
def threeBoundaryQuotientModel
    {H : Subgroup Mobius.complexMobiusGroup} (G : UnitDiscFuchsianGroup H)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬ Mobius.MobiusElliptic f) :
    Surfaces.HyperbolicSurfaceModel (threeBoundaryQuotientRiemannSurface G) where
  group := H
  invariant := G.invariant
  discontinuous := G.discontinuous
  no_elliptic := hno
  homeomorph := Homeomorph.refl _
  analytic := Surfaces.RiemannAnalyticMap.id _

end LowDimensionalTopology.Geometry.Fuchsian
