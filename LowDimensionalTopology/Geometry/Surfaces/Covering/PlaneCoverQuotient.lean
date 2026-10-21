module
public import LowDimensionalTopology.Geometry.Surfaces.Covering.PlaneUniversalDeck
@[expose] public section
noncomputable section
open Set Filter Topology
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
/-- The genuine finite-plane domain of the actual translation group obtained from a plane cover. -/
def planeDeckMobiusDomain {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas B p) :
    MobiusInvariantDomain (planeDeckMobiusHom B p hp ha).range :=
  translationPlaneDomain _ (planeDeckMobiusRange_translations B p hp ha)

/-- The cover's original fibers are precisely the orbits of its actual Mobius translation image. -/
theorem planeDeckMobius_fiber_iff_orbit {X : Type*} [TopologicalSpace X]
    (B : RiemannAtlas X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas B p) (a b : ℂ) :
    p a = p b ↔
      translationPlaneHomeomorph _ (planeDeckMobiusRange_translations B p hp ha) a ∈
        MulAction.orbit (planeDeckMobiusHom B p hp ha).range
          (translationPlaneHomeomorph _ (planeDeckMobiusRange_translations B p hp ha) b) := by
  constructor
  · intro hab
    obtain ⟨d, hd⟩ := covering_exists_deck_map hp b a hab.symm
    refine ⟨⟨planeDeckMobiusHom B p hp ha d, ⟨d, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (planeDeckMobiusHom_apply B p hp ha d b).trans
      (congrArg ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hd)
  · rintro ⟨g, hg⟩
    obtain ⟨d, hd⟩ := g.property
    have hv := congrArg Subtype.val hg
    change g.val.val (b : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (a :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hv
    have hdb : d.val b = a := OnePoint.coe_injective
      ((planeDeckMobiusHom_apply B p hp ha d b).symm.trans
        ((congrArg (fun M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => M.val (b :
          _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) hd).trans hv))
    exact (congrArg p hdb).symm.trans (deck.proj_smul d b)

/-- The actual full Mobius quotient of the finite plane recovers the original base topology. -/
def planeDeckMobiusQuotientHomeomorph {X : Type*} [TopologicalSpace X]
    (B : RiemannAtlas X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas B p)
    (hs : Function.Surjective p) : MobiusDomainQuotient (planeDeckMobiusDomain B p hp ha) ≃ₜ X := by
  let H := (planeDeckMobiusHom B p hp ha).range
  let hT := planeDeckMobiusRange_translations B p hp ha
  let e := translationPlaneHomeomorph H hT
  let F : C(ℂ, X) := ⟨p, hp.continuous⟩
  have hF : Topology.IsQuotientMap F := hp.isQuotientMap hs
  refine (Homeomorph.Quotient.congr e.symm ?_).trans hF.homeomorph
  intro x y
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  rw [e.symm_apply_apply, e.symm_apply_apply]
  exact (planeDeckMobius_fiber_iff_orbit B p hp ha a b).symm

theorem planeDeckMobiusQuotientHomeomorph_apply_projection {X : Type*} [TopologicalSpace X]
    (B : RiemannAtlas X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas B p)
    (hs : Function.Surjective p) (z : ℂ) :
    planeDeckMobiusQuotientHomeomorph B p hp ha hs
      (mobiusDomainProjection (planeDeckMobiusDomain B p hp ha)
        (translationPlaneHomeomorph _ (planeDeckMobiusRange_translations B p hp ha) z)) = p z := by
  change p ((translationPlaneHomeomorph _ (planeDeckMobiusRange_translations B p hp ha)).symm
    (translationPlaneHomeomorph _ (planeDeckMobiusRange_translations B p hp ha) z)) = p z
  rw [Homeomorph.symm_apply_apply]

/-- The actual quotient homeomorphism is analytic for the genuine Mobius quotient atlas. -/
theorem planeDeckMobiusQuotientHomeomorph_analytic {X : Type*} [TopologicalSpace X] [T2Space X]
    (B : RiemannAtlas X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas B p)
    (hs : Function.Surjective p) :
    RiemannAnalyticMap
      (mobiusQuotientRiemannSurface (planeDeckMobiusDomain B p hp ha)
        (planeDeckMobiusRange_discontinuous B p hp ha)).toRiemannAtlas B
      (planeDeckMobiusQuotientHomeomorph B p hp ha hs) := by
  let H := (planeDeckMobiusHom B p hp ha).range
  let hT := planeDeckMobiusRange_translations B p hp ha
  let hD := planeDeckMobiusRange_discontinuous B p hp ha
  have hno : ∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g :=
    fun g hg _hne => planeDeckMobiusRange_noElliptic B p hp ha g hg
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_surjective_localHomeomorph
    (translationPlaneProjection_analytic H hT hD)
    (translationPlaneProjection_covering H hT hD hno).isLocalHomeomorph
    (translationPlaneProjection_surjective H hT) (planeDeckMobiusQuotientHomeomorph B p hp ha hs).continuous
  have he : (planeDeckMobiusQuotientHomeomorph B p hp ha hs :
      MobiusDomainQuotient (planeDeckMobiusDomain B p hp ha) → X) ∘
        translationPlaneProjection H hT = p := by
    funext z
    exact planeDeckMobiusQuotientHomeomorph_apply_projection B p hp ha hs z
  exact he.symm ▸ ha

/-- A genuine analytic covering by the whole plane represents the original base as the
actual discontinuous translation Mobius quotient, with its original branched atlas. -/
theorem riemannSurface_planeCover_conformallyEquivalent {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas R.toRiemannAtlas p)
    (hs : Function.Surjective p) :
    RiemannConformallyEquivalent R
      (mobiusQuotientRiemannSurface (planeDeckMobiusDomain R.toRiemannAtlas p hp ha)
        (by let := R.t2Space; exact planeDeckMobiusRange_discontinuous R.toRiemannAtlas p hp ha)) := by
  let := R.t2Space
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.symm
  exact ⟨planeDeckMobiusQuotientHomeomorph R.toRiemannAtlas p hp ha hs,
    planeDeckMobiusQuotientHomeomorph_analytic R.toRiemannAtlas p hp ha hs,
    (planeDeckMobiusQuotientHomeomorph R.toRiemannAtlas p hp ha hs).bijective⟩

/-- The plane alternative supplies a genuine translation-only actual Mobius subgroup,
without postulating a group representation or changing the given complex structure. -/
theorem riemannSurface_planeCover_translationQuotient {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas R.toRiemannAtlas p)
    (hs : Function.Surjective p) :
    ∃ (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hT : ∀ g ∈ H, ∃ b : ℂ, g =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b)
      (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (Set.range ((↑) : ℂ →
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))),
      (∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) ∧
        RiemannConformallyEquivalent R
          (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD) := by
  let := R.t2Space
  refine ⟨(planeDeckMobiusHom R.toRiemannAtlas p hp ha).range,
    planeDeckMobiusRange_translations R.toRiemannAtlas p hp ha,
    planeDeckMobiusRange_discontinuous R.toRiemannAtlas p hp ha, ?_,
    riemannSurface_planeCover_conformallyEquivalent R p hp ha hs⟩
  intro g hg _hne
  exact planeDeckMobiusRange_noElliptic R.toRiemannAtlas p hp ha g hg

/-- The plane alternative for an actually constructed universal cover gives the genuine
translation quotient conclusion; uniformization remains an explicit separate hypothesis. -/
theorem RiemannUniversalCover.translationQuotient_of_conformallyEquivalent_plane
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X} (C : RiemannUniversalCover R)
    (hc : @RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface complexPlaneRiemannSurface) :
    ∃ (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hT : ∀ g ∈ H, ∃ b : ℂ, g =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b)
      (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (Set.range ((↑) : ℂ →
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))),
      (∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) ∧
        RiemannConformallyEquivalent R
          (mobiusQuotientRiemannSurface (translationPlaneDomain H hT) hD) := by
  let : TopologicalSpace C.space := C.topology
  obtain ⟨f, hf, hbij⟩ := hc
  let E := hf.toHomeomorph hbij
  have hi := hf.inverse_analytic hbij
  have hp : IsCoveringMap (C.projection ∘ E.symm) := C.covering.comp_homeomorph E.symm
  have ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas R.toRiemannAtlas
      (C.projection ∘ E.symm) := C.analytic_projection.comp hi
  exact riemannSurface_planeCover_translationQuotient R (C.projection ∘ E.symm) hp ha
    (C.surjective.comp E.symm.surjective)

end LowDimensionalTopology.Geometry.Surfaces
