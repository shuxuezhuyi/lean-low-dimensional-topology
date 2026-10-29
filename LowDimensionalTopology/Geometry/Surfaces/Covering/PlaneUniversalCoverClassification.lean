module

public import LowDimensionalTopology.Geometry.Surfaces.Covering.StandardCoverClassification
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.AnalyticLifting
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CompactGenusTypes
public import Mathlib.Analysis.Complex.CoveringMap

/-!
# The plane universal-cover alternative and the three genuine base models

The converse uses actual analytic plane covers of the plane, punctured plane
and every period-lattice torus. Comparing their sources uses unbundled covering
uniqueness across independent universes, so the plane is never silently treated
as a carrier in the universe of an arbitrary original surface.
-/

@[expose] public section
noncomputable section

open Set Module

namespace LowDimensionalTopology.Geometry.Surfaces

universe u v w

/-- Two genuine simply connected analytic covers of the same original surface
have conformally equivalent sources, even in different universes. -/
theorem riemannSurface_conformallyEquivalent_of_simplyConnected_covers
    {E : Type u} {F : Type v} {X : Type w}
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F]
    (A : RiemannSurface E) (B : RiemannSurface F) (R : RiemannSurface X)
    (p : E → X) (q : F → X) (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (hap : RiemannAnalyticMap A.toRiemannAtlas R.toRiemannAtlas p)
    (haq : RiemannAnalyticMap B.toRiemannAtlas R.toRiemannAtlas q)
    (hsq : Function.Surjective q) : RiemannConformallyEquivalent A B := by
  let e₀ : E := Classical.choice inferInstance
  obtain ⟨f₀, h₀⟩ := hsq (p e₀)
  obtain ⟨U, ⟨hU₀, hUq, hUa⟩, _⟩ :=
    RiemannAnalyticMap.existsUnique_continuous_lift A.toRiemannAtlas
      B.toRiemannAtlas R.toRiemannAtlas hq haq ⟨p, hp.continuous⟩ e₀ f₀ h₀
  obtain ⟨V, ⟨hV₀, hVp, _hVa⟩, _⟩ :=
    RiemannAnalyticMap.existsUnique_continuous_lift B.toRiemannAtlas
      A.toRiemannAtlas R.toRiemannAtlas hp hap ⟨q, hq.continuous⟩ f₀ e₀ h₀.symm
  have hVU : (V ∘ U : E → E) = id :=
    hp.eq_of_comp_eq (V.continuous.comp U.continuous) continuous_id
      (by funext e; exact (congrFun hVp (U e)).trans (congrFun hUq e))
      e₀ (by simp only [Function.comp_apply, hU₀, hV₀, id_eq])
  have hUV : (U ∘ V : F → F) = id :=
    hq.eq_of_comp_eq (U.continuous.comp V.continuous) continuous_id
      (by funext f; exact (congrFun hUq (V f)).trans (congrFun hVp f))
      f₀ (by simp only [Function.comp_apply, hV₀, hU₀, id_eq])
  let e : E ≃ₜ F :=
    { toFun := U
      invFun := V
      left_inv := fun x => congrFun hVU x
      right_inv := fun y => congrFun hUV y
      continuous_toFun := U.continuous
      continuous_invFun := V.continuous }
  exact ⟨e, hUa.mpr hap, e.bijective⟩

/-- The literal exponential gives an actual analytic plane cover of the
punctured plane in its original complex chart. -/
theorem puncturedPlane_exists_analytic_planeCover :
    ∃ p : ℂ → {z : ℂ // z ≠ 0}, IsCoveringMap p ∧ Function.Surjective p ∧
      RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas
        puncturedPlaneRiemannSurface.toRiemannAtlas p := by
  refine ⟨fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩,
    Complex.isCoveringMap_exp, Complex.isAddQuotientCoveringMap_exp.surjective, ?_⟩
  apply (RiemannAnalyticMap.globalChart_iff (OpenPartialHomeomorph.refl ℂ) rfl
    puncturedPlaneChart puncturedPlaneChart_source _).mpr
  refine ⟨Complex.isCoveringMap_exp.continuous, ?_⟩
  change AnalyticOnNhd ℂ Complex.exp _
  intro z _hz
  exact analyticAt_id.cexp

/-- Any actual analytic surjective plane covering identifies the source of the
original universal cover conformally with the complex plane. -/
theorem RiemannUniversalCover.plane_model_of_analytic_planeCover
    {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (C : RiemannUniversalCover R) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas R.toRiemannAtlas p)
    (hs : Function.Surjective p) :
    @RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface
      complexPlaneRiemannSurface := by
  let := C.topology
  let := C.simplyConnected
  exact riemannSurface_conformallyEquivalent_of_simplyConnected_covers
    C.surface complexPlaneRiemannSurface R C.projection p C.covering hp
    C.analytic_projection ha hs

/-- Transport an actual analytic plane covering through an actual biholomorphism
of the base, preserving the original universal cover and original atlases. -/
theorem RiemannUniversalCover.plane_model_of_conformallyEquivalent_planeCover
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} (C : RiemannUniversalCover R) (S : RiemannSurface Y)
    (hRS : RiemannConformallyEquivalent R S)
    (p : ℂ → Y) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas S.toRiemannAtlas p)
    (hs : Function.Surjective p) :
    @RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface
      complexPlaneRiemannSurface := by
  obtain ⟨f, hf, hbij⟩ := hRS
  let e := hf.toHomeomorph hbij
  exact C.plane_model_of_analytic_planeCover (e.symm ∘ p)
    (hp.homeomorph_comp e.symm) ((hf.inverse_analytic hbij).comp ha)
    (e.symm.surjective.comp hs)

/-- The actual universal cover is the plane exactly for the plane, punctured
plane and genuine period-lattice torus conformal types. -/
theorem RiemannUniversalCover.plane_model_iff_standard_quotients
    {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (C : RiemannUniversalCover R) :
    (@RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface
      complexPlaneRiemannSurface) ↔
      RiemannConformallyEquivalent R complexPlaneRiemannSurface ∨
        RiemannConformallyEquivalent R puncturedPlaneRiemannSurface ∨
          ∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b,
            RiemannConformallyEquivalent R T.surface := by
  constructor
  · exact C.plane_model_conformal_classification
  · rintro (h | h | ⟨_b, T, h⟩)
    · obtain ⟨f, hf, hbij⟩ := h
      let e := hf.toHomeomorph hbij
      have hp : IsCoveringMap (e.symm : ℂ → X) := by
        apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
        exact e.symm.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
          (fun x _hx => (Set.finite_singleton x).preimage e.symm.injective.injOn)
          e.symm.isLocalHomeomorph.isLocalHomeomorphOn
      exact C.plane_model_of_analytic_planeCover e.symm hp (hf.inverse_analytic hbij)
        e.symm.surjective
    · obtain ⟨p, hp, hs, ha⟩ := puncturedPlane_exists_analytic_planeCover
      exact C.plane_model_of_conformallyEquivalent_planeCover puncturedPlaneRiemannSurface
        h p hp ha hs
    · exact C.plane_model_of_conformallyEquivalent_planeCover T.surface h T.projection
        T.covering T.analytic_projection T.surjective

/-- The torus alternative includes every original complex structure on a
surface with actual two-torus topology, not just a preselected flat model. -/
theorem RiemannUniversalCover.plane_model_iff_plane_puncturedPlane_or_torus
    {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (C : RiemannUniversalCover R) :
    (@RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface
      complexPlaneRiemannSurface) ↔
      RiemannConformallyEquivalent R complexPlaneRiemannSurface ∨
        RiemannConformallyEquivalent R puncturedPlaneRiemannSurface ∨
          Nonempty (X ≃ₜ ComplexTorusCarrier) := by
  constructor
  · intro h
    rcases C.plane_model_iff_standard_quotients.mp h with hp | hp | ⟨_b, _T, f, hf, hbij⟩
    · exact Or.inl hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr ⟨hf.toHomeomorph hbij⟩)
  · rintro (hp | hp | he)
    · exact C.plane_model_iff_standard_quotients.mpr (Or.inl hp)
    · exact C.plane_model_iff_standard_quotients.mpr (Or.inr (Or.inl hp))
    · obtain ⟨e⟩ := he
      exact C.plane_model_of_homeomorphic_torus e

end LowDimensionalTopology.Geometry.Surfaces
