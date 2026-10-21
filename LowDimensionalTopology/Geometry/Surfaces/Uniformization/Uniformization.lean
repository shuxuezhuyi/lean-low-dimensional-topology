module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannManifoldEquivalences
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannStandardModels
public import LowDimensionalTopology.External.Uniformization.FunctionTheory.RiemannSphere.Basic
public import LowDimensionalTopology.External.Uniformization.RiemannDynamics.Uniformization.Trichotomy
public import LowDimensionalTopology.Geometry.Surfaces.Covering.StandardCoverClassification
public import LowDimensionalTopology.Geometry.Surfaces.Uniformization.CompactCoverModels
@[expose] public section
noncomputable section
open Set Topology
open scoped Manifold ContDiff OnePoint
namespace LowDimensionalTopology.Geometry.Surfaces

theorem sphereReciprocal_eq_nativeInv (z : OnePoint ℂ) : sphereReciprocal z = z⁻¹ := by
  induction z using OnePoint.rec with
  | infty => simp [RiemannSphere.inv_def, RiemannSphere.inv]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      exact sphereReciprocal_zero.trans RiemannSphere.inv_zero'.symm
    · rw [sphereReciprocal_coe z hz, RiemannSphere.inv_coe hz]

theorem sphereRiemannSurface_analytic_native :
    RiemannAnalyticMap sphereRiemannSurface.toRiemannAtlas
      (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold (OnePoint ℂ)).toRiemannAtlas id := by
  apply (riemannAnalyticMap_iff_locally _ _ id).mpr
  refine ⟨continuous_id, ?_⟩
  intro x
  induction x using OnePoint.rec with
  | coe z =>
    refine ⟨sphereFiniteChart, Set.mem_insert _ _, ?_,
      RiemannSphere.coeOpenPartialHomeomorph.symm, Or.inl rfl, ?_, ?_⟩
    · simp only [sphereFiniteChart_source, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact OnePoint.coe_ne_infty z
    · change (z : OnePoint ℂ) ≠ (∞ : OnePoint ℂ)
      exact OnePoint.coe_ne_infty z
    · change AnalyticAt ℂ (fun w : ℂ => RiemannSphere.coeOpenPartialHomeomorph.symm (sphereFiniteChart.symm w)) _
      change AnalyticAt ℂ id _
      exact analyticAt_id
  | infty =>
    refine ⟨sphereInfinityChart, Set.mem_insert_of_mem _ (Set.mem_singleton _), ?_,
      RiemannSphere.invCoeOpenPartialHomeomorph.symm, Or.inr rfl, ?_, ?_⟩
    · rw [sphereInfinityChart_source]
      exact OnePoint.infty_ne_coe (0 : ℂ)
    · change (∞ : OnePoint ℂ) ∈ RiemannSphere.invCoeOpenPartialHomeomorph.target
      rw [RiemannSphere.invCoeOpenPartialHomeomorph_target]
      exact RiemannSphere.inf_ne_zero
    · have he : riemannChartMap sphereInfinityChart id
          RiemannSphere.invCoeOpenPartialHomeomorph.symm = id := by
        funext w
        change ((sphereReciprocal (w : OnePoint ℂ))⁻¹).toComplex = w
        rw [sphereReciprocal_eq_nativeInv, inv_inv]
        rfl
      rw [he]
      exact analyticAt_id

theorem sphereRiemannSurface_conformallyEquivalent_native :
    RiemannConformallyEquivalent sphereRiemannSurface (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold (OnePoint ℂ)) :=
  ⟨id, sphereRiemannSurface_analytic_native, Function.bijective_id⟩

/-- Uniformization in the original surface definition, with countability proved from
its existing assumptions by Radó rather than added as a hypothesis. -/
theorem riemannSurface_uniformization {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) [SimplyConnectedSpace X] :
    RiemannConformallyEquivalent R discRiemannSurface ∨
      RiemannConformallyEquivalent R complexPlaneRiemannSurface ∨
        RiemannConformallyEquivalent R sphereRiemannSurface := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.secondCountableTopology
  rcases RiemannDynamics.uniformization_trichotomy X with h | h | h
  · have he : RiemannConformallyEquivalent (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold X)
        standardUnitDiscRiemannSurface :=
      riemannConformallyEquivalent_ofManifold_iff_nonempty_diffeomorph.mpr h
    have hs : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold X = R := R.ofManifold_toChartedSpace
    rw [hs] at he
    exact Or.inl (he.trans discRiemannSurface_conformallyEquivalent_standardUnitDisc.symm)
  · have he : RiemannConformallyEquivalent (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold X)
        (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold ℂ) :=
      riemannConformallyEquivalent_ofManifold_iff_nonempty_diffeomorph.mpr h
    have hs : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold X = R := R.ofManifold_toChartedSpace
    rw [hs] at he
    exact Or.inr (Or.inl (he.trans complexPlaneRiemannSurface_conformallyEquivalent_manifold.symm))
  · have he : RiemannConformallyEquivalent (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold X)
        (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold (OnePoint ℂ)) :=
      riemannConformallyEquivalent_ofManifold_iff_nonempty_diffeomorph.mpr h
    have hs : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold X = R := R.ofManifold_toChartedSpace
    rw [hs] at he
    exact Or.inr (Or.inr (he.trans sphereRiemannSurface_conformallyEquivalent_native.symm))

/-- The actual universal covering surface has one of the three exact conformal models. -/
theorem RiemannUniversalCover.uniformization {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (C : RiemannUniversalCover R) :
    @RiemannConformallyEquivalent C.space _ C.topology _ C.surface discRiemannSurface ∨
      @RiemannConformallyEquivalent C.space _ C.topology _ C.surface complexPlaneRiemannSurface ∨
        @RiemannConformallyEquivalent C.space _ C.topology _ C.surface sphereRiemannSurface := by
  let := C.topology
  let := C.simplyConnected
  exact riemannSurface_uniformization C.surface

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace Module

/-- Every original Riemann surface is a genuine discontinuous no-elliptic Mobius
quotient of one of the three standard simply connected domains. -/
theorem riemannSurface_standardDomain_quotient {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) :
    ∃ (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (D : MobiusInvariantDomain H)
      (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H D.carrier),
      (∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) ∧
      (D.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ∨ D.carrier = Set.range ((↑) : ℂ →
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∨
        D.carrier = Set.univ) ∧ SimplyConnectedSpace D.carrier ∧
      RiemannConformallyEquivalent R (mobiusQuotientRiemannSurface D hD) := by
  obtain ⟨C⟩ := riemannSurface_nonempty_universalCover R
  rcases C.uniformization with h | h | h
  · obtain ⟨H, hInv, hD, hno, he⟩ := C.isHyperbolicType_of_conformallyEquivalent_disc h
    exact ⟨H, unitDiscMobiusInvariantDomain H hInv, hD, hno, Or.inl rfl, discRiemannSurface_simplyConnected, he⟩
  · obtain ⟨H, hT, hD, hno, he⟩ := C.translationQuotient_of_conformallyEquivalent_plane h
    exact ⟨H, translationPlaneDomain H hT, hD, hno, Or.inr (Or.inl rfl),
      (translationPlaneHomeomorph H hT).toHomotopyEquiv.simplyConnectedSpace_iff.mp inferInstance, he⟩
  · have he := C.conformallyEquivalent_sphere_of_sphere_model h
    let H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := ⊥
    have hd : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H (sphereMobiusDomain H).carrier := by
      intro K _ _
      exact Set.toFinite _
    have hno : ∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g := by
      intro g hg hn
      exact (hn (Subgroup.mem_bot.mp hg)).elim
    have hsc : SimplyConnectedSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := by
      let := C.topology
      let := C.simplyConnected
      obtain ⟨f, hf, hbij⟩ := h
      exact (hf.toHomeomorph hbij).toHomotopyEquiv.simplyConnectedSpace_iff.mp inferInstance
    let := hsc
    exact ⟨H, sphereMobiusDomain H, hd, hno, Or.inr (Or.inr rfl),
      (sphereDomainHomeomorph H).toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance,
      he.trans (mobius_sphere_quotient_conformallyEquivalent H hd hno).symm⟩

/-- The plane and sphere alternatives give precisely the actual nonhyperbolic models;
the remaining alternative is the original genuine disc-quotient definition. -/
theorem riemannSurface_conformal_classification {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) :
    RiemannConformallyEquivalent R sphereRiemannSurface ∨
      RiemannConformallyEquivalent R complexPlaneRiemannSurface ∨
      RiemannConformallyEquivalent R puncturedPlaneRiemannSurface ∨
      (∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b,
        RiemannConformallyEquivalent R T.surface) ∨ IsHyperbolicType R := by
  obtain ⟨C⟩ := riemannSurface_nonempty_universalCover R
  rcases C.uniformization with h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (C.isHyperbolicType_of_conformallyEquivalent_disc h))))
  · rcases C.plane_model_conformal_classification h with hp | hp | hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hp))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
  · exact Or.inl (C.conformallyEquivalent_sphere_of_sphere_model h)

/-- Compact original surfaces admit exactly the three remaining kinds of genuine
conformal models. The topological-genus identification is a separate assertion. -/
theorem riemannSurface_compact_conformal_classification {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (R : RiemannSurface X) :
    RiemannConformallyEquivalent R sphereRiemannSurface ∨
      (∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b,
        RiemannConformallyEquivalent R T.surface) ∨ IsHyperbolicType R := by
  rcases riemannSurface_conformal_classification R with h | h | h | h | h
  · exact Or.inl h
  · exact (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.not_plane_of_compact R h).elim
  · exact (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.not_puncturedPlane_of_compact R
    h).elim
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The quotient representation provides an actual simply connected analytic cover
of the given surface, with the actual Mobius group as the quotient-covering action. -/
theorem riemannSurface_standardUniversalCover {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) :
    ∃ (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (D : MobiusInvariantDomain H),
      SimplyConnectedSpace D.carrier ∧
      (∀ g ∈ H, g ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) ∧
      (D.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ∨ D.carrier = Set.range ((↑) : ℂ →
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∨
        D.carrier = Set.univ) ∧
      ∃ p : D.carrier → X, IsQuotientCoveringMap p H ∧
        RiemannAnalyticMap (mobiusDomainRiemannSurface D).toRiemannAtlas R.toRiemannAtlas p := by
  obtain ⟨H, D, hd, hno, hstd, hsc, f, hf, hbij⟩ := riemannSurface_standardDomain_quotient R
  let E := hf.toHomeomorph hbij
  refine ⟨H, D, hsc, hno, hstd, E.symm ∘ mobiusDomainProjection D,
    (mobiusDomain_noElliptic_covering D hd hno).homeomorph_comp E.symm, ?_⟩
  exact (hf.inverse_analytic hbij).comp (mobiusDomainProjection_analytic D hd)

end LowDimensionalTopology.Geometry.Surfaces
