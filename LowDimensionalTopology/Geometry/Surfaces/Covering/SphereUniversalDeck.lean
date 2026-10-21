module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Surfaces.Covering.PlaneUniversalDeck
@[expose] public section
noncomputable section
open Set Filter Topology
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces

/-- A sphere homeomorphism fixing infinity has a whole-plane finite coordinate. -/
theorem sphereFiniteHomeomorphChart_source (H : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ≃ₜ
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hH : H ∞ = ∞) :
    (riemannHomeomorphChart sphereFiniteChart H sphereFiniteChart).source = Set.univ := by
  rw [riemannHomeomorphChart_source]
  ext z
  simp only [riemannChartMapDomain, sphereFiniteChart_target, Set.mem_inter_iff, Set.mem_univ,
    true_and, Set.mem_preimage, sphereFiniteChart_symm, sphereFiniteChart_source,
    Set.mem_compl_iff, Set.mem_singleton_iff, iff_true]
  intro he
  exact OnePoint.coe_ne_infty z (H.injective (he.trans hH.symm))

theorem sphereFiniteHomeomorphChart_target (H : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ≃ₜ
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hH : H ∞ = ∞) :
    (riemannHomeomorphChart sphereFiniteChart H sphereFiniteChart).target = Set.univ := by
  rw [riemannHomeomorphChart_target]
  rw [← riemannHomeomorphChart_source sphereFiniteChart H.symm sphereFiniteChart]
  exact sphereFiniteHomeomorphChart_source H.symm (by
    apply H.injective
    rw [H.apply_symm_apply, hH])

/-- An analytic sphere homeomorphism fixing infinity has a genuine actual Mobius extension,
by the proved entire-plane affine theorem. -/
theorem sphere_analytic_fix_infty_exists_mobius (H : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ≃ₜ
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (ha : RiemannAnalyticMap sphereRiemannAtlas sphereRiemannAtlas H) (hH : H ∞ = ∞) :
    ∃ M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, ∀ z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, M.val z = H z := by
  let F := riemannHomeomorphChart sphereFiniteChart H sphereFiniteChart
  have hs : F.source = Set.univ := sphereFiniteHomeomorphChart_source H hH
  have ht : F.target = Set.univ := sphereFiniteHomeomorphChart_target H hH
  let e := F.toHomeomorphOfSourceEqUnivTargetEqUniv hs ht
  have hae : AnalyticOnNhd ℂ e Set.univ := by
    intro z _hz
    have hzs : z ∈ F.source := hs.symm ▸ Set.mem_univ z
    rw [riemannHomeomorphChart_source] at hzs
    exact ha.2 sphereFiniteChart (Set.mem_insert _ _) sphereFiniteChart (Set.mem_insert _ _) z hzs
  obtain ⟨M, ⟨hMinfty, hMe⟩, _hMu⟩ := plane_analytic_automorphism_existsUnique_mobius e hae
  refine ⟨M, ?_⟩
  intro z
  induction z using OnePoint.rec with
  | infty => exact hMinfty.trans hH.symm
  | coe z =>
    have hHz : H (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ sphereFiniteChart.source := by
      rw [sphereFiniteChart_source]
      intro he
      exact OnePoint.coe_ne_infty z (H.injective (he.trans hH.symm))
    have hcoord := sphereFiniteChart.left_inv hHz
    change ((sphereFiniteChart (H (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = H (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hcoord
    exact (hMe z).trans hcoord

/-- Every genuinely analytic sphere automorphism is uniquely an actual Mobius transformation. -/
theorem sphere_analytic_automorphism_existsUnique_mobius (H :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ≃ₜ
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (ha : RiemannAnalyticMap sphereRiemannAtlas sphereRiemannAtlas H) :
    ∃! M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, ∀ z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, M.val z = H z := by
  obtain ⟨N, hN⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_exists_send_to_infty (H ∞)
  let K := H.trans (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph N)
  have hK : K ∞ = ∞ := hN
  have hKa : RiemannAnalyticMap sphereRiemannAtlas sphereRiemannAtlas K :=
    (mobius_riemannSphere_analytic N).comp ha
  obtain ⟨M, hM⟩ := sphere_analytic_fix_infty_exists_mobius K hKa hK
  let A := N⁻¹ * M
  have hA (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : A.val z = H z := by
    change N.val.symm (M.val z) = H z
    rw [hM z]
    exact N.val.symm_apply_apply (H z)
  refine ⟨A, hA, ?_⟩
  intro B hB
  exact mobius_eq_of_agree_plane B A (fun z => (hB z).trans (hA z).symm)

/-- The unique actual Mobius transformation of a genuine analytic sphere automorphism. -/
def sphereAnalyticAutomorphismMobius (H : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ≃ₜ
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (ha : RiemannAnalyticMap sphereRiemannAtlas sphereRiemannAtlas
      H) : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  (sphere_analytic_automorphism_existsUnique_mobius H ha).choose

theorem sphereAnalyticAutomorphismMobius_apply (H : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ≃ₜ
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (ha : RiemannAnalyticMap sphereRiemannAtlas sphereRiemannAtlas H) (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    (sphereAnalyticAutomorphismMobius H ha).val z = H z :=
  (sphere_analytic_automorphism_existsUnique_mobius H ha).choose_spec.1 z

/-- An analytic action on the sphere is represented by genuine actual Mobius transformations. -/
def sphereAnalyticActionMobiusHom {G : Type*} [Group G]
    (ρ : G →* (_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ≃ₜ
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (ha : ∀ g, RiemannAnalyticMap sphereRiemannAtlas sphereRiemannAtlas (ρ g)) :
    G →* _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup where
  toFun g := sphereAnalyticAutomorphismMobius (ρ g) (ha g)
  map_one' := by
    apply mobius_eq_of_agree_plane
    intro z
    rw [sphereAnalyticAutomorphismMobius_apply, map_one]
    rfl
  map_mul' g h := by
    apply mobius_eq_of_agree_plane
    intro z
    rw [sphereAnalyticAutomorphismMobius_apply, map_mul]
    change (ρ g) ((ρ h) (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) =
      (sphereAnalyticAutomorphismMobius (ρ g) (ha g)).val
        ((sphereAnalyticAutomorphismMobius (ρ h) (ha h)).val (z :
          _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    rw [sphereAnalyticAutomorphismMobius_apply, sphereAnalyticAutomorphismMobius_apply]

theorem sphereAnalyticActionMobiusHom_injective {G : Type*} [Group G]
    (ρ : G →* (_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex ≃ₜ
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (ha : ∀ g, RiemannAnalyticMap sphereRiemannAtlas sphereRiemannAtlas (ρ g))
    (hρ : Function.Injective ρ) : Function.Injective (sphereAnalyticActionMobiusHom ρ ha) := by
  intro g h he
  apply hρ
  apply Homeomorph.ext
  intro z
  have hv := congrArg (fun M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => M.val z) he
  change (sphereAnalyticAutomorphismMobius (ρ g) (ha g)).val z =
    (sphereAnalyticAutomorphismMobius (ρ h) (ha h)).val z at hv
  simpa only [sphereAnalyticAutomorphismMobius_apply] using hv

/-- The actual Mobius representation of the analytic sphere-covering deck group. -/
def sphereDeckMobiusHom {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap sphereRiemannAtlas B
      p) : deck p →* _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  sphereAnalyticActionMobiusHom (deck p).subtype (covering_deck_analytic_of_analytic hp ha)

theorem sphereDeckMobiusHom_injective {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap sphereRiemannAtlas B p) : Function.Injective (sphereDeckMobiusHom B p hp ha) :=
  sphereAnalyticActionMobiusHom_injective _ _ Subtype.val_injective

theorem sphereDeckMobiusHom_apply {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap sphereRiemannAtlas B p) (g : deck p) (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    (sphereDeckMobiusHom B p hp ha g).val z = g • z :=
  sphereAnalyticAutomorphismMobius_apply g.val (covering_deck_analytic_of_analytic hp ha g) z

/-- Every actual deck transformation of an analytic sphere covering is identity, because
all nonidentity actual Mobius maps have a genuine boundary fixed point. -/
theorem sphereCover_deck_eq_one {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap sphereRiemannAtlas B p) (g : deck p) : g = 1 := by
  let : ConnectedSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := sphereRiemannSurface.connectedSpace
  by_cases he : sphereDeckMobiusHom B p hp ha g = 1
  · apply sphereDeckMobiusHom_injective B p hp ha
    rw [he, map_one]
  · obtain ⟨z, hz⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_has_boundary_fixed _ he
    apply _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.covering_deck_fixedPoint_eq_one hp g z
    exact (sphereDeckMobiusHom_apply B p hp ha g z).symm.trans hz

/-- The actual Mobius image of the sphere deck group is the literal trivial subgroup. -/
theorem sphereDeckMobiusRange_eq_bot {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap sphereRiemannAtlas B p) : (sphereDeckMobiusHom B p hp ha).range = ⊥ := by
  apply le_antisymm _ bot_le
  rintro f ⟨g, rfl⟩
  change sphereDeckMobiusHom B p hp ha g = 1
  rw [sphereCover_deck_eq_one B p hp ha g, map_one]

/-- For a simply connected actual sphere cover, deck triviality makes the original
surjective analytic covering a conformal bijection. -/
theorem riemannSurface_sphereCover_conformallyEquivalent {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex]
    (R : RiemannSurface X) (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex → X) (hp : IsCoveringMap
      p)
    (ha : RiemannAnalyticMap sphereRiemannAtlas R.toRiemannAtlas p) (hs : Function.Surjective p) :
    RiemannConformallyEquivalent R sphereRiemannSurface := by
  let : LocallyPathConnectedSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := sphereRiemannAtlas.locallyPathConnectedSpace
  have hinj : Function.Injective p := by
    intro a b hab
    obtain ⟨g, hg⟩ := covering_exists_deck_map hp a b hab
    have hg1 := sphereCover_deck_eq_one R.toRiemannAtlas p hp ha g
    rw [hg1, one_smul] at hg
    exact hg
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.symm ⟨p, ha, hinj, hs⟩

/-- The genuine sphere alternative for a constructed universal cover implies that the
original Riemann surface is conformally the sphere; no uniformization assertion is inserted. -/
theorem RiemannUniversalCover.conformallyEquivalent_sphere_of_sphere_model
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X} (C : RiemannUniversalCover R)
    (hc : @RiemannConformallyEquivalent C.space _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex C.topology
      _ C.surface sphereRiemannSurface) :
    RiemannConformallyEquivalent R sphereRiemannSurface := by
  let : TopologicalSpace C.space := C.topology
  let : SimplyConnectedSpace C.space := C.simplyConnected
  obtain ⟨f, hf, hbij⟩ := hc
  let E := hf.toHomeomorph hbij
  let : SimplyConnectedSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := E.toHomotopyEquiv.simplyConnectedSpace_iff.mp inferInstance
  have hi := hf.inverse_analytic hbij
  have hp : IsCoveringMap (C.projection ∘ E.symm) := C.covering.comp_homeomorph E.symm
  have ha : RiemannAnalyticMap sphereRiemannAtlas R.toRiemannAtlas
      (C.projection ∘ E.symm) := C.analytic_projection.comp hi
  exact riemannSurface_sphereCover_conformallyEquivalent R (C.projection ∘ E.symm) hp ha
    (C.surjective.comp E.symm.surjective)

end LowDimensionalTopology.Geometry.Surfaces
