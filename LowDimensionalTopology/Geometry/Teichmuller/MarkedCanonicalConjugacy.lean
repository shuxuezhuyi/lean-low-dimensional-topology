module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedPolygonMonodromy
public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalPairNormalizationRigidity
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticRotationAngles

/-!
# Given normalized canonical systems on actual marked targets

An anchored lift of the actual change of marking intertwines the endpoint
deck maps of every prescribed polygon side. Biholomorphic marked equivalence,
including its actual free marking homotopy, then produces one real Möbius
conjugator for all of those maps. Dynamic normalization forces that derived
conjugator to be the identity projective map.

The systems are given with their dynamically labelled normalization; the
conclusion retains each ordered projective generator on the actual targets.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation Hyperbolic Mobius

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}

/-- The actual anchored marking lift intertwines the actual endpoint deck
maps of the same prescribed polygon loops on the two native targets. -/
theorem MarkedRiemannSurface.markedPolygonEndpointDeck_intertwines_lift
    (m n : MarkedRiemannSurface.{0, 0} R)
    (M : HyperbolicSurfaceModel m.surface.toRiemannSurface)
    (N : HyperbolicSurfaceModel n.surface.toRiemannSurface)
    (e : X ≃ₜ PolygonQuotient g) (a b : ℍ)
    (ha : M.halfPlaneCover a = (m.marking.toHomeomorph.symm.trans e).symm (boundaryBase g).val)
    (hb : N.halfPlaneCover b = (n.marking.toHomeomorph.symm.trans e).symm (boundaryBase g).val)
    (F : ℍ ≃ₜ ℍ)
    (hF : LiZhongQC.IsLift M.halfPlaneCover N.halfPlaneCover
      (m.marking.toHomeomorph.symm.trans n.marking.toHomeomorph) F)
    (hFab : F a = b) (d : Edge g) (z : ℍ) :
    N.markedPolygonEndpointDeck (n.marking.toHomeomorph.symm.trans e) b hb d • F z =
      F (M.markedPolygonEndpointDeck (m.marking.toHomeomorph.symm.trans e) a ha d • z) := by
  let f := m.marking.toHomeomorph.symm.trans n.marking.toHomeomorph
  let em := m.marking.toHomeomorph.symm.trans e
  let en := n.marking.toHomeomorph.symm.trans e
  let α := M.markedPolygonLoopLift em a ha d
  let β := N.markedPolygonLoopLift en b hb d
  let Dm := M.markedPolygonEndpointDeck em a ha d
  let Dn := N.markedPolygonEndpointDeck en b hb d
  have hα := M.markedPolygonLoopLift_spec em a ha d
  have hβ := N.markedPolygonLoopLift_spec en b hb d
  have hloop (t : unitInterval) : markedPolygonLoop en d t = f (markedPolygonLoop em d t) := by
    change n.marking.toHomeomorph (e.symm (positivePolygonLoop d t)) =
      n.marking.toHomeomorph (m.marking.toHomeomorph.symm
        (m.marking.toHomeomorph (e.symm (positivePolygonLoop d t))))
    rw [m.marking.toHomeomorph.symm_apply_apply]
  have hpaths : (F : ℍ → ℍ) ∘ α = (β : unitInterval → ℍ) := by
    apply N.halfPlaneCover_covering.eq_of_comp_eq
      (F.continuous.comp α.continuous) β.continuous ?_ (0 : unitInterval) ?_
    · funext t
      change N.halfPlaneCover (F (α t)) = N.halfPlaneCover (β t)
      have hαt : M.halfPlaneCover (α t) = markedPolygonLoop em d t :=
        congrFun hα.1 t
      have hβt : N.halfPlaneCover (β t) = markedPolygonLoop en d t :=
        congrFun hβ.1 t
      rw [hF (α t), hαt, hβt]
      exact (hloop t).symm
    · change F (α 0) = β 0
      rw [hα.2.1, hβ.2.1, hFab]
  have hpoint : Dn • b = F (Dm • a) := by
    have h := congrFun hpaths (1 : unitInterval)
    change F (α 1) = β 1 at h
    rw [hα.2.2, hβ.2.2] at h
    exact h.symm
  have hwhole : (fun y : ℍ => Dn • F y) = (fun y : ℍ => F (Dm • y)) := by
    apply N.halfPlaneCover_covering.eq_of_comp_eq
      ((continuous_const_smul Dn).comp F.continuous)
      (F.continuous.comp (continuous_const_smul Dm)) ?_ a ?_
    · funext y
      change N.halfPlaneCover (Dn • F y) = N.halfPlaneCover (F (Dm • y))
      rw [deck.proj_smul Dn (F y), hF (Dm • y), deck.proj_smul Dm y, hF y]
    · change Dn • F a = F (Dm • a)
      rw [hFab]
      exact hpoint
  exact congrFun hwhole z

/-- Biholomorphic target equivalence and the actual free marking homotopy
produce one real conjugator for every prescribed canonical endpoint deck map. -/
theorem MarkedRiemannSurface.exists_markedPolygonEndpointDeck_conjugator
    (m n : MarkedRiemannSurface.{0, 0} R)
    (M : HyperbolicSurfaceModel m.surface.toRiemannSurface)
    (N : HyperbolicSurfaceModel n.surface.toRiemannSurface)
    (e : X ≃ₜ PolygonQuotient g) (a b : ℍ)
    (ha : M.halfPlaneCover a = (m.marking.toHomeomorph.symm.trans e).symm (boundaryBase g).val)
    (hb : N.halfPlaneCover b = (n.marking.toHomeomorph.symm.trans e).symm (boundaryBase g).val)
    (hmn : MarkedRiemannSurface.Equivalent m n) :
    ∃ Q : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ (d : Edge g) (z : ℍ),
      Q • (M.markedPolygonEndpointDeck (m.marking.toHomeomorph.symm.trans e) a ha d • z) =
        N.markedPolygonEndpointDeck (n.marking.toHomeomorph.symm.trans e) b hb d • (Q • z) := by
  let := m.surface.toRiemannAtlas.toChartedSpace
  let := n.surface.toRiemannAtlas.toChartedSpace
  let := m.surface.toRiemannAtlas.isManifold
  let := n.surface.toRiemannAtlas.isManifold
  let := m.surface.t2Space
  let := n.surface.t2Space
  let := m.surface.connectedSpace
  let := n.surface.connectedSpace
  let f := m.marking.toHomeomorph.symm.trans n.marking.toHomeomorph
  obtain ⟨Γm, _hΓm, hpM⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨Γn, _hΓn, hpN⟩ := N.exists_halfPlaneCover_uniformization
  have hab : N.halfPlaneCover b = f (M.halfPlaneCover a) := by
    rw [ha, hb]
    change n.marking.toHomeomorph (e.symm (boundaryBase g).val) =
      n.marking.toHomeomorph (m.marking.toHomeomorph.symm
        (m.marking.toHomeomorph (e.symm (boundaryBase g).val)))
    rw [m.marking.toHomeomorph.symm_apply_apply]
  obtain ⟨F, hF, hFab⟩ := LiZhongQC.exists_lift hpM hpN f a b hab
  obtain ⟨h, hh, hhom⟩ := hmn
  obtain ⟨c, hc⟩ := N.halfPlaneCover_surjective (h (M.halfPlaneCover a))
  obtain ⟨C, hC, _hCac⟩ := LiZhongQC.exists_lift hpM hpN h a c hc
  have hholo := (analyticHomeomorph_iff_sourceBiholomorphic
    m.surface.toRiemannAtlas n.surface.toRiemannAtlas h).mp hh
  obtain ⟨P, hP⟩ := LiZhongQC.utm_eq_smul_of_isKQC_one C
    (LiZhongQC.h23l_lift_isKQC hpM hpN ((LiZhongQC.isKQCRS_one_iff h).mpr hholo) hC)
  let invm := _root_.toContinuousMap m.marking.toHomeomorph.symm
  have hhom' : ContinuousMap.Homotopic (_root_.toContinuousMap h) (_root_.toContinuousMap f) := by
    have ht := hhom.comp (ContinuousMap.Homotopic.refl invm)
    have hl : ((_root_.toContinuousMap h).comp m.markingMap).comp invm =
        _root_.toContinuousMap h := by
      ext y
      exact congrArg h (m.marking.toHomeomorph.apply_symm_apply y)
    have hr : n.markingMap.comp invm = _root_.toContinuousMap f := by
      ext y
      rfl
    rw [hl, hr] at ht
    exact ht
  obtain ⟨δ, hδ, hrel⟩ :=
    (LiZhongQC.thm23_1_homotopy_iff hpM hpN h f hC hF).mp hhom'
  let Q := δ⁻¹ * P
  have hQ (y : ℍ) : Q • y = δ⁻¹ • C y := by
    change (δ⁻¹ * P) • y = δ⁻¹ • C y
    rw [mul_smul, ← hP y]
  refine ⟨Q, ?_⟩
  intro d z
  let Dm := M.markedPolygonEndpointDeck (m.marking.toHomeomorph.symm.trans e) a ha d
  let Dn := N.markedPolygonEndpointDeck (n.marking.toHomeomorph.symm.trans e) b hb d
  obtain ⟨A, hA, hrep⟩ := exists_uniformization_matrix_representative hpM Dm a
  have hnat (y : ℍ) : Dn • F y = F (Dm • y) :=
    m.markedPolygonEndpointDeck_intertwines_lift n M N e a b ha hb F hF hFab d y
  have hR := hrel A hA (C z)
  rw [C.symm_apply_apply] at hR
  calc
    Q • (Dm • z) = δ⁻¹ • C (Dm • z) := hQ _
    _ = δ⁻¹ • C (A • z) := congrArg (fun y : ℍ => δ⁻¹ • C y) (hrep z).symm
    _ = F (A • F.symm (δ⁻¹ • C z)) := by rw [hR, inv_smul_smul]
    _ = F (Dm • F.symm (Q • z)) := by rw [← hQ z, hrep]
    _ = Dn • (Q • z) := by
      simpa only [F.apply_symm_apply] using (hnat (F.symm (Q • z))).symm

/-- The full ordered projective generator system of given dynamically
normalized models is determined by the original marked equivalence class. -/
theorem MarkedRiemannSurface.given_normalizedCanonicalGenerators_unique
    (m n : MarkedRiemannSurface.{0, 0} R)
    (M : HyperbolicSurfaceModel m.surface.toRiemannSurface)
    (N : HyperbolicSurfaceModel n.surface.toRiemannSurface)
    (hg : 1 < g) (e : X ≃ₜ PolygonQuotient g) (a b : ℍ)
    (ha : M.halfPlaneCover a = (m.marking.toHomeomorph.symm.trans e).symm (boundaryBase g).val)
    (hb : N.halfPlaneCover b = (n.marking.toHomeomorph.symm.trans e).symm (boundaryBase g).val)
    (γ δ : Edge g → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hγ : ∀ (d : Edge g) (z : ℍ), γ d • z =
      M.markedPolygonEndpointDeck (m.marking.toHomeomorph.symm.trans e) a ha d • z)
    (hδ : ∀ (d : Edge g) (z : ℍ), δ d • z =
      N.markedPolygonEndpointDeck (n.marking.toHomeomorph.symm.trans e) b hb d • z)
    (hγα : MobiusAttractiveFixedPoint (realSLMobius (γ (finalHandle hg, 0))) (1 : ℂ))
    (hδα : MobiusAttractiveFixedPoint (realSLMobius (δ (finalHandle hg, 0))) (1 : ℂ))
    (hγβ : IsMobiusAttractingRepellingPair (realSLMobius (γ (finalHandle hg, 1))) ∞ (0 : ℂ))
    (hδβ : IsMobiusAttractingRepellingPair (realSLMobius (δ (finalHandle hg, 1))) ∞ (0 : ℂ))
    (hmn : MarkedRiemannSurface.Equivalent m n) :
    ∀ d : Edge g, realSLMobius (γ d) = realSLMobius (δ d) := by
  obtain ⟨Q, hQ⟩ := m.exists_markedPolygonEndpointDeck_conjugator n M N e a b ha hb hmn
  have hacts (d : Edge g) (z : ℍ) : Q • (γ d • z) = δ d • (Q • z) := by
    rw [hγ d z, hδ d (Q • z)]
    exact hQ d z
  have hconj (d : Edge g) : realSLMobius (δ d) =
      realSLMobius Q * realSLMobius (γ d) * (realSLMobius Q)⁻¹ := by
    calc
      realSLMobius (δ d) = realSLMobius (Q * γ d * Q⁻¹) := by
        apply realSLMobius_eq_of_native_action
        intro z
        simpa only [mul_smul, smul_inv_smul] using (hacts d (Q⁻¹ • z)).symm
      _ = _ := by rw [map_mul, map_mul, map_inv]
  have hqid : realSLMobius Q = 1 := normalizedCanonicalPair_conjugator_eq_one
    (realSLMobius (γ (finalHandle hg, 0))) (realSLMobius (γ (finalHandle hg, 1)))
    (realSLMobius (δ (finalHandle hg, 0))) (realSLMobius (δ (finalHandle hg, 1)))
    (realSLMobius Q) hγα hδα hγβ hδβ
    (hconj (finalHandle hg, 0)) (hconj (finalHandle hg, 1))
  intro d
  have h := hconj d
  rw [hqid, one_mul, inv_one, mul_one] at h
  exact h.symm

end LowDimensionalTopology.Geometry.Teichmuller
