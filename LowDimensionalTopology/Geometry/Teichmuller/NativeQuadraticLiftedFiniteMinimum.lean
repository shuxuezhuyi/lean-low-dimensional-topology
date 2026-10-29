module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticProjectionDistance
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFiniteQuadraticMinimum
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S25_QuadraticDifferentials
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Finite minima between fixed lifts of the actual quadratic differential

A compact-surface minimum is lifted in its fixed endpoint homotopy class.
The existing covering endpoint theorem and exact coefficient integral keep
both actual lifted endpoints and all original lifted path competitors.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- There is a finite minimum among all paths between the actual fixed lifts. -/
theorem exists_native_lifted_finite_minimum
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ a b : UpperHalfPlane, ∃ γ : Path a b,
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) γ < ⊤ ∧
        ∀ δ : Path a b, phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) γ ≤
          phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  intro hp
  let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
    (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b
  let η : Path a b := PathConnectedSpace.somePath a b
  let α : Path (p a) (p b) := η.map hp.1.continuous
  have hqfun : (q : X → ℂ → ℂ) ≠ 0 := fun h => hq (Subtype.ext h)
  obtain ⟨γR, hγRhom, hγRmin⟩ := thm25_4_shortest_exists q.property hqfun α
  obtain ⟨β, hβhom, hβfin⟩ := s25s_finite_rep q.property hqfun α
  have hγRfin : phiLengthPath (q : X → ℂ → ℂ) γR < ⊤ :=
    (hγRmin β hβhom).trans_lt hβfin
  have hγR0 : γR.toContinuousMap 0 = p a := γR.source
  have hα0 : α.toContinuousMap 0 = p a := α.source
  let L : C(unitInterval, UpperHalfPlane) := hp.1.liftPath γR.toContinuousMap a hγR0
  have hL0 : L 0 = a := hp.1.liftPath_zero γR.toContinuousMap a hγR0
  have hηcanonical : η.toContinuousMap = hp.1.liftPath α.toContinuousMap a hα0 :=
    (hp.1.eq_liftPath_iff' hα0).2 ⟨rfl, η.source⟩
  have hend := hp.1.liftPath_apply_one_eq_of_homotopicRel
    (show γR.toContinuousMap.HomotopicRel α.toContinuousMap {0, 1} from hγRhom)
    a hγR0 hα0
  have hL1 : L 1 = b := by
    change hp.1.liftPath γR.toContinuousMap a hγR0 1 = b
    rw [hend, ← hηcanonical]
    exact η.target
  let γ : Path a b := ⟨L, hL0, hL1⟩
  have hγlift (t : unitInterval) : p (γ t) = γR t :=
    congrFun (hp.1.liftPath_lifts γR.toContinuousMap a hγR0) t
  obtain ⟨hγLip, hγintegral⟩ :=
    utm_length_lift q.property hp γR γ.toContinuousMap hγlift hγRfin
  have hlength : phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) γ =
      phiLengthPath (q : X → ℂ → ℂ) γR := by
    change phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) γ 0 1 = _
    rw [liftedQuadraticLengthOn_eq_integral_of_lipschitz R.toRiemannSurface q hp
      a b γ 0 1 le_rfl zero_lt_one le_rfl hγLip]
    exact hγintegral
  refine ⟨γ, hlength.symm ▸ hγRfin, ?_⟩
  intro δ
  have hδhom : (δ.map hp.1.continuous).Homotopic α :=
    (SimplyConnectedSpace.paths_homotopic δ η).map ⟨p, hp.1.continuous⟩
  calc phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) γ =
        phiLengthPath (q : X → ℂ → ℂ) γR := hlength
    _ ≤ phiLengthPath (q : X → ℂ → ℂ) (δ.map hp.1.continuous) := hγRmin _ hδhom
    _ ≤ phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ :=
      actualUniformizingProjection_pathLength_le R.toRiemannSurface q hp δ

/-- The finite lifted minimum is a local geodesic of the same differential. -/
theorem exists_native_lifted_finite_geodesic_minimum
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ a b : UpperHalfPlane, ∃ γ : Path a b,
        IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) γ ∧
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) γ < ⊤ ∧
        ∀ δ : Path a b, phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) γ ≤
          phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
    (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b
  obtain ⟨γ, hfinite, hmin⟩ := exists_native_lifted_finite_minimum R q hq hp a b
  exact ⟨γ, native_finite_allPathMinimum_isPhiGeodesic R q hq hp γ hfinite hmin,
    hfinite, hmin⟩

end LowDimensionalTopology.Geometry.Teichmuller
