module

public import LowDimensionalTopology.Geometry.Teichmuller.ActualQuadraticGeodesicLift
public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticBigonUniqueness
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Original quadratic-geodesic traces in a distinct-endpoint homotopy class

Both original local geodesics lift from the same point and have the same lifted
endpoint. Their actual lifts are local geodesics of the same lifted quadratic
differential. The actual finite bigon count then proves
equality of lifted ranges, which projects to the original ranges.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC
open LowDimensionalTopology.Unproved.Teichmuller

/-- Two original local quadratic geodesics with distinct endpoints have the
same range in a fixed endpoint homotopy class, using finite bigon geometry and the local angle bound. -/
theorem phiGeodesic_range_eq_of_homotopic_of_endpoints_ne
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (g : ℕ) (_hg : 2 ≤ g) (_hgenus : R.HasGenus g)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (p : UpperHalfPlane → X) (_hp : IsUniformization Γ p)
      (_hbigon : QuadraticGeodesicBigonExtraction R q hq (Γ := Γ) (p := p))
      (_hangle : QuadraticGeodesicLocalAngleBound R q hq (Γ := Γ) (p := p))
      {a b : X} (_hab : a ≠ b) (α β : Path a b),
      IsPhiGeodesicRS (q : X → ℂ → ℂ) α →
      IsPhiGeodesicRS (q : X → ℂ → ℂ) β →
      α.Homotopic β → Set.range α = Set.range β := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro Γ p hp hbigon hangle a b hab α β hα hβ hhom
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  obtain ⟨z₀, hz₀⟩ := hp.2.2.1 a
  have hα0 : (α : C(unitInterval, X)) 0 = p z₀ := by
    rw [hz₀]
    exact α.source
  have hβ0 : (β : C(unitInterval, X)) 0 = p z₀ := by
    rw [hz₀]
    exact β.source
  let A : C(unitInterval, UpperHalfPlane) :=
    hp.1.liftPath (α : C(unitInterval, X)) z₀ hα0
  let B : C(unitInterval, UpperHalfPlane) :=
    hp.1.liftPath (β : C(unitInterval, X)) z₀ hβ0
  have hA0 : A 0 = z₀ := hp.1.liftPath_zero (α : C(unitInterval, X)) z₀ hα0
  have hB0 : B 0 = z₀ := hp.1.liftPath_zero (β : C(unitInterval, X)) z₀ hβ0
  have hAlift : ∀ u, p (A u) = α u :=
    fun u => congrFun (hp.1.liftPath_lifts (α : C(unitInterval, X)) z₀ hα0) u
  have hBlift : ∀ u, p (B u) = β u :=
    fun u => congrFun (hp.1.liftPath_lifts (β : C(unitInterval, X)) z₀ hβ0) u
  have hB1A1 : B 1 = A 1 :=
    hp.1.liftPath_apply_one_eq_of_homotopicRel hhom.symm z₀ hβ0 hα0
  let δA : Path (A 0) (A 1) := ⟨A, rfl, rfl⟩
  let δB₀ : Path (B 0) (B 1) := ⟨B, rfl, rfl⟩
  let δB : Path (A 0) (A 1) := δB₀.cast (hA0.trans hB0.symm) hB1A1.symm
  have hδA : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δA :=
    isPhiGeodesicRS_actualLift R.toRiemannSurface q hp α A hAlift hα
  have hδB₀ : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δB₀ :=
    isPhiGeodesicRS_actualLift R.toRiemannSurface q hp β B hBlift hβ
  have hδB : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δB := by
    simpa only [δB, IsPhiGeodesicRS, phiLengthOn, Path.extend_cast] using hδB₀
  have hends : A 0 ≠ A 1 := by
    intro h
    apply hab
    calc a = p (A 0) := ((hAlift 0).trans α.source).symm
      _ = p (A 1) := congrArg p h
      _ = b := (hAlift 1).trans α.target
  have htraces : Set.range δA = Set.range δB :=
    native_quadratic_geodesic_range_eq_of_bigon_inputs
      R q hq hbigon hangle hp δA δB hends hδA hδB
  have hAp : (p ∘ δA) = (α : unitInterval → X) := funext hAlift
  have hBp : (p ∘ δB) = (β : unitInterval → X) := funext hBlift
  have hproject := congrArg (fun S : Set UpperHalfPlane => p '' S) htraces
  rw [← Set.range_comp, ← Set.range_comp, hAp, hBp] at hproject
  exact hproject

end LowDimensionalTopology.Geometry.Teichmuller
