module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticSegmentLocalGeodesic
public import LowDimensionalTopology.Geometry.Teichmuller.NativeSmoothQuadraticLocalGlobal

/-!
# Unique global minimum of the same smooth quadratic segment

The supplied segment itself attains the actual smooth-path infimum. Every
smooth global minimizer has the same unparametrized trace; no equality of
path parametrizations is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC LowDimensionalTopology.Unproved.Teichmuller

/-- The original source-smooth segment is globally shortest, with unique
minimizing range, under the explicit geometric and classical inputs. -/
theorem native_sourceSmooth_segment_uniqueGlobalMinimizer
    (hArc : NativeCommonMonotoneArc) (happrox : NativeQuadraticSmoothCofinality)
    (hordinary : NativeQuadraticOrdinaryEndpointRay) (hzero : NativeQuadraticZeroEndpointRay)
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (g : ℕ) (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hbigon : QuadraticGeodesicBigonExtraction R q hq (Γ := Γ) (p := p))
    (hextract : QuadraticGeodesicFinitePolygonExtraction R q hq (Γ := Γ) (p := p))
    (hangle : QuadraticGeodesicLocalAngleBound R q hq (Γ := Γ) (p := p)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (L : Path a b),
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface L →
        IsQuadraticSegment upperHalfNativeSurface qH L.toContinuousMap →
        IsGlobalQuadraticMinimizer upperHalfNativeSurface qH L ∧
          ∀ δ : Path a b, IsGlobalQuadraticMinimizer upperHalfNativeSurface qH δ →
            Set.range δ = Set.range L := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
    (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b L hSmooth hSeg
  have hLGeo := native_sourceSmooth_segment_isPhiGeodesic hordinary hzero R q hq hp L hSmooth hSeg
  have hLMin : IsGlobalQuadraticMinimizer upperHalfNativeSurface qH L :=
    (native_sourceSmooth_isPhiGeodesic_iff_globalMinimizer hArc happrox
      R g hg hgenus q hq hbigon hextract hangle hp L hSmooth).mp hLGeo
  have hab : a ≠ b := by
    intro heq
    have hends : L (0 : unitInterval) = L (1 : unitInterval) := by
      rw [L.source, L.target]
      exact heq
    have hbad := congrArg (fun u : unitInterval => (u : ℝ)) (hSeg.1 hends)
    exact zero_ne_one hbad
  refine ⟨hLMin, ?_⟩
  intro δ hδMin
  have hδGeo :=
    (native_sourceSmooth_isPhiGeodesic_iff_globalMinimizer hArc happrox
      R g hg hgenus q hq hbigon hextract hangle hp δ hδMin.1).mpr hδMin
  exact native_quadratic_geodesic_range_eq_of_bigon_inputs
    R q hq hbigon hangle hp δ L hab hδGeo hLGeo

end LowDimensionalTopology.Geometry.Teichmuller
