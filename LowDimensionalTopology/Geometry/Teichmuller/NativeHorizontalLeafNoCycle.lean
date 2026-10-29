module

public import LowDimensionalTopology.Unproved.Teichmuller.QuadraticHorizontalCycleCarrier
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFiniteHorizontalCycle
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticGeodesicPolygonConsumers

/-!
# No actual embedded horizontal leaf circle under the explicit carrier input

The carrier's same-trace admissible path is proved locally geodesic by the
finite horizontal-side theorem. The existing polygon inputs then make that
actual loop constant, contradicting its supplied half-open-interval embedding.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC LowDimensionalTopology.Unproved.Teichmuller

/-- An actual embedded horizontal leaf circle cannot exist, using the explicit
classical carrier and the separate zero-ray, polygon-extraction and angle inputs. -/
theorem native_horizontal_leaf_loop_false
    (hzero : NativeQuadraticZeroEndpointRay)
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hextract : QuadraticGeodesicFinitePolygonExtraction R q hq (Γ := Γ) (p := p))
    (hangle : QuadraticGeodesicLocalAngleBound R q hq (Γ := Γ) (p := p))
    (hcarrier : NativeFiniteHorizontalCycleCarrier R q hq (Γ := Γ) (p := p)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ _hp : IsUniformization Γ p,
      ∀ {a : UpperHalfPlane} (C : Path a a),
        IsActualHorizontalLeafLoop (utm_liftQD (q : X → ℂ → ℂ) p) C → False := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  intro a C hC
  obtain ⟨δ, _htrace, hδinj, hSmooth, n, hn, cuts, hcuts, h0, h1, hzeros, hhorizontal⟩ :=
    hcarrier hp C hC
  have hgeo : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δ := by
    exact native_finite_horizontal_cycle_isPhiGeodesic hzero R q hq hp δ
      hSmooth hδinj n hn cuts hcuts h0 h1 hzeros hhorizontal
  have hconstant : ∀ u : unitInterval, δ u = a := by
    exact nativeQuadraticGeodesic_loop_constant_of_polygon_inputs
      R q hq hextract hangle hp a δ hgeo
  let uHalf : unitInterval := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have h0mem : (0 : unitInterval) ∈ Ico (0 : unitInterval) 1 :=
    ⟨le_rfl, zero_lt_one⟩
  have hHalfmem : uHalf ∈ Ico (0 : unitInterval) 1 := by
    change ((0 : unitInterval) : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) < ((1 : unitInterval) : ℝ)
    norm_num only [Set.Icc.coe_zero, Set.Icc.coe_one]
    exact ⟨True.intro, True.intro⟩
  have htime : (0 : unitInterval) = uHalf :=
    hδinj h0mem hHalfmem ((hconstant 0).trans (hconstant uHalf).symm)
  have hval : (0 : ℝ) = 1 / 2 := by
    simpa only [Set.Icc.coe_zero, uHalf] using
      congrArg (fun u : unitInterval => (u : ℝ)) htime
  norm_num at hval

end LowDimensionalTopology.Geometry.Teichmuller
