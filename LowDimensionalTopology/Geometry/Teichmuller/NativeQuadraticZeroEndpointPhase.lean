module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticThetaArcGeodesic
public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticThetaArcPhase
public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticBigonUniqueness

/-!
# The phase of two arcs joining the same lifted zeros

The original smooth injective arcs become local geodesics of the same native
lifted differential. The finite bigon argument proves
their actual common trace. A regular interior point cannot correspond to a
zero endpoint of the second arc, so the local phase comparison applies.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC
open LowDimensionalTopology.Unproved.Teichmuller

/-- Smooth injective fixed-phase arcs joining the same actual lifted zeros
have the same unit phase, using finite bigon geometry and the local angle bound. -/
theorem native_thetaArc_phase_eq_of_zero_endpoints
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (g : ℕ) (_hg : 2 ≤ g) (_hgenus : R.HasGenus g)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hbigon : QuadraticGeodesicBigonExtraction R q hq (Γ := Γ) (p := p))
    (hangle : QuadraticGeodesicLocalAngleBound R q hq (Γ := Γ) (p := p)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ _hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (α β : Path a b) (θα θβ : ℝ),
        ψ (a : ℂ) = 0 → ψ (b : ℂ) = 0 →
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface α →
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface β →
        Function.Injective α → Function.Injective β →
        IsHorizontalArc (fun z => Complex.exp (-(θα : ℂ) * Complex.I) * ψ z)
          (fun u : ℝ => (α.extend u : ℂ)) 0 1 →
        IsHorizontalArc (fun z => Complex.exp (-(θβ : ℂ) * Complex.I) * ψ z)
          (fun u : ℝ => (β.extend u : ℂ)) 0 1 →
        Complex.exp ((θα : ℂ) * Complex.I) =
          Complex.exp ((θβ : ℂ) * Complex.I) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b α β θα θβ ha hb hαSmooth hβSmooth hαInj hβInj hαArc hβArc
  have hab : a ≠ b := by
    intro h
    have hends : α (0 : unitInterval) = α 1 :=
      α.source.trans (h.trans α.target.symm)
    have h01 : (0 : ℝ) = 1 :=
      congrArg (fun u : unitInterval => (u : ℝ)) (hαInj hends)
    exact zero_ne_one h01
  have hαGeo : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) α :=
    native_smooth_thetaArc_isPhiGeodesic R q hq hp α θα hαSmooth hαArc
  have hβGeo : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) β :=
    native_smooth_thetaArc_isPhiGeodesic R q hq hp β θβ hβSmooth hβArc
  have htrace : Set.range α = Set.range β :=
    native_quadratic_geodesic_range_eq_of_bigon_inputs
      R q hq hbigon hangle hp α β hab hαGeo hβGeo
  have hs : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hregular : ψ (α.extend (1 / 2) : ℂ) ≠ 0 :=
    (mul_ne_zero_iff.mp (hαArc (1 / 2) hs).2.2.1).2
  have hmem : α ⟨1 / 2, Ioo_subset_Icc_self hs⟩ ∈ Set.range β := by
    rw [← htrace]
    exact mem_range_self _
  obtain ⟨u, hu⟩ := hmem
  have hpointU : α.extend (1 / 2) = β u :=
    (α.extend_apply (Ioo_subset_Icc_self hs)).trans hu.symm
  have hu0 : u ≠ 0 := by
    intro hzero
    apply hregular
    rw [hpointU, hzero, β.source]
    exact ha
  have hu1 : u ≠ 1 := by
    intro hone
    apply hregular
    rw [hpointU, hone, β.target]
    exact hb
  have ht : (u : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu0)),
      lt_of_le_of_ne u.property.2 (unitInterval.coe_ne_one.mpr hu1)⟩
  have hpoint : α.extend (1 / 2) = β.extend (u : ℝ) :=
    hpointU.trans (β.extend_apply u.property).symm
  exact thetaArc_phase_eq_of_same_actual_trace R q hq hp α β θα θβ
    (1 / 2) (u : ℝ) hαInj hβInj htrace hs ht hpoint hαArc hβArc

end LowDimensionalTopology.Geometry.Teichmuller
