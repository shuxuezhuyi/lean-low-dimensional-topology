module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeLiftedHorizontalArcNoClosure
public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticZeroEndpointPhase

/-!
# Injectivity and phase uniqueness of the actual lifted arcs

Rotating the original quadratic differential makes a fixed-phase arc horizontal.
The existing endpoint-separation theorem applies to every subinterval, so
injectivity is a conclusion. The same-zero phase comparison then retains only
the original source-smooth carrier and the finite bigon/angle inputs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC
open LowDimensionalTopology.Unproved.Teichmuller

/-- Every fixed-phase arc of the actual lifted differential is injective,
including its continuous endpoints. -/
theorem native_thetaArc_injective
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ _hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      ∀ {a b : UpperHalfPlane} (α : Path a b) (θ : ℝ),
        IsHorizontalArc (fun z => Complex.exp (-(θ : ℂ) * Complex.I) * ψ z)
          (fun t : ℝ => (α.extend t : ℂ)) 0 1 →
        Function.Injective α := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  dsimp only
  intro a b α θ hθ
  let u : ℂ := Complex.exp (-(θ : ℂ) * Complex.I)
  let qθ : HolomorphicQuadraticDifferential R.toRiemannAtlas := u • q
  have hu : u ≠ 0 := Complex.exp_ne_zero _
  have hqθ : qθ ≠ 0 := smul_ne_zero hu hq
  have hψθ : utm_liftQD (qθ : X → ℂ → ℂ) p = fun z => u * ψ z := by
    funext z
    simp only [qθ, ψ, utm_liftQD, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hsep : ∀ s t : unitInterval, s < t → α s ≠ α t := by
    intro s t hst heq
    have hst' : (s : ℝ) < (t : ℝ) := hst
    have hArc : IsHorizontalArc (utm_liftQD (qθ : X → ℂ → ℂ) p)
        (fun r : ℝ => (α.extend r : ℂ)) (s : ℝ) (t : ℝ) := by
      rw [hψθ]
      intro r hr
      exact hθ r ⟨lt_of_le_of_lt s.property.1 hr.1,
        lt_of_lt_of_le hr.2 t.property.2⟩
    have hcont : ContinuousOn (fun r : ℝ => (α.extend r : ℂ))
        (Icc (s : ℝ) (t : ℝ)) :=
      (UpperHalfPlane.continuous_coe.comp α.continuous_extend).continuousOn
    have hH : (fun r : ℝ => (α.extend r : ℂ)) '' Icc (s : ℝ) (t : ℝ) ⊆ upperHalf := by
      rintro _ ⟨r, _, rfl⟩
      exact (α.extend r).im_pos
    have hne := nativeLiftedHorizontalArc_endpoints_ne R qθ hqθ Γ p hp
      (fun r : ℝ => (α.extend r : ℂ)) (s : ℝ) (t : ℝ) hst' hArc hcont hH
    apply hne
    rw [α.extend_apply s.property, α.extend_apply t.property]
    exact congrArg (fun z : UpperHalfPlane => (z : ℂ)) heq
  intro s t h
  rcases lt_trichotomy s t with hst | heq | hts
  · exact False.elim (hsep s t hst h)
  · exact heq
  · exact False.elim (hsep t s hts h.symm)

/-- Same-zero source-smooth fixed-phase arcs have the same unit phase;
their injectivity is derived from the actual original differential. -/
theorem native_thetaArc_phase_eq_of_zero_endpoints_without_injective
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (g : ℕ) (hg : 2 ≤ g) (hgenus : R.HasGenus g)
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
        IsHorizontalArc (fun z => Complex.exp (-(θα : ℂ) * Complex.I) * ψ z)
          (fun u : ℝ => (α.extend u : ℂ)) 0 1 →
        IsHorizontalArc (fun z => Complex.exp (-(θβ : ℂ) * Complex.I) * ψ z)
          (fun u : ℝ => (β.extend u : ℂ)) 0 1 →
        Complex.exp ((θα : ℂ) * Complex.I) =
          Complex.exp ((θβ : ℂ) * Complex.I) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b α β θα θβ ha hb hαSmooth hβSmooth hαArc hβArc
  exact native_thetaArc_phase_eq_of_zero_endpoints R g hg hgenus q hq hbigon hangle hp
    α β θα θβ ha hb hαSmooth hβSmooth
    (native_thetaArc_injective R q hq hp α θα hαArc)
    (native_thetaArc_injective R q hq hp β θβ hβArc) hαArc hβArc

end LowDimensionalTopology.Geometry.Teichmuller
