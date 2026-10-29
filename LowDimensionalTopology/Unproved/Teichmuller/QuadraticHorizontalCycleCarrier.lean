module

public import LowDimensionalTopology.Geometry.Teichmuller.DECoverDescent
public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticSegments
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticPiecewiseSmoothPath
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness

/-!
# An explicit classical carrier for an actual horizontal leaf circle

The original continuous clock is unrestricted. The carrier supplies a new
admissible parameter on the same embedded trace, with finite genuine zero
cuts and actual horizontal open sides. This finite admissible parameterization
is an unproved classical input. It contains no metric or geodesic condition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller LiZhongQC

/-- An embedded based circle follows actual horizontal natural-coordinate
leaves at every regular point, without a regularity condition on its clock. -/
def IsActualHorizontalLeafLoop (ψ : ℂ → ℂ)
    {a : UpperHalfPlane} (C : Path a a) : Prop :=
  InjOn C (Ico (0 : unitInterval) 1) ∧
    ∀ t : unitInterval, ψ (C t : ℂ) ≠ 0 →
      ∃ e : OpenPartialHomeomorph ℂ ℂ,
        e.source ⊆ upperHalf ∧ (C t : ℂ) ∈ e.source ∧
        AnalyticOnNhd ℂ (e : ℂ → ℂ) e.source ∧
        (∀ z ∈ e.source, deriv (e : ℂ → ℂ) z ^ 2 = ψ z) ∧
        ∀ᶠ s : unitInterval in 𝓝 t,
          (C s : ℂ) ∈ e.source ∧ (e (C s : ℂ)).im = (e (C t : ℂ)).im

/-- Classical finite admissible parameterization of the same actual embedded
leaf-circle trace. The output retains its atlas, endpoints and genuine zero cuts. -/
def NativeFiniteHorizontalCycleCarrier
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (_hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → X} : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  ∀ _hp : IsUniformization Γ p,
    let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
    ∀ {a : UpperHalfPlane} (C : Path a a), IsActualHorizontalLeafLoop ψ C →
      ∃ δ : Path a a,
        Set.range δ = Set.range C ∧
        InjOn δ (Ico (0 : unitInterval) 1) ∧
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface δ ∧
        ∃ n : ℕ, 0 < n ∧ ∃ cuts : Fin (n + 1) → unitInterval,
          StrictMono cuts ∧ cuts 0 = 0 ∧ cuts (Fin.last n) = 1 ∧
          (∀ i : Fin (n + 1), 0 < i.val → i.val < n → ψ (δ (cuts i) : ℂ) = 0) ∧
          ∀ i : Fin n,
            IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ))
              (cuts i.castSucc : ℝ) (cuts i.succ : ℝ)

end LowDimensionalTopology.Unproved.Teichmuller
