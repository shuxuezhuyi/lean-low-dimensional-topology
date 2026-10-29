module

public import LowDimensionalTopology.Geometry.Teichmuller.AnyInitialNaturalParameter

/-! Terminal quadratic differentials for the literal normalized Teichmüller
coefficient. The zero initial differential has an explicit canonical extension. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter Topology
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open LiZhongQC
universe u v
variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

/-- Finite zero orders and the affine formula for every supplied initial parameter. -/
def BookTerminalDifferentialProperties
    (R : Surfaces.ClosedRiemannSurface X) (S : Surfaces.ClosedRiemannSurface Y)
    (φ : Surfaces.HolomorphicQuadraticDifferential R.toRiemannAtlas) (f : X ≃ₜ Y)
    (ψ : Surfaces.HolomorphicQuadraticDifferential S.toRiemannAtlas) : Prop :=
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  (∀ (p : X) (m : ℕ), IsZeroOfOrder φ p m → IsZeroOfOrder ψ (f p) m) ∧
    ∀ (p : X), IsRegularPoint φ p →
      ∀ ζ : ℂ → ℂ, IsNaturalParameterAt φ p ζ →
        ∃ η : ℂ → ℂ, IsNaturalParameterAt ψ (f p) η ∧
          ∀ᶠ z in 𝓝 (chartAt ℂ p p),
            η (localMapExpr f p z) =
              (ζ z + (QuadraticL1.bookNorm R φ : ℂ) * conj (ζ z)) /
                (1 - (QuadraticL1.bookNorm R φ : ℂ))

/-- The source properties with the canonical zero terminal specified separately. -/
def BookTerminalDifferentialConditions
    (R : Surfaces.ClosedRiemannSurface X) (S : Surfaces.ClosedRiemannSurface Y)
    (φ : Surfaces.HolomorphicQuadraticDifferential R.toRiemannAtlas) (f : X ≃ₜ Y)
    (ψ : Surfaces.HolomorphicQuadraticDifferential S.toRiemannAtlas) : Prop :=
  (φ = 0 → ψ = 0) ∧ BookTerminalDifferentialProperties R S φ f ψ

/-- The literal book coefficient determines a unique terminal differential under
the explicit convention that the zero initial differential has zero terminal differential. -/
theorem bookTerminalDifferential_existsUnique_canonical
    (R : Surfaces.ClosedRiemannSurface X) (S : Surfaces.ClosedRiemannSurface Y)
    (φ : Surfaces.HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (hφ : φ ∈ QuadraticL1.openUnitBall R) (f : X ≃ₜ Y)
    (hf :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      IsQCRS f)
    (hμ : HasBookTeichmullerCoefficient R S f φ) :
    ∃! ψ : Surfaces.HolomorphicQuadraticDifferential S.toRiemannAtlas,
      BookTerminalDifferentialConditions R S φ f ψ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  rcases bookCoefficient_geometric R S φ hφ f hf hμ with ⟨hzero, -⟩ | ⟨ψ, hT⟩
  · refine ⟨0, ?_, ?_⟩
    · refine ⟨fun _ => rfl, ?_, ?_⟩
      · intro p m hm
        simp [hzero, IsZeroOfOrder] at hm
      · intro p hp
        exfalso
        exact hp (by simp [hzero])
    · intro ψ hψ
      exact hψ.1 hzero
  · have hne : φ ≠ 0 := by
      intro hzero
      apply hT.initial_ne
      simp only [hzero, Submodule.coe_zero]
    refine ⟨ψ, ?_, ?_⟩
    · exact ⟨fun hz => (hne hz).elim,
        bookTeichmuller_zeroOrders_and_anyInitialNaturalParameter R S φ ψ f
          (QuadraticL1.bookNorm R φ) hT⟩
    · intro ψ' hψ'
      have hT' : IsTeichmullerMap f φ ψ' (QuadraticL1.bookNorm R φ) := by
        refine ⟨hT.qc, hT.initial, hT.initial_ne, ψ'.property,
          hT.k_nonneg, hT.k_lt_one, ?_, hψ'.2.1⟩
        intro p hp
        obtain ⟨_, A, _, hA, _, _⟩ := hT.regular p hp
        obtain ⟨η, hη, hrel⟩ := hψ'.2.2 p hp A hA
        refine ⟨?_, A, η, hA, hη, hrel⟩
        change (ψ' : Y → ℂ → ℂ) (f p) (chartAt ℂ (f p) (f p)) ≠ 0
        rw [← hη.2.2.2.self_of_nhds]
        exact pow_ne_zero 2 hη.2.2.1
      exact bookTerminalDifferential_unique R S φ f ψ' ψ
        (QuadraticL1.bookNorm R φ) hT' hT

/-- For a nonzero initial differential the two source properties alone determine
one terminal differential, on the same original target and at the literal book norm. -/
theorem bookTerminalDifferential_existsUnique_of_ne
    (R : Surfaces.ClosedRiemannSurface X) (S : Surfaces.ClosedRiemannSurface Y)
    (φ : Surfaces.HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (hφ : φ ∈ QuadraticL1.openUnitBall R) (hφne : φ ≠ 0) (f : X ≃ₜ Y)
    (hf :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      IsQCRS f)
    (hμ : HasBookTeichmullerCoefficient R S f φ) :
    ∃! ψ : Surfaces.HolomorphicQuadraticDifferential S.toRiemannAtlas,
      BookTerminalDifferentialProperties R S φ f ψ := by
  obtain ⟨ψ, hψ, huniq⟩ := bookTerminalDifferential_existsUnique_canonical R S φ hφ f hf hμ
  refine ⟨ψ, hψ.2, ?_⟩
  intro ψ' hψ'
  exact huniq ψ' ⟨fun hz => (hφne hz).elim, hψ'⟩

end LowDimensionalTopology.Geometry.Teichmuller
