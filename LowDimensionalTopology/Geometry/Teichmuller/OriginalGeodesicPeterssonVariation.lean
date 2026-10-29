module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGeodesicSeriesLocallyUniform
public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeriesConvergence
public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeriesAutomorphic
public import LowDimensionalTopology.Geometry.Teichmuller.NativeGeneralEndpointLengthPetersson

/-!
# The same original simple geodesic and its native Petersson variation

One actual full-period covering of the original simple geodesic has its
convergent, holomorphic, integrable automorphic endpoint series. Every original
compatible direction has the marked-length first variation given by its
literal coefficient pairing on each original fundamental region.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces GammaMeasurableBeltrami

/-- The same original simple geodesic has its genuine endpoint Petersson
series and native original-coefficient marked-length first variation. -/
theorem originalClosedGeodesic_exists_petersson_variation
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {M : HyperbolicSurfaceModel R.toRiemannSurface} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ)
    (hp : let := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∃ (A : Deck) (hA : Hyperbolic.realSLMobius A ≠ 1)
      (ht : 4 < (Matrix.trace A.val) ^ 2), A ∈ Γ ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
        (Subgroup.zpowers (Hyperbolic.realSLMobius A))
      let CA := Quotient (QuotientGroup.rightRel SA)
      ∀ (ρ : CA → Γ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
        let T : CA → ℂ → ℂ := fun u z =>
          GeodesicSeries.seed (Hyperbolic.hHyperbolicAxis A hA ht)
              (LiZhongQC.h36p_m (ρ u).val z) * (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2
        let Θ : ℂ → ℂ := fun z => ∑' u : CA, T u z
        (∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
          HasSum (fun u : CA => T u z) (Θ z) ∧ Summable (fun u : CA => ‖T u z‖)) ∧
        TendstoLocallyUniformlyOn
          (fun (E : Finset CA) (z : ℂ) => ∑ u ∈ E, T u z) Θ
          (atTop : Filter (Finset CA)) LiZhongQC.upperHalf ∧
        ∀ (F : Set ℂ), LiZhongQC.IsFundamentalDomainH Γ F →
          Θ ∈ LiZhongQC.integrableAutomorphicQD Γ F ∧
          ∀ μ : Space Γ,
            HasDerivAt
              (fun t : ℝ => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus q.toLoop
                (TeichmullerSpace.coefficientProjection R hg hgenus
                  (canonicalHandleGroupPresentation g) hΓ (LiZhongQC.s27g_actsFreely hp) hp
                  ((t : ℂ) • μ)))
              ((2 / Real.pi) * (LiZhongQC.beltramiPairing F (planeRepresentative μ.val) Θ).re) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  dsimp only
  obtain ⟨A, hA, ht, hAΓ, hcov, hlocal⟩ :=
    GeodesicSeries.originalClosedGeodesic_exists_locallyUniform_petersson R q hp hcircle
  refine ⟨A, hA, ht, hAΓ, hcov, ?_⟩
  intro ρ hρ
  refine ⟨GeodesicSeries.geodesicSeries_hasSum_norm Γ hΓ A hAΓ hA ht ρ hρ,
    hlocal ρ hρ, ?_⟩
  intro F hF
  refine ⟨GeodesicSeries.geodesicSeries_mem_integrableAutomorphicQD Γ hΓ A hAΓ hA ht ρ hρ F hF,
    fun μ => ?_⟩
  exact marked_length_hasDerivAt_general_endpoint_petersson R hg hgenus hΓ hp
    q.toLoop A hAΓ hcov hA ht μ ρ hρ F hF

end LowDimensionalTopology.Geometry.Teichmuller
