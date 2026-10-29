module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.InwardRegularEndpointGerm
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ProjectedOrthogonalCurveGerms

/-! Inward orthogonal endpoint curves in the same original projected finite clips. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- Two actual orthogonal native finite segments give inward curves with
nonzero coordinate derivatives and the original ambient intrinsic right angle. -/
theorem HyperbolicSurfaceModel.exists_projected_inward_orthogonal_germs
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (L N : HalfPlaneLine) (z w v : ℍ)
    (horth : L.OrthogonalAt N z) (hzw : z ≠ w) (hzv : z ≠ v)
    (hw : w ∈ L.carrier) (hv : v ∈ N.carrier)
    (g : OpenPartialHomeomorph X ℂ) (hg : g ∈ R.charts)
    (hgz : M.halfPlaneCover z ∈ g.source) :
    ∃ (α β : ℝ → X) (a b : ℝ) (d : ℂ), a ≠ 0 ∧ b ≠ 0 ∧ d ≠ 0 ∧
      α 0 = M.halfPlaneCover z ∧ β 0 = M.halfPlaneCover z ∧
      ContinuousAt α 0 ∧ ContinuousAt β 0 ∧
      HasDerivAt (fun t => g (α t)) (d * (a • L.tangentAt z)) 0 ∧
      HasDerivAt (fun t => g (β t)) (d * (b • N.tangentAt z)) 0 ∧
      deriv (fun t => g (α t)) 0 ≠ 0 ∧ deriv (fun t => g (β t)) 0 ≠ 0 ∧
      riemannIntrinsicCurveAngle R.toRiemannAtlas (M.halfPlaneCover z) α β 0 =
        Real.pi / 2 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (0 : ℝ) ε,
        α t ∈ M.halfPlaneCover '' closedHSegment z w ∧
        β t ∈ M.halfPlaneCover '' closedHSegment z v := by
  obtain ⟨γ, a, ha, hγ0, hγ, hDγ, _, ε, hε, hclipγ⟩ :=
    L.exists_inward_regular_endpoint_germ z w hzw horth.1 hw
  obtain ⟨σ, b, hb, hσ0, hσ, hDσ, _, η, hη, hclipσ⟩ :=
    N.exists_inward_regular_endpoint_germ z v hzv horth.2.1 hv
  obtain ⟨d, hd, hpγ, hpσ, hnγ, hnσ, hangle⟩ :=
    M.projected_orthogonal_curve_derivatives L N z horth γ σ 0 a b ha hb
      hγ hσ hγ0 hσ0 hDγ hDσ g hg hgz
  refine ⟨(fun t => M.halfPlaneCover (γ t)), (fun t => M.halfPlaneCover (σ t)),
    a, b, d, ha, hb, hd, ?_, ?_, ?_, ?_, hpγ, hpσ, hnγ, hnσ, hangle,
    min ε η, lt_min_iff.mpr ⟨hε, hη⟩, ?_⟩
  · exact congrArg M.halfPlaneCover hγ0
  · exact congrArg M.halfPlaneCover hσ0
  · exact M.halfPlaneCover_covering.continuous.continuousAt.comp hγ
  · exact M.halfPlaneCover_covering.continuous.continuousAt.comp hσ
  · intro t ht
    have htγ : t ∈ Ioo (0 : ℝ) ε := ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    have htσ : t ∈ Ioo (0 : ℝ) η := ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
    exact ⟨⟨γ t, ((mem_openHSegment_iff hzw).mp (hclipγ t htγ)).1, rfl⟩,
      ⟨σ t, ((mem_openHSegment_iff hzv).mp (hclipσ t htσ)).1, rfl⟩⟩

end LowDimensionalTopology.Geometry.Surfaces
