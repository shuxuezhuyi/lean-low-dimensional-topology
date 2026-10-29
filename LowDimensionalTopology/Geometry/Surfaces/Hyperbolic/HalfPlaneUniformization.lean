module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.AxisPowerLoops
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannStandardModels
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S22_RiemannSurfaces

/-!
# Uniformization of the same original hyperbolic model projection

The subgroup is the full actual SL(2,R) stabilizer of the given model's covering
projection. Neither the surface nor its projection is replaced by another
uniformization, and no representative-sign homomorphism is assumed.
-/

public section
noncomputable section

open Set
open scoped UpperHalfPlane Manifold ContDiff MatrixGroups

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- The original model's actual half-plane cover is a source uniformization by
its full actual matrix stabilizer, in the original surface atlas. -/
theorem HyperbolicSurfaceModel.exists_halfPlaneCover_uniformization
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        A ∈ Γ ↔ ∀ z : ℍ, M.halfPlaneCover (A • z) = M.halfPlaneCover z) ∧
      LiZhongQC.IsUniformization Γ M.halfPlaneCover := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨e, he, _heinv⟩ := LiZhongQC.s22c6_cayley_diffeomorph
  have heq : (e : ℍ → standardUnitDiscOpens) = halfPlaneToDisc := by
    funext z
    apply Subtype.ext
    exact (he z).trans (show LiZhongQC.cayley (z : ℂ) = (halfPlaneToDisc z : ℂ) from rfl)
  have hcayley : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      standardUnitDiscRiemannSurface.toRiemannAtlas halfPlaneToDisc := by
    rw [← heq]
    exact riemannAnalyticMap_of_contMDiff_ofManifold e.contMDiff_toFun
  let E : ℍ ≃ₜ extendedUnitDisc := cayleyHomeomorph.trans discFiniteHomeomorph.symm
  have hE : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      discRiemannSurface.toRiemannAtlas E :=
    (riemannAnalyticMap_homeomorph_symm standardUnitDiscHomeomorph
      standardUnitDiscHomeomorph_analytic).comp hcayley
  have hEinv : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas
      (RiemannAtlas.ofManifold ℍ) E.symm := riemannAnalyticMap_homeomorph_symm E hE
  have hpa : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      R.toRiemannAtlas M.halfPlaneCover := M.discCover_analytic.comp hE
  have hpa' : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      (RiemannAtlas.ofManifold X) M.halfPlaneCover := by
    rw [RiemannAtlas.ofManifold_toChartedSpace R.toRiemannAtlas]
    exact hpa
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) M.halfPlaneCover :=
    hpa'.contMDiff_ofManifold.mdifferentiable (by simp)
  apply LiZhongQC.s22c6_full_stabilizer_isUniformization M.halfPlaneCover
    M.halfPlaneCover_covering hhol M.halfPlaneCover_surjective
  intro τ₁ τ₂ hτ
  have hτ' : M.discCover (E τ₁) = M.discCover (E τ₂) := hτ
  obtain ⟨F, hFτ, hpF, hFa⟩ := analytic_discCovers_exists_homeomorph R.toRiemannAtlas
    M.discCover M.discCover M.discCover_covering M.discCover_covering
    M.discCover_analytic M.discCover_analytic (E τ₁) (E τ₂) hτ'
  let G : ℍ ≃ₜ ℍ := (E.trans F).trans E.symm
  have hGa : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      (RiemannAtlas.ofManifold ℍ) G := hEinv.comp (hFa.comp hE)
  refine ⟨G, hGa.contMDiff_ofManifold.mdifferentiable (by simp), ?_, ?_⟩
  · funext z
    change M.discCover (E (E.symm (F (E z)))) = M.discCover (E z)
    rw [E.apply_symm_apply]
    exact congrFun hpF (E z)
  · change E.symm (F (E τ₁)) = τ₂
    rw [hFτ, E.symm_apply_apply]

end LowDimensionalTopology.Geometry.Surfaces
