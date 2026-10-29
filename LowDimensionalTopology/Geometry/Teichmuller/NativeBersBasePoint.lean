module

public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBersCoordinates

/-!
# The identity marking is the actual Bers base point

The chosen marked-surface/group equivalence comes with a normalized-lift
characterization. The identity covering lift and identity boundary map satisfy
that characterization for the original identity marking and zero coefficient.
Consequently the actual native base point maps to the group origin and to zero
in the existing Bers coordinates. No arbitrary reference point is substituted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces

private def referenceZeroCoefficient
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : LiZhongQC.BeltramiGamma Γ :=
  ⟨⟨0, ⟨0, le_refl 0, zero_lt_one, MeasureTheory.aestronglyMeasurable_const, by simp⟩,
    fun _ _ => rfl⟩, fun _ _ => Filter.Eventually.of_forall fun _ => by simp⟩

private theorem symmetricSolution_zero : LiZhongQC.fMuSym (0 : ℂ → ℂ) = id := by
  have he : LiZhongQC.symmetricExtension (0 : ℂ → ℂ) = 0 := by
    funext z
    simp only [LiZhongQC.symmetricExtension, Pi.zero_apply, map_zero, ite_self]
  rw [LiZhongQC.fMuSym, he, LiZhongQC.bB_l_normalizedSolution_zero]

/-- The raw Bers value of the actual zero-coefficient group class is zero. -/
theorem sourceBersMap_origin
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    LiZhongQC.bersMapGamma Γ (LiZhongQC.TeichGamma.origin Γ) = 0 := by
  rw [LiZhongQC.bg_bersMapGamma_eq
    (μ := referenceZeroCoefficient Γ)
    (show Quotient.mk _ (referenceZeroCoefficient Γ) = LiZhongQC.TeichGamma.origin Γ
      from rfl)]
  funext z
  change LiZhongQC.lowerHalf.indicator
    (LiZhongQC.schwarzian (LiZhongQC.normalizedSolution (0 : ℂ → ℂ))) z = 0
  rw [LiZhongQC.bB_l_normalizedSolution_zero]
  by_cases hz : z ∈ LiZhongQC.lowerHalf
  · rw [indicator_of_mem hz, LiZhongQC.bB_l_schwarzian_id]
  · rw [indicator_of_notMem hz]

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Forgetting smoothness preserves the original identity-marked representative. -/
theorem toSource_basePoint :
    toSource R (basePoint R) =
      (letI := R.toRiemannAtlas.toChartedSpace;
        Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X))
          ((MarkedRiemannSurface.refl R).toSource)) := rfl

variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

private theorem identityMarking_normalizedLift (p : UpperHalfPlane → X) :
    letI := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsNormalizedLift p p (MarkedRiemannSurface.refl R).toSource.marking
      (Homeomorph.refl UpperHalfPlane) (id : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane) := by
  let := R.toRiemannAtlas.toChartedSpace
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro z
    rfl
  · refine ⟨?_, continuousOn_id, injOn_id _, image_id _⟩
    intro z hz
    congr 1
    change ((z : ℂ) : LiZhongQC.ExtPlane) =
      ((LiZhongQC.liftToC (Homeomorph.refl UpperHalfPlane) z : ℂ) : LiZhongQC.ExtPlane)
    unfold LiZhongQC.liftToC
    simp only [dite_eq_left (show 0 < z.im from hz), Homeomorph.refl_apply, id_eq]

/-- The chosen normalized-lift equivalence sends the actual group origin to
the original identity-marked native class. -/
theorem sourceGammaEquiv_origin :
    sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp
      (LiZhongQC.TeichGamma.origin Γ) = toSource R (basePoint R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let m : LiZhongQC.MarkedRS X := (MarkedRiemannSurface.refl R).toSource
  have hspec := Classical.choose_spec (LiZhongQC.teichGamma_equiv_teichSpace hg
    (R.sourceHasGenus hgenus hPresentation) hΓ hfree hp)
  have he := (hspec (referenceZeroCoefficient Γ) m).mpr
    ⟨Γ, p, Homeomorph.refl UpperHalfPlane, id, hp,
      identityMarking_normalizedLift R p, fun x => by
        change ((x : ℂ) : LiZhongQC.ExtPlane) =
          ((LiZhongQC.fMuSym (0 : ℂ → ℂ) x : ℂ) : LiZhongQC.ExtPlane)
        rw [symmetricSolution_zero]; rfl⟩
  change sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp
    (LiZhongQC.TeichGamma.origin Γ) = Quot.mk _ m at he
  exact he

/-- The actual identity-marked native base point is exactly the zero-coefficient
class for the same uniformizing group and the same chosen equivalence. -/
theorem gammaEquiv_basePoint :
    gammaEquiv R hg hgenus hPresentation hΓ hfree hp (basePoint R) =
      LiZhongQC.TeichGamma.origin Γ := by
  apply (sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp).injective
  change (sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp)
    ((sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp).symm
      (sourceEquiv R hg hgenus hPresentation (basePoint R))) = _
  rw [Equiv.apply_symm_apply, sourceGammaEquiv_origin]; rfl

/-- The existing Bers coordinate function is based at zero on the actual
original identity-marked class, rather than on a separately chosen fibre. -/
theorem bersCoordinates_basePoint :
    bersCoordinates R hg hgenus hPresentation hΓ hfree hp (basePoint R) = 0 := by
  let φ : LiZhongQC.automorphicQD Γ :=
    ⟨LiZhongQC.bersMapGamma Γ
        (gammaEquiv R hg hgenus hPresentation hΓ hfree hp (basePoint R)),
      (LiZhongQC.bersMapGamma_mem hΓ _).1⟩
  have hφ : φ = 0 := by
    apply Subtype.ext
    change LiZhongQC.bersMapGamma Γ
      (gammaEquiv R hg hgenus hPresentation hΓ hfree hp (basePoint R)) = 0
    rw [gammaEquiv_basePoint, sourceBersMap_origin]
  change linearBersCoordinates R hg hgenus hPresentation hΓ hp φ = 0
  rw [hφ, map_zero]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
