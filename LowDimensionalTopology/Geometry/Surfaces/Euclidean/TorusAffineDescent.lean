module

public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.TorusAffineLift
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Actual affine descent between native complex tori

A nonzero complex scalar carrying the complete original period lattice onto the
other lattice descends to an analytic homeomorphism of the actual torus models.
The argument uses the models' original covering fibres and atlases. It supplies
the geometric converse to `TorusAffineLift`; the normalized SL(2,Z) arithmetic is
separate.
-/

@[expose] public section
noncomputable section

open Set Module

namespace LowDimensionalTopology.Geometry.Surfaces

/-- An actual affine map descends through the two genuine analytic plane covers
when its scalar carries precisely one full period lattice onto the other. -/
theorem ComplexTorusModel.affine_descends_to_analytic_homeomorph
    {b c : Basis (Fin 2) ℝ ℂ} (T : ComplexTorusModel b) (U : ComplexTorusModel c)
    (a d : ℂ) (ha : a ≠ 0)
    (hΛ : ∀ v : ℂ, v ∈ Submodule.span ℤ (Set.range b) ↔
      a * v ∈ Submodule.span ℤ (Set.range c)) :
    ∃ f : ComplexTorusCarrier ≃ₜ ComplexTorusCarrier,
      RiemannAnalyticMap T.surface.toRiemannAtlas U.surface.toRiemannAtlas f ∧
      RiemannAnalyticMap U.surface.toRiemannAtlas T.surface.toRiemannAtlas f.symm ∧
      ∀ z : ℂ, f (T.projection z) = U.projection (a * z + d) := by
  classical
  let F : ℂ → ℂ := fun z => a * z + d
  have hFsurj : Function.Surjective F := by
    intro w
    refine ⟨(w - d) / a, ?_⟩
    dsimp only [F]
    field_simp [ha]
    ring
  have hFc : Continuous F := (continuous_const.mul continuous_id).add continuous_const
  have hFa : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas
      complexPlaneRiemannSurface.toRiemannAtlas F :=
    (complexPlaneRiemannSurface_analytic_iff F).mpr (by
      intro z _hz
      exact (analyticAt_const.mul analyticAt_id).add analyticAt_const)
  have hfiber (z w : ℂ) : T.projection z = T.projection w ↔
      U.projection (F z) = U.projection (F w) := by
    rw [T.fiber_iff, U.fiber_iff]
    have hsub : F z - F w = a * (z - w) := by dsimp only [F]; ring
    rw [hsub]
    exact hΛ (z - w)
  let f : ComplexTorusCarrier → ComplexTorusCarrier := fun x =>
    U.projection (F (Function.surjInv T.surjective x))
  have hcomm (z : ℂ) : f (T.projection z) = U.projection (F z) := by
    exact (hfiber _ _).mp (Function.surjInv_eq T.surjective (T.projection z))
  have hcomp : f ∘ T.projection = U.projection ∘ F := funext hcomm
  have hfc : Continuous f := by
    apply (T.covering.isQuotientMap T.surjective).continuous_iff.mpr
    rw [hcomp]
    exact U.covering.continuous.comp hFc
  have hfa : RiemannAnalyticMap T.surface.toRiemannAtlas U.surface.toRiemannAtlas f := by
    apply RiemannAnalyticMap.of_comp_surjective_localHomeomorph T.analytic_projection
      T.covering.isLocalHomeomorph T.surjective hfc
    rw [hcomp]
    exact U.analytic_projection.comp hFa
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      obtain ⟨z, rfl⟩ := T.surjective x
      obtain ⟨w, rfl⟩ := T.surjective y
      apply (hfiber z w).mpr
      simpa only [hcomm] using hxy
    · intro y
      obtain ⟨w, rfl⟩ := U.surjective y
      obtain ⟨z, rfl⟩ := hFsurj w
      exact ⟨T.projection z, hcomm z⟩
  refine ⟨hfa.toHomeomorph hbij, hfa, hfa.inverse_analytic hbij, ?_⟩
  exact hcomm

/-- For arbitrary actual native models, conformal equivalence is exactly
nonzero complex scaling equivalence of their complete original period lattices.
This is the geometric criterion; it does not assert a canonical marking. -/
theorem ComplexTorusModel.conformallyEquivalent_iff_scales_period_lattice
    {b c : Basis (Fin 2) ℝ ℂ} (T : ComplexTorusModel b) (U : ComplexTorusModel c) :
    RiemannConformallyEquivalent T.surface U.surface ↔
      ∃ a : ℂ, a ≠ 0 ∧ ∀ v : ℂ,
        v ∈ Submodule.span ℤ (Set.range b) ↔
          a * v ∈ Submodule.span ℤ (Set.range c) := by
  constructor
  · rintro ⟨f, hf, hbij⟩
    exact T.analytic_homeomorph_scales_period_lattice U (hf.toHomeomorph hbij) hf
  · rintro ⟨a, ha, hΛ⟩
    obtain ⟨f, hf, _hfi, _hcomm⟩ :=
      T.affine_descends_to_analytic_homeomorph U a 0 ha hΛ
    exact ⟨f, hf, f.bijective⟩

end LowDimensionalTopology.Geometry.Surfaces
