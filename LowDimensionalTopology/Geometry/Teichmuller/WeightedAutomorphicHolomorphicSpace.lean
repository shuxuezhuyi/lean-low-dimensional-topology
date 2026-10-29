module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicBergmanProjection
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicDecomposition

/-!
# The original holomorphic quadratic space in the weighted essential norm

Its vectors are the weighted lifts of all original quadratic differentials.
The norm is inherited from the actual coefficient space, not the Petersson norm.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicCoefficient

open Surfaces GammaMeasurableBeltrami
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

/-- Two conjugate-linear maps give the weighted lift of every original vector. -/
def quadraticLift : HolomorphicQuadraticDifferential R.toRiemannAtlas →ₗ[ℂ] Space Γ where
  toFun q := (beltramiEquiv Γ).symm (NativeHarmonicBeltrami.ofQuadratic R p hp q)
  map_add' q r := by rw [NativeHarmonicBeltrami.ofQuadratic_add, map_add]
  map_smul' a q := by
    rw [NativeHarmonicBeltrami.ofQuadratic_smul, LinearIsometryEquiv.map_smulₛₗ]
    change conj (conj a) • _ = a • _
    rw [Complex.conj_conj]

/-- The actual class retains the literal unconjugated square-height coefficient. -/
theorem quadraticLift_coe_ae (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    (quadraticLift R p hp q).val =ᵐ[volume]
      fun z : ℍ => (z.im : ℂ) ^ 2 * WeilPetersson.liftQuadratic R.toRiemannAtlas p q z := by
  filter_upwards [Lp.coeFn_star (NativeHarmonicBeltrami.ofQuadratic R p hp q).val,
    NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp q] with z hs hq
  change (star (NativeHarmonicBeltrami.ofQuadratic R p hp q).val : Ambient) z = _
  rw [hs]
  change conj ((NativeHarmonicBeltrami.ofQuadratic R p hp q).val z) = _
  rw [hq]
  change conj ((z.im : ℂ) ^ 2 * conj (WeilPetersson.liftQuadratic R.toRiemannAtlas p q z)) = _
  rw [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj]

theorem quadraticLift_coe_ae_flat (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    (quadraticLift R p hp q).val =ᵐ[flatMeasure]
      fun z : ℍ => (z.im : ℂ) ^ 2 * WeilPetersson.liftQuadratic R.toRiemannAtlas p q z :=
  ae_hyperbolic_iff.mp (quadraticLift_coe_ae R p hp q)

/-- The book's holomorphic space, with the inherited weighted essential norm. -/
def holomorphicSubmodule : Submodule ℂ (Space Γ) := (quadraticLift R p hp).range

abbrev Holomorphic := ↥(holomorphicSubmodule R p hp)

theorem mem_holomorphicSubmodule_iff_exists_quadratic (g : Space Γ) :
    g ∈ holomorphicSubmodule R p hp ↔
      ∃ q : HolomorphicQuadraticDifferential R.toRiemannAtlas, quadraticLift R p hp q = g :=
  Iff.rfl

/-- Every original holomorphic automorphic coefficient descends on the same surface. -/
theorem exists_quadraticLift_of_automorphic {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ LiZhongQC.upperHalf)
    (ha : ∀ γ ∈ Γ, ∀ z ∈ LiZhongQC.upperHalf,
      φ (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) /
        ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z) :
    ∃ q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
      quadraticLift R p hp q ∈ holomorphicSubmodule R p hp ∧
      (∀ z : ℍ, WeilPetersson.liftQuadratic R.toRiemannAtlas p q z = φ z) ∧
      (quadraticLift R p hp q).val =ᵐ[volume] fun z : ℍ => (z.im : ℂ) ^ 2 * φ z := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨q, hq, he⟩ := LiZhongQC.utm_x_descent hp hφ ha
  have hqz (z : ℍ) : WeilPetersson.liftQuadratic R.toRiemannAtlas p ⟨q, hq⟩ z = φ z :=
    he (z : ℂ) z.im_pos
  refine ⟨⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩, hqz, ?_⟩
  filter_upwards [quadraticLift_coe_ae R p hp ⟨q, hq⟩] with z hz
  exact hz.trans (congrArg (fun w : ℂ => (z.im : ℂ) ^ 2 * w) (hqz z))

/-- The actual image is exactly the fixed space of the literal Bergman projection. -/
theorem mem_holomorphicSubmodule_iff_fixed (g : Space Γ) :
    g ∈ holomorphicSubmodule R p hp ↔ bergmanProjection R P p hp F hF g = g := by
  change (∃ q, quadraticLift R p hp q = g) ↔ _
  constructor
  · rintro ⟨q, rfl⟩
    rw [bergmanProjection_apply]
    change (beltramiEquiv Γ).symm (NativePetersson.harmonicProjection R P p hp F hF
      ((beltramiEquiv Γ) ((beltramiEquiv Γ).symm
        (NativeHarmonicBeltrami.ofQuadratic R p hp q)))) = _
    rw [LinearIsometryEquiv.apply_symm_apply,
      NativePetersson.harmonicProjection_fixes_ofQuadratic]
    rfl
  · intro hg
    have hh : NativePetersson.harmonicProjection R P p hp F hF
        ((beltramiEquiv Γ) g) = (beltramiEquiv Γ) g := by
      have he := congrArg (beltramiEquiv Γ) hg
      simpa only [bergmanProjection_apply, LinearIsometryEquiv.apply_symm_apply] using he
    obtain ⟨q, hq⟩ :=
      (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic R P p hp F hF _).mp
        ((NativePetersson.mem_harmonicSubmodule_iff R P p hp F hF _).mpr hh)
    refine ⟨q, ?_⟩
    change (beltramiEquiv Γ).symm (NativeHarmonicBeltrami.ofQuadratic R p hp q) = g
    rw [hq, LinearIsometryEquiv.symm_apply_apply]

theorem range_bergmanProjection :
    (bergmanProjection R P p hp F hF).toLinearMap.range = holomorphicSubmodule R p hp := by
  ext g
  constructor
  · rintro ⟨f, rfl⟩
    exact (mem_holomorphicSubmodule_iff_fixed R P p hp F hF _).mpr
      (bergmanProjection_idempotent R P p hp F hF f)
  · intro hg
    exact ⟨g, (mem_holomorphicSubmodule_iff_fixed R P p hp F hF g).mp hg⟩

include P hF in
theorem holomorphicSubmodule_isClosed :
    IsClosed (holomorphicSubmodule R p hp : Set (Space Γ)) := by
  have he : (holomorphicSubmodule R p hp : Set (Space Γ)) =
      {g | bergmanProjection R P p hp F hF g = g} :=
    Set.ext (mem_holomorphicSubmodule_iff_fixed R P p hp F hF)
  rw [he]
  exact isClosed_eq (bergmanProjection R P p hp F hF).continuous continuous_id

include P hF in
/-- Completeness uses precisely the inherited original weighted essential norm. -/
theorem holomorphic_completeSpace : CompleteSpace (Holomorphic R p hp) :=
  (holomorphicSubmodule_isClosed R P p hp F hF).isComplete.completeSpace_coe

end LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicCoefficient
