module

public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.ElementaryPacking
public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.NormalizedTorusClassification
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed

/-!
# Actual lattice tori and normalized models

The integer span of any real basis of the complex plane determines a discrete
subgroup of actual translations. Its plane quotient supplies a genuine complex
torus with its analytic covering map. In particular, every parameter in the
upper half-plane determines a closed Riemann surface of topological genus one.
-/

@[expose] public section
noncomputable section

open Module
open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Mobius

/-- Actual translations by the integer period lattice of a real basis. -/
def complexLatticeTranslationGroup (b : Basis (Fin 2) ℝ ℂ) :
    Subgroup complexMobiusGroup where
  carrier := {g | ∃ v ∈ Submodule.span ℤ (Set.range b), g = mobiusTranslation v}
  one_mem' := ⟨0, Submodule.zero_mem _,
    ((mobiusTranslation_eq_one_iff 0).mpr rfl).symm⟩
  mul_mem' := by
    rintro f g ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, Submodule.add_mem _ hv hw, (mobiusTranslation_add v w).symm⟩
  inv_mem' := by
    rintro f ⟨v, hv, rfl⟩
    exact ⟨-v, Submodule.neg_mem _ hv, (mobiusTranslation_neg v).symm⟩

theorem complexLatticeTranslationGroup_translations (b : Basis (Fin 2) ℝ ℂ) :
    ∀ g ∈ complexLatticeTranslationGroup b, ∃ v : ℂ, g = mobiusTranslation v := by
  rintro g ⟨v, _hv, hgv⟩
  exact ⟨v, hgv⟩

/-- The geometric displacement subgroup is exactly the specified period lattice. -/
theorem complexLatticeTranslationGroup_displacements (b : Basis (Fin 2) ℝ ℂ) :
    translationDisplacements (complexLatticeTranslationGroup b) =
      (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
  ext v
  constructor
  · rintro ⟨w, hw, hvw⟩
    exact (mobiusTranslation_injective hvw).symm ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- Discreteness uses the original subspace topology of the actual Möbius group. -/
theorem complexLatticeTranslationGroup_discrete (b : Basis (Fin 2) ℝ ℂ) :
    IsDiscreteMobiusSubgroup (complexLatticeTranslationGroup b) := by
  let : DiscreteTopology (translationDisplacements (complexLatticeTranslationGroup b)) := by
    rw [complexLatticeTranslationGroup_displacements]
    infer_instance
  exact (translationDisplacementHomeomorph (complexLatticeTranslationGroup b)
    (complexLatticeTranslationGroup_translations b)).discreteTopology

theorem complexLatticeTranslationGroup_fixes_infty (b : Basis (Fin 2) ℝ ℂ) :
    complexLatticeTranslationGroup b ≤ mobiusInftyStabilizer := by
  rintro g ⟨v, _hv, rfl⟩
  exact mobiusTranslation_infty v

/-- The actual action is discontinuous on the whole finite complex plane. -/
theorem complexLatticeTranslationGroup_discontinuous (b : Basis (Fin 2) ℝ ℂ) :
    IsMobiusDiscontinuousOn (complexLatticeTranslationGroup b)
      (translationPlaneDomain (complexLatticeTranslationGroup b)
        (complexLatticeTranslationGroup_translations b)).carrier := by
  apply discrete_affine_unit_discontinuous (complexLatticeTranslationGroup b)
    (complexLatticeTranslationGroup_discrete b)
    (complexLatticeTranslationGroup_fixes_infty b)
  intro g
  have hm : mobiusMultiplier
      ⟨g.val, complexLatticeTranslationGroup_fixes_infty b g.property⟩ = 1 :=
    (mobiusMultiplier_eq_one_iff_translation _).mpr
      (complexLatticeTranslationGroup_translations b g.val g.property)
  rw [hm]
  exact norm_one

/-- Nonidentity translations are parabolic, so no elliptic isotropy enters the quotient. -/
theorem complexLatticeTranslationGroup_no_elliptic (b : Basis (Fin 2) ℝ ℂ) :
    ∀ g ∈ complexLatticeTranslationGroup b, g ≠ 1 → ¬MobiusElliptic g := by
  rintro g ⟨v, _hv, rfl⟩ hne he
  exact he.not_parabolic ((mobiusTranslation_parabolic_iff v).mpr
    ((mobiusTranslation_eq_one_iff v).not.mp hne))

/-- The complex torus associated to an arbitrary full real basis, with its genuine
analytic plane cover and exact original lattice fibres. -/
def complexLatticeTorusModel (b : Basis (Fin 2) ℝ ℂ) : ComplexTorusModel b :=
  translationComplexTorusModel (complexLatticeTranslationGroup b)
    (complexLatticeTranslationGroup_translations b)
    (complexLatticeTranslationGroup_discontinuous b)
    (complexLatticeTranslationGroup_no_elliptic b) b
    (complexLatticeTranslationGroup_displacements b)

/-- Every genuine complex torus model carries its original compact complex atlas. -/
def ComplexTorusModel.closedRiemannSurface {b : Basis (Fin 2) ℝ ℂ}
    (T : ComplexTorusModel b) : ClosedRiemannSurface ComplexTorusCarrier :=
  ClosedRiemannSurface.ofRiemannSurface T.surface

@[simp]
theorem ComplexTorusModel.closedRiemannSurface_toRiemannSurface
    {b : Basis (Fin 2) ℝ ℂ} (T : ComplexTorusModel b) :
    T.closedRiemannSurface.toRiemannSurface = T.surface := rfl

/-- This genus witness identifies the actual torus with the one-handle surface. -/
theorem ComplexTorusModel.closedRiemannSurface_hasGenus
    {b : Basis (Fin 2) ℝ ℂ} (T : ComplexTorusModel b) :
    T.closedRiemannSurface.HasGenus 1 :=
  ⟨canonicalHandleSurfaceOneHomeomorph.symm⟩

/-- The actual normalized torus exists for every upper-half-plane parameter. -/
def normalizedTorusModel (τ : UpperHalfPlane) :
    ComplexTorusModel (normalizedTorusBasis τ) :=
  complexLatticeTorusModel (normalizedTorusBasis τ)

/-- The normalized closed Riemann surface with periods generated by `1` and `τ`. -/
def normalizedClosedTorus (τ : UpperHalfPlane) : ClosedRiemannSurface ComplexTorusCarrier :=
  (normalizedTorusModel τ).closedRiemannSurface

theorem normalizedClosedTorus_hasGenus (τ : UpperHalfPlane) :
    (normalizedClosedTorus τ).HasGenus 1 :=
  (normalizedTorusModel τ).closedRiemannSurface_hasGenus

/-- The chosen analytic covering has precisely the normalized integer periods. -/
theorem normalizedTorusModel_fiber_iff (τ : UpperHalfPlane) (z w : ℂ) :
    (normalizedTorusModel τ).projection z = (normalizedTorusModel τ).projection w ↔
      z - w ∈ Submodule.span ℤ ({(1 : ℂ), (τ : ℂ)} : Set ℂ) := by
  rw [(normalizedTorusModel τ).fiber_iff, normalizedTorusBasis_span]

/-- Classification now applies to actual chosen models for every pair of parameters. -/
theorem normalizedClosedTorus_conformallyEquivalent_iff_modular (τ σ : UpperHalfPlane) :
    RiemannConformallyEquivalent (normalizedClosedTorus τ).toRiemannSurface
      (normalizedClosedTorus σ).toRiemannSurface ↔
        ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℤ, M • τ = σ :=
  ComplexTorusModel.normalized_conformallyEquivalent_iff_modular
    τ σ (normalizedTorusModel τ) (normalizedTorusModel σ)

end LowDimensionalTopology.Geometry.Surfaces
