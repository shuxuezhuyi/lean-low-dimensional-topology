module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeComplexMinimizers

/-!
# The four displacement types of the original modular action

The full-log displacement is computed on the original QC-marked quotient.
Parabolic and pseudo-hyperbolic types are the two cases where the genuine
infimum has no minimizing point. The four cases are exhaustive and disjoint.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Surfaces LiZhongQC
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

local notation "ModularR" =>
  @SourceQCModular.ModularGroup X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold

/-- Zero actual infimal displacement, with no point attaining it. -/
def IsParabolic (γ : ModularR) : Prop :=
  infimalDisplacement R γ = 0 ∧ ¬ ∃ p, IsMinimizingPoint R γ p

/-- Strictly positive actual infimal displacement, with no point attaining it. -/
def IsPseudoHyperbolic (γ : ModularR) : Prop :=
  0 < infimalDisplacement R γ ∧ ¬ ∃ p, IsMinimizingPoint R γ p

/-- The genuine infimum over every original marked point is nonnegative. -/
theorem infimalDisplacement_nonneg (γ : ModularR) :
    0 ≤ infimalDisplacement R γ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  apply Real.sInf_nonneg
  rintro _ ⟨p, rfl⟩
  rw [displacement, QCBookMetric.bookDistance_eq_two_mul]
  exact mul_nonneg (by norm_num) (s29_m_teichDistance_nonneg _ _)

/-- Every actual modular class has one of the four source displacement types. -/
theorem modular_displacement_type_cases (γ : ModularR) :
    IsElliptic R γ ∨ IsParabolic R γ ∨ IsHyperbolic R γ ∨ IsPseudoHyperbolic R γ := by
  classical
  by_cases hz : infimalDisplacement R γ = 0
  · by_cases hm : ∃ p, IsMinimizingPoint R γ p
    · exact Or.inl ⟨hz, hm⟩
    · exact Or.inr (Or.inl ⟨hz, hm⟩)
  · have hp : 0 < infimalDisplacement R γ :=
      lt_of_le_of_ne (infimalDisplacement_nonneg R γ) (Ne.symm hz)
    by_cases hm : ∃ p, IsMinimizingPoint R γ p
    · exact Or.inr (Or.inr (Or.inl ⟨hp, hm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hp, hm⟩))

/-- No actual modular class belongs to two distinct displacement types. -/
theorem modular_displacement_types_pairwise_disjoint (γ : ModularR) :
    ¬ (IsElliptic R γ ∧ IsParabolic R γ) ∧
    ¬ (IsElliptic R γ ∧ IsHyperbolic R γ) ∧
    ¬ (IsElliptic R γ ∧ IsPseudoHyperbolic R γ) ∧
    ¬ (IsParabolic R γ ∧ IsHyperbolic R γ) ∧
    ¬ (IsParabolic R γ ∧ IsPseudoHyperbolic R γ) ∧
    ¬ (IsHyperbolic R γ ∧ IsPseudoHyperbolic R γ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨he, hp⟩
    exact hp.2 he.2
  · rintro ⟨he, hh⟩
    exact (ne_of_gt hh.1) he.1
  · rintro ⟨he, hs⟩
    exact (ne_of_gt hs.1) he.1
  · rintro ⟨hp, hh⟩
    exact hp.2 hh.2
  · rintro ⟨hp, hs⟩
    exact (ne_of_gt hs.1) hp.1
  · rintro ⟨hh, hs⟩
    exact hs.2 hh.2

/-- Failure to attain the actual infimum is exactly one of the two remaining types. -/
theorem no_minimizingPoint_iff_parabolic_or_pseudoHyperbolic (γ : ModularR) :
    (¬ ∃ p, IsMinimizingPoint R γ p) ↔ IsParabolic R γ ∨ IsPseudoHyperbolic R γ := by
  classical
  constructor
  · intro hm
    by_cases hz : infimalDisplacement R γ = 0
    · exact Or.inl ⟨hz, hm⟩
    · exact Or.inr
        ⟨lt_of_le_of_ne (infimalDisplacement_nonneg R γ) (Ne.symm hz), hm⟩
  · intro h
    exact h.elim And.right And.right

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
