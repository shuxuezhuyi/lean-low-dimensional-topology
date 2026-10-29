module

public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiDifferential
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# The Banach space of continuous Beltrami differentials

Uniform convergence is imposed on all original chart coefficients at once.
The coordinate law cuts out a closed linear subspace of actual bounded
continuous functions on the disjoint union of chart targets. On a compact
surface this is linearly equivalent to the existing continuous tensor model,
and its norm is exactly the intrinsic supremum norm already defined there.

-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ComplexConjugate BoundedContinuousFunction

namespace LowDimensionalTopology.Geometry.Teichmuller.BeltramiDifferential

open Surfaces

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A point in the disjoint union of the actual original chart targets. -/
abbrev AtlasTarget (A : RiemannAtlas X) := Σ e : Chart A, e.val.target

/-- Restrict one continuous function on the atlas disjoint union to each chart. -/
def restrictLinear (A : RiemannAtlas X) :
    (AtlasTarget A →ᵇ ℂ) →ₗ[ℂ] Coefficients A where
  toFun f e := ⟨fun z => f ⟨e, z⟩, f.continuous.comp continuous_sigmaMk⟩
  map_add' f g := by
    funext e
    apply ContinuousMap.ext
    intro z
    rfl
  map_smul' a f := by
    funext e
    apply ContinuousMap.ext
    intro z
    rfl

/-- Bounded continuous coefficient families satisfying the actual tensor law. -/
def boundedSubmodule (A : RiemannAtlas X) :
    Submodule ℂ (AtlasTarget A →ᵇ ℂ) :=
  (coefficientSubmodule A).comap (restrictLinear A)

/-- Uniform limits preserve every coordinate change equation. -/
theorem isClosed_boundedSubmodule (A : RiemannAtlas X) :
    IsClosed (boundedSubmodule A : Set (AtlasTarget A →ᵇ ℂ)) := by
  change IsClosed {μ : AtlasTarget A →ᵇ ℂ |
    ∀ (e f : Chart A) (x : X) (hxe : x ∈ e.val.source) (hxf : x ∈ f.val.source),
      μ ⟨e, ⟨e.val x, e.val.map_source hxe⟩⟩ =
        μ ⟨f, ⟨f.val x, f.val.map_source hxf⟩⟩ *
          conj (deriv (e.val.symm.trans f.val) (e.val x)) /
            deriv (e.val.symm.trans f.val) (e.val x)}
  simp_rw [ofPred_forall]
  refine isClosed_iInter fun e => isClosed_iInter fun f =>
    isClosed_iInter fun x => isClosed_iInter fun hxe => isClosed_iInter fun hxf => ?_
  exact isClosed_eq
    (BoundedContinuousFunction.lipschitz_eval_const _).continuous
    (((BoundedContinuousFunction.lipschitz_eval_const _).continuous.mul_const _).div_const _)

/-- The closed subspace, with its inherited uniform norm and completeness. -/
def boundedClosedSubmodule (A : RiemannAtlas X) :
    ClosedSubmodule ℂ (AtlasTarget A →ᵇ ℂ) :=
  ⟨boundedSubmodule A, isClosed_boundedSubmodule A⟩

/-- Continuous Beltrami differentials with the uniform coefficient norm. -/
abbrev BanachSpace (A : RiemannAtlas X) := ↥(boundedClosedSubmodule A)

/-- Every element of the Banach model is an actual continuous tensor. -/
def toTensor {A : RiemannAtlas X} (μ : BanachSpace A) : BeltramiDifferential A :=
  ⟨restrictLinear A μ.val, μ.property⟩

@[simp]
theorem toTensor_coeff {A : RiemannAtlas X} (μ : BanachSpace A)
    (e : Chart A) (z : e.val.target) : (toTensor μ).coeff e z = μ.val ⟨e, z⟩ := rfl

theorem toTensor_injective {A : RiemannAtlas X} :
    Function.Injective (toTensor (A := A)) := by
  intro μ ν h
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  rintro ⟨e, z⟩
  exact congrArg (fun τ : BeltramiDifferential A => τ.coeff e z) h

section Compact

variable [CompactSpace X] {A : RiemannAtlas X}

/-- Compactness bounds every chart coefficient by the same intrinsic norm. -/
def ofTensor (μ : BeltramiDifferential A) : BanachSpace A :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p : AtlasTarget A => μ.coeff p.1 p.2)
    (continuous_sigma fun e => (μ.coeff e).continuous)
    μ.supNorm (fun p => μ.coeff_norm_le_supNorm p.1 p.2), μ.property⟩

@[simp]
theorem ofTensor_apply (μ : BeltramiDifferential A) (e : Chart A)
    (z : e.val.target) : (ofTensor μ).val ⟨e, z⟩ = μ.coeff e z := rfl

@[simp]
theorem toTensor_ofTensor (μ : BeltramiDifferential A) : (toTensor (ofTensor μ)) = μ := by
  apply ext
  intro e z
  rfl

@[simp]
theorem ofTensor_toTensor (μ : BanachSpace A) : ofTensor (toTensor μ) = μ := by
  apply toTensor_injective
  exact toTensor_ofTensor (toTensor μ)

/-- The Banach presentation changes neither coefficients nor the tensor law. -/
def compactLinearEquiv : BeltramiDifferential A ≃ₗ[ℂ] BanachSpace A where
  toFun := ofTensor
  invFun := toTensor (A := A)
  left_inv := toTensor_ofTensor
  right_inv := ofTensor_toTensor
  map_add' μ ν := by
    apply toTensor_injective
    apply ext
    intro e z
    rfl
  map_smul' a μ := by
    apply toTensor_injective
    apply ext
    intro e z
    rfl

/-- The uniform Banach norm agrees with the original compact-surface sup norm. -/
theorem norm_ofTensor (μ : BeltramiDifferential A) : ‖ofTensor μ‖ = μ.supNorm := by
  apply le_antisymm
  · exact (BoundedContinuousFunction.norm_le μ.supNorm_nonneg).2
      (fun p => μ.coeff_norm_le_supNorm p.1 p.2)
  · apply (ContinuousMap.norm_le μ.abs (norm_nonneg _)).2
    intro x
    obtain ⟨e, he, hx⟩ := A.cover x
    rw [Real.norm_eq_abs, abs_of_nonneg (μ.abs_nonneg x), μ.abs_eq_coeff ⟨e, he⟩ x hx]
    exact (ofTensor μ).val.norm_coe_le_norm
      ⟨⟨e, he⟩, ⟨e x, e.map_source hx⟩⟩

theorem norm_toTensor (μ : BanachSpace A) : (toTensor μ).supNorm = ‖μ‖ := by
  rw [← norm_ofTensor, ofTensor_toTensor]

/-- Strictly subunit coefficients form the genuine open unit ball. -/
theorem norm_lt_one_iff (μ : BanachSpace A) :
    ‖μ‖ < 1 ↔ ∀ (e : Chart A) (z : e.val.target), ‖(toTensor μ).coeff e z‖ < 1 := by
  rw [← norm_toTensor]
  constructor
  · intro h e z
    exact lt_of_le_of_lt ((toTensor μ).coeff_norm_le_supNorm e z) h
  · intro h
    apply (ContinuousMap.norm_lt_iff (toTensor μ).abs (by positivity)).2
    intro x
    obtain ⟨e, he, hx⟩ := A.cover x
    rw [Real.norm_eq_abs, abs_of_nonneg ((toTensor μ).abs_nonneg x),
      (toTensor μ).abs_eq_coeff ⟨e, he⟩ x hx]
    exact h ⟨e, he⟩ ⟨e x, e.map_source hx⟩

end Compact

end LowDimensionalTopology.Geometry.Teichmuller.BeltramiDifferential
