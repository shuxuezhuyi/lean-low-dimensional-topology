module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizerModularIsometry
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Royden's characterization of the original modular action

The acting group is the full original quasiconformal normalizer quotient.
The statement retains every biholomorphic permutation of the original group
Teichmuller space, higher-genus faithfulness and the exact genus-two kernel.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller

open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller
open LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

/-- The full natural modular action exhausts the biholomorphic automorphisms,
is faithful for genus greater than two, and has the cyclic order-two kernel
in genus two. This is an explicit unproved classical statement. -/
def RoydenModularAutomorphisms
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  letI := R.t2Space
  letI := R.connectedSpace
  letI := R.compactSpace
  letI := gammaQCMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  letI := gammaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let representation := upperModularRepresentation R hg hgenus hΓ hp
  (∀ f : Equiv.Perm (LiZhongQC.TeichGamma Γ),
    (ContMDiff 𝓘(ℂ, Fin (3 * g - 3) → ℂ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ) ω f ∧
      ContMDiff 𝓘(ℂ, Fin (3 * g - 3) → ℂ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ) ω f.symm) →
    ∃ γ : QCNormalizerModular.ModularGroup hp, representation γ = f) ∧
  (2 < g → Function.Injective representation) ∧
  (g = 2 → Nonempty (representation.ker ≃* Multiplicative (ZMod 2)))

end LowDimensionalTopology.Unproved.Teichmuller
