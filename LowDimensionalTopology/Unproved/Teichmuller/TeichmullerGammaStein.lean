module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeAhlforsWeillNeighborhood
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Cartan's Stein conditions on the original group Teichmuller space

The compact holomorphic hull, point separation and global holomorphic local
coordinates use the original group quotient with its actual QC metric and Bers
atlas. Countable compact exhaustion is retained explicitly as well.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller

open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller
open LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

/-- The full Stein assertion for the same original complex Teichmuller space.
This is an explicit unproved statement, with all three Cartan conditions. -/
def TeichmullerGammaStein
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
  letI := gammaBers_isManifold R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let I := 𝓘(ℂ, Fin (3 * g - 3) → ℂ)
  SigmaCompactSpace (LiZhongQC.TeichGamma Γ) ∧
  (∀ K : Set (LiZhongQC.TeichGamma Γ), IsCompact K →
    IsCompact {a | ∀ f : LiZhongQC.TeichGamma Γ → ℂ,
      ContMDiff I 𝓘(ℂ) ω f → (∀ b ∈ K, ‖f b‖ ≤ 1) → ‖f a‖ ≤ 1}) ∧
  (∀ a b : LiZhongQC.TeichGamma Γ, a ≠ b →
    ∃ f : LiZhongQC.TeichGamma Γ → ℂ, ContMDiff I 𝓘(ℂ) ω f ∧ f a ≠ f b) ∧
  (∀ a : LiZhongQC.TeichGamma Γ,
    ∃ F : LiZhongQC.TeichGamma Γ → Fin (3 * g - 3) → ℂ,
      ContMDiff I I ω F ∧ Function.Bijective (mfderiv I I F a))

end LowDimensionalTopology.Unproved.Teichmuller
