/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ConformalTypes
public import LowDimensionalTopology.External.LiZhongQC.Ch03.S15_Distortion
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S22_RiemannSurfaces
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Normalized quasiconformal maps of the canonical Fuchsian model

The maps are actual plane homeomorphisms with their actual sphere extensions.
They retain the canonical reflected half-plane convention, three-point
normalization, and equality of the entire conjugated projective sphere group
with an actual real Fuchsian group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped MatrixGroups OnePoint ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open Hyperbolic Mobius

/-- Canonical normalized QC maps of the Fuchsian model, with the same global
sphere conjugation and the reflected half-plane convention. -/
def normalizedQCFuchsianMaps (Γ : Subgroup SL(2, ℝ)) : Set (ℂ ≃ₜ ℂ) :=
  {w | (∃ K : ℝ, LiZhongQC.IsKQCNormalizedPlane w K) ∧
    (∀ z : ℂ, w (conj z) = conj (w z)) ∧
    w '' LiZhongQC.upperHalf = LiZhongQC.upperHalf ∧
    ∃ Δ : Subgroup SL(2, ℝ), LiZhongQC.IsFuchsian Δ ∧
      ((Γ.map realSLMobius).map complexMobiusGroup.subtype).map
          (MulAut.conj w.onePointCongr.toEquiv).toMonoidHom =
        (Δ.map realSLMobius).map complexMobiusGroup.subtype}

/-- The actual sphere extension fixes all three normalization points. -/
theorem normalizedQCFuchsianMaps_sphere_normalization
    {Γ : Subgroup SL(2, ℝ)} {w : ℂ ≃ₜ ℂ} (hw : w ∈ normalizedQCFuchsianMaps Γ) :
    w.onePointCongr (∞ : ExtendedComplex) = ∞ ∧
      w.onePointCongr ((0 : ℂ) : ExtendedComplex) = ((0 : ℂ) : ExtendedComplex) ∧
      w.onePointCongr ((1 : ℂ) : ExtendedComplex) = ((1 : ℂ) : ExtendedComplex) := by
  obtain ⟨K, hK⟩ := hw.1
  refine ⟨rfl, ?_, ?_⟩
  · change ((w (0 : ℂ) : ℂ) : ExtendedComplex) = ((0 : ℂ) : ExtendedComplex)
    exact congrArg (fun z : ℂ => (z : ExtendedComplex)) hK.2.2.1
  · change ((w (1 : ℂ) : ℂ) : ExtendedComplex) = ((1 : ℂ) : ExtendedComplex)
    exact congrArg (fun z : ℂ => (z : ExtendedComplex)) hK.2.2.2

/-- Every genuine Fuchsian group admits the original identity map in this family. -/
theorem homeomorph_refl_mem_normalizedQCFuchsianMaps
    (Γ : Subgroup SL(2, ℝ)) (hΓ : LiZhongQC.IsFuchsian Γ) :
    Homeomorph.refl ℂ ∈ normalizedQCFuchsianMaps Γ := by
  have hnorm : LiZhongQC.IsKQCNormalizedPlane (Homeomorph.refl ℂ) 1 := by
    refine ⟨LiZhongQC.isKQC_one_of_conformal isOpen_univ
      (LiZhongQC.isConformalOnto_id univ), ?_, rfl, rfl⟩
    exact Set.image_id _
  refine ⟨⟨1, hnorm⟩, (fun _ => rfl), ?_, Γ, hΓ, ?_⟩
  · exact Set.image_id _
  · have hrefl : (Homeomorph.refl ℂ).onePointCongr.toEquiv =
        (1 : Equiv.Perm ExtendedComplex) := by
      apply Equiv.ext
      intro z
      cases z using OnePoint.rec <;> rfl
    rw [hrefl, map_one]
    exact Subgroup.map_id _

end LowDimensionalTopology.Geometry.Teichmuller
