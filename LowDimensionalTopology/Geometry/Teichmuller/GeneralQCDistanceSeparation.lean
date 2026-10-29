/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCSmallComparisons
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedLiftComposition
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedMarkingActions

/-!
# Separation for the original full-log QC distance

The reference has the actual uniformization and fixed-triple coordinate
convention of the book's noncommutative Fuchsian setting. Zero distance gives
internally chosen small comparisons. Their normalized lifts tend to the
identity, so the actual marking actions coincide by passage to the limit.
The original normalized-action criterion then gives equality of the original
marked classes. No compactness, genus or extremal representative is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u

/-- Zero full-log distance separates the original common-universe marked
classes in the original book uniformization coordinates. -/
theorem mk_eq_of_distance_zero
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (m n : Marked.{u, u} R) (hzero : distance (mk m) (mk n) = 0) : mk m = mk n := by
  let F₁ := canonicalMarkingLift R hp m
  let F₂ := canonicalMarkingLift R hp n
  have h₁ := canonicalMarkingLift_spec R hp m
  have h₂ := canonicalMarkingLift_spec R hp n
  obtain ⟨f, hf, hlim⟩ := exists_small_comparisons_of_distance_zero m n h₁.2.1 hzero
  let H : ℕ → (ℍ ≃ₜ ℍ) := fun j =>
    Classical.choose (s27u_uniformization_transport h₁.2.1 (f j) (hf j).1)
  have hH (j : ℕ) :=
    Classical.choose_spec (s27u_uniformization_transport h₁.2.1 (f j) (hf j).1)
  let moved (j : ℕ) : Marked.{u, u} R :=
    { target := n.target
      marking := m.marking.trans (f j)
      qc := s28q_isQCRS_trans m.qc (hf j).1 }
  have hmoved (j : ℕ) : (moved j).Equivalent n := by
    refine ⟨Homeomorph.refl _, isBiholomorphic_id, ?_⟩
    change ContinuousMap.Homotopic
      ((m.marking.trans (f j) : R.carrier ≃ₜ n.target.carrier) :
        C(R.carrier, n.target.carrier))
      (n.marking : C(R.carrier, n.target.carrier))
    exact (hf j).2.1
  have hactions (j : ℕ) : ∀ γ ∈ Γ, ∀ τ : ℍ,
      (F₁.trans (H j)) (γ • (F₁.trans (H j)).symm τ) =
        F₂ (γ • F₂.symm τ) := by
    exact (marked_equivalent_iff_normalized_lift_actions R hp hfixed (moved j) n
      (hH j).2.1 h₂.2.1
      (normalizedLift_comp h₁.2.2 (hH j).2.2.1) h₂.2.2).mp (hmoved j)
  have hconj (j : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hγ : γ ∈ Γ) (τ : ℍ) :
      H j (F₁ (γ • F₁.symm τ)) = F₂ (γ • F₂.symm (H j τ)) := by
    have h := hactions j γ hγ (H j τ)
    change H j (F₁ (γ • F₁.symm ((H j).symm (H j τ)))) =
      F₂ (γ • F₂.symm (H j τ)) at h
    rwa [(H j).symm_apply_apply] at h
  have hpoint (τ : ℍ) : Tendsto (fun j => H j τ) atTop (𝓝 τ) := by
    apply UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff.mpr
    have h := hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (τ : ℂ))
    apply h.congr
    intro j
    exact ((hH j).1 τ).symm
  apply (mk_eq_mk_iff_canonical_lift_actions R hp hfixed m n).mpr
  change ∀ γ ∈ Γ, ∀ τ : ℍ, F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ)
  intro γ hγ τ
  have hleft := hpoint (F₁ (γ • F₁.symm τ))
  have hc : Continuous (fun z : ℍ => F₂ (γ • F₂.symm z)) :=
    F₂.continuous.comp ((continuous_const_smul γ).comp F₂.symm.continuous)
  have hright := (hc.tendsto τ).comp (hpoint τ)
  have hright' : Tendsto (fun j => H j (F₁ (γ • F₁.symm τ))) atTop
      (𝓝 (F₂ (γ • F₂.symm τ))) :=
    hright.congr (fun j => (hconj j γ hγ τ).symm)
  exact tendsto_nhds_unique hleft hright'

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
