module

public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiDifferential
public import LowDimensionalTopology.External.LiZhongQC.Ch01.S07_GeometricDefinition

/-!
# Compact coefficient bounds and the C¹ quasiconformal criterion

The plane estimate is the domain-independent
part of LiZhongQC.Lemmas.DEDescent.s24q_isKQC_of_bound, upstream commit
1c0d5473c020b66ed5106331a38a61536760b9b2. No genus or uniformization occurs.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.BeltramiDifferential

open Surfaces

universe u

/-- On a compact surface, pointwise strict bounds on a genuine continuous tensor
are equivalent to a strict bound on its intrinsic supremum norm. -/
theorem supNorm_lt_one_iff
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {A : RiemannAtlas X} (μ : BeltramiDifferential A) :
    μ.supNorm < 1 ↔ ∀ x, μ.abs x < 1 := by
  change ‖μ.abs‖ < 1 ↔ _
  constructor
  · intro h x
    have hx := (μ.abs.norm_lt_iff (by norm_num : (0 : ℝ) < 1)).1 h x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (μ.abs_nonneg x)] using hx
  · intro h
    apply (μ.abs.norm_lt_iff (by norm_num : (0 : ℝ) < 1)).2
    intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (μ.abs_nonneg x)] using h x

/-- A strict bound in every original chart gives a single uniform constant below
one; compactness is the reason the strict inequality is retained. -/
theorem exists_uniform_coeff_bound_lt_one
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {A : RiemannAtlas X} (μ : BeltramiDifferential A)
    (hμ : ∀ (e : Chart A) (z : e.val.target), ‖μ.coeff e z‖ < 1) :
    ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      ∀ (e : Chart A) (z : e.val.target), ‖μ.coeff e z‖ ≤ k := by
  refine ⟨μ.supNorm, μ.supNorm_nonneg, ?_, μ.coeff_norm_le_supNorm⟩
  apply (μ.supNorm_lt_one_iff).2
  intro x
  obtain ⟨e, he, hx⟩ := A.cover x
  rw [μ.abs_eq_coeff ⟨e, he⟩ x hx]
  exact hμ ⟨e, he⟩ ⟨e x, e.map_source hx⟩

end LowDimensionalTopology.Geometry.Teichmuller.BeltramiDifferential

namespace LiZhongQC

/-- The actual C¹ criterion on an arbitrary open plane set. The finite constant
comes from the supplied uniform coefficient bound, not from C¹ regularity alone. -/
theorem isKQC_of_contDiffOn_jacobian_pos_bound
    {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : ContDiffOn ℝ 1 f D) (hhomeo : IsHomeomorphOnto f D (f '' D))
    (hJ : ∀ z ∈ D, 0 < jacobian f z)
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hμ : ∀ z ∈ D, ‖complexDilatation f z‖ ≤ k) :
    IsKQC f D ((1 + k) / (1 - k)) := by
  have hk1' : 0 < 1 - k := by linarith
  have hlt : ∀ z ∈ D, ‖dzbar f z‖ < ‖dz f z‖ := by
    intro z hz
    have h := hJ z hz
    unfold jacobian at h
    nlinarith [norm_nonneg (dzbar f z), norm_nonneg (dz f z)]
  refine isKQC_of_isC1Quasiconformal ⟨hD, ?_, hf, hhomeo, fun z hz => ⟨hlt z hz, ?_⟩⟩
  · rw [le_div_iff₀ hk1']
    linarith
  · have hm := hμ z hz
    have hm0 := norm_nonneg (complexDilatation f z)
    unfold dilatationQuotient
    rw [div_le_div_iff₀ (by linarith) hk1']
    nlinarith

end LiZhongQC
