module
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# A supporting line for disjoint open convex planar sets.

Geometric Hahn–Banach separation places common closure points of two nonempty disjoint
open convex subsets of the complex plane on a single real affine line.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Classical

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis

set_option backward.isDefEq.respectTransparency false in
/-- Two nonempty disjoint open convex planar sets have all common closure points on one real line. -/
theorem convex_open_disjoint_closures_hyperplane {U V : Set ℂ}
    (hUc : Convex ℝ U) (hUo : IsOpen U) (hUn : U.Nonempty)
    (hVc : Convex ℝ V) (hVo : IsOpen V) (hVn : V.Nonempty) (hd : Disjoint U V) :
    ∃ (n : ℂ) (t : ℝ), n ≠ 0 ∧ ∀ z ∈ closure U ∩ closure V, inner ℝ n z = t := by
  obtain ⟨f, t, hUf, hVf⟩ := geometric_hahn_banach_open_open hUc hUo hVc hVo hd
  have hf : f ≠ 0 := by
    intro he
    obtain ⟨u, hu⟩ := hUn
    obtain ⟨v, hv⟩ := hVn
    have h1 := hUf u hu
    have h2 := hVf v hv
    rw [he] at h1 h2
    simp only [zero_apply] at h1 h2
    exact h1.not_ge h2.le
  let n : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm f
  have hn : n ≠ 0 := by
    intro he
    apply hf
    apply (InnerProductSpace.toDual ℝ ℂ).symm.injective
    simpa only [map_zero] using he
  have hUl : closure U ⊆ {z | f z ≤ t} := closure_minimal
    (fun z hz => (hUf z hz).le) (isClosed_le f.continuous continuous_const)
  have hVr : closure V ⊆ {z | t ≤ f z} := closure_minimal
    (fun z hz => (hVf z hz).le) (isClosed_le continuous_const f.continuous)
  refine ⟨n, t, hn, fun z hz => ?_⟩
  change inner ℝ ((InnerProductSpace.toDual ℝ ℂ).symm f) z = t
  rw [InnerProductSpace.toDual_symm_apply]
  exact le_antisymm (hUl hz.1) (hVr hz.2)

end LowDimensionalTopology.Geometry.Auxiliary.Analysis
