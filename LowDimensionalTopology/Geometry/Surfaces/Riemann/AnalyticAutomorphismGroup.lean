module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.SourceGenus
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.HurwitzTheorem

/-!
# The actual conformal automorphism group and its Hurwitz bound

Automorphisms are homeomorphisms analytic in the original complex atlas. Their
inverse analyticity follows from the existing native theorem, rather than being
an additional structure field. The genus comparison is a concrete explicit input.

The analytic Hurwitz proof reused below is due to Wu Xiaobin, fixed source commit
1c0d5473c020b66ed5106331a38a61536760b9b2, Apache-2.0.
-/

@[expose] public section
noncomputable section

open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

/-- Actual analytic target automorphisms, with composition inherited from homeomorphisms. -/
def RiemannAtlas.analyticAutomorphismSubgroup (A : RiemannAtlas X) : Subgroup (X ≃ₜ X) where
  carrier := {f | RiemannAnalyticMap A A f}
  one_mem' := RiemannAnalyticMap.id A
  mul_mem' := by
    intro f g hf hg
    change RiemannAnalyticMap A A ((f : X → X) ∘ (g : X → X))
    exact hf.comp hg
  inv_mem' := by
    intro f hf
    exact riemannAnalyticMap_homeomorph_symm f hf

/-- A higher-genus closed Riemann surface has a finite actual automorphism group,
with the sharp Hurwitz bound. Finiteness is stated separately from the card bound. -/
theorem ClosedRiemannSurface.analyticAutomorphism_finite_card_le
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g) :
    Finite R.toRiemannAtlas.analyticAutomorphismSubgroup ∧
      Nat.card R.toRiemannAtlas.analyticAutomorphismSubgroup ≤ 84 * (g - 1) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  have heq : {f : X ≃ₜ X | RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas f} =
      {f : X ≃ₜ X | LiZhongQC.IsBiholomorphic (f : X → X)} := by
    ext f
    exact Teichmuller.analyticHomeomorph_iff_sourceBiholomorphic
      R.toRiemannAtlas R.toRiemannAtlas f
  have h := LiZhongQC.hurwitz hg (R.sourceHasGenus hgenus hPresentation)
  rw [← heq] at h
  exact ⟨h.1, h.2⟩

end LowDimensionalTopology.Geometry.Surfaces
