module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalQuadraticFoliation
public import Mathlib.Tactic.Linarith

/-!
# Local plaque compatibility of flat charts of the same differential

Two flat charts of the same native quadratic differential have a local sign
and translation transition. Equality of their imaginary coordinates therefore
defines the same local plaques on an actual common open neighborhood.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    {q : HolomorphicQuadraticDifferential R.toRiemannAtlas}

/-- Genuine flat charts of the same differential have the same local plaques on overlaps. -/
theorem quadraticNaturalLeafCharts_locallySamePlaques
    {e d : OpenPartialHomeomorph X ℂ} (he : IsQuadraticNaturalLeafChart R q e)
    (hd : IsQuadraticNaturalLeafChart R q d) {p : X} (hp : p ∈ e.source ∩ d.source) :
    LocallySamePlaques e d p := by
  let := R.toRiemannAtlas.toChartedSpace
  have hE := he.2 p hp.1
  have hD := hd.2 p hp.2
  obtain ⟨ε, c, hε, hEq⟩ := LiZhongQC.s26d_a_natural_unique
    (W := fun x => e x - e p) (W' := fun x => d x - d p)
    (he.1 hp.1) hE.1 hE.2.2.2 hD.1 hD.2.2.2
  have hN : (e.source ∩ d.source) ∩
      {x | e x - e p = ε * (d x - d p) + c} ∈ 𝓝 p :=
    inter_mem (inter_mem (e.open_source.mem_nhds hp.1)
      (d.open_source.mem_nhds hp.2)) hEq
  obtain ⟨W, hWS, hWo, hpW⟩ := mem_nhds_iff.mp hN
  refine ⟨W, hWo, hpW, fun x hx => (hWS hx).1, ?_⟩
  intro x hx y hy
  have hxEq := (hWS hx).2
  have hyEq := (hWS hy).2
  rcases hε with rfl | rfl
  all_goals
    have hxim := congrArg Complex.im hxEq
    have hyim := congrArg Complex.im hyEq
    simp only [one_mul, neg_one_mul, Complex.sub_im, Complex.add_im, Complex.neg_im]
      at hxim hyim
    constructor <;> intro hxy <;> linarith

end LowDimensionalTopology.Geometry.Teichmuller
