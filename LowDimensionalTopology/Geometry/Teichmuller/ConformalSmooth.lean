module

public import LowDimensionalTopology.Geometry.Teichmuller.MappingClassGroup
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Biholomorphic maps and smooth oriented surface maps

The real smooth structure is derived from the original analytic coordinate
changes. An analytic homeomorphism consequently supplies a real smooth
diffeomorphism and preserves the complex orientations, with no additional
regularity or Jacobian hypothesis.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces

universe u v

/-- A complex analytic atlas also gives a real smooth manifold in the same charts. -/
theorem RiemannAtlas.isRealManifold {X : Type u} [TopologicalSpace X] (A : RiemannAtlas X) :
    let := A.toChartedSpace
    IsManifold 𝓘(ℝ, ℂ) ∞ X := by
  let := A.toChartedSpace
  apply isManifold_of_contDiffOn 𝓘(ℝ, ℂ) ∞ X
  intro e f he hf
  have h : ContDiffOn ℝ ∞ (e.symm.trans f) (e.symm.trans f).source :=
    ((A.compatible e he f hf).contDiffOn (n := ∞)
      (e.symm.trans f).open_source.uniqueDiffOn).restrict_scalars ℝ
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id,
    Set.inter_univ] using h

/-- An all-chart analytic surface map is real smooth for the original atlases. -/
theorem RiemannAnalyticMap.contMDiff_real {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {f : X → Y}
    (hf : RiemannAnalyticMap A B f) :
    let := A.toChartedSpace
    let := B.toChartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f := by
  let := A.toChartedSpace
  let := B.toChartedSpace
  let := A.isRealManifold
  let := B.isRealManifold
  rw [contMDiff_iff]
  refine ⟨hf.continuous, ?_⟩
  intro x y
  have h := ((hf.2 (chartAt ℂ x) (chart_mem_atlas ℂ x)
    (chartAt ℂ y) (chart_mem_atlas ℂ y)).contDiffOn (n := ∞)
      (riemannChartMapDomain_isOpen _ f _ hf.continuous).uniqueDiffOn).restrict_scalars ℝ
  simpa only [extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_target,
    OpenPartialHomeomorph.extend_source, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.preimage_id, Set.range_id, Set.inter_univ,
    riemannChartMap, riemannChartMapDomain] using h

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

/-- Biholomorphic coordinate changes preserve the complex orientations. -/
theorem analyticHomeomorph_preservesComplexOrientation
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} (h : X ≃ₜ Y)
    (hh : RiemannAnalyticMap A B h) : PreservesComplexOrientation A B h := by
  intro e he g hg z hz
  let F := riemannHomeomorphChart e h g
  have hzF : z ∈ F.source := by
    change z ∈ (riemannHomeomorphChart e h g).source
    rwa [riemannHomeomorphChart_source]
  have hF : AnalyticOnNhd ℂ F F.source := by
    change AnalyticOnNhd ℂ (riemannHomeomorphChart e h g)
      (riemannHomeomorphChart e h g).source
    rw [riemannHomeomorphChart_source]
    exact hh.2 e he g hg
  change 0 < realJacobian F z
  rw [realJacobian_eq_norm_deriv_sq (hF z hzF).differentiableAt]
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
    (openPartialHomeomorph_analytic_forward_deriv_ne_zero F hF z hzF))

namespace SmoothSurfaceEquiv

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Regard an analytic homeomorphism as the induced real smooth surface equivalence.
Analyticity of the inverse follows from the existing analytic inverse theorem. -/
def ofConformalHomeomorph (R : RiemannSurface X) (S : RiemannSurface Y)
    (h : X ≃ₜ Y) (hh : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas h) :
    SmoothSurfaceEquiv R S := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  exact
    { toEquiv := h.toEquiv
      contMDiff_toFun := hh.contMDiff_real
      contMDiff_invFun := (riemannAnalyticMap_homeomorph_symm h hh).contMDiff_real }

@[simp]
theorem ofConformalHomeomorph_toHomeomorph
    (R : RiemannSurface X) (S : RiemannSurface Y) (h : X ≃ₜ Y)
    (hh : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas h) :
    (ofConformalHomeomorph R S h hh).toHomeomorph = h := rfl

/-- The induced real smooth equivalence is orientation preserving. -/
theorem ofConformalHomeomorph_preservesComplexOrientation
    (R : RiemannSurface X) (S : RiemannSurface Y) (h : X ≃ₜ Y)
    (hh : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas h) :
    PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas
      (ofConformalHomeomorph R S h hh).toHomeomorph := by
  simpa only [ofConformalHomeomorph_toHomeomorph] using
    analyticHomeomorph_preservesComplexOrientation h hh

end SmoothSurfaceEquiv

namespace OrientedSurfaceAut

variable {X : Type u} [TopologicalSpace X]

/-- A conformal automorphism gives an actual orientation-preserving smooth automorphism. -/
def ofConformalHomeomorph (R : ClosedRiemannSurface X) (h : X ≃ₜ X)
    (hh : RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas h) : OrientedSurfaceAut R where
  smooth := SmoothSurfaceEquiv.ofConformalHomeomorph
    R.toRiemannSurface R.toRiemannSurface h hh
  orientation_preserving :=
    SmoothSurfaceEquiv.ofConformalHomeomorph_preservesComplexOrientation
      R.toRiemannSurface R.toRiemannSurface h hh

@[simp]
theorem ofConformalHomeomorph_toHomeomorph
    (R : ClosedRiemannSurface X) (h : X ≃ₜ X)
    (hh : RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas h) :
    (ofConformalHomeomorph R h hh).toHomeomorph = h := rfl

/-- The subgroup consisting of the actual analytic surface automorphisms. -/
def conformalSubgroup (R : ClosedRiemannSurface X) : Subgroup (OrientedSurfaceAut R) where
  carrier := {f | RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph}
  one_mem' := RiemannAnalyticMap.id R.toRiemannAtlas
  mul_mem' := by
    intro f g hf hg
    exact hf.comp hg
  inv_mem' := by
    intro f hf
    exact riemannAnalyticMap_homeomorph_symm f.toHomeomorph hf

/-- The conformal-to-smooth conversion lands in the conformal automorphism subgroup. -/
theorem ofConformalHomeomorph_mem_conformalSubgroup
    (R : ClosedRiemannSurface X) (h : X ≃ₜ X)
    (hh : RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas h) :
    ofConformalHomeomorph R h hh ∈ conformalSubgroup R := by
  change RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas
    (ofConformalHomeomorph R h hh).toHomeomorph
  simpa only [ofConformalHomeomorph_toHomeomorph] using hh

end OrientedSurfaceAut

end LowDimensionalTopology.Geometry.Teichmuller
