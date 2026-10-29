module

public import LowDimensionalTopology.Geometry.Teichmuller.Space
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothBeltrami
public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiCompactBounds
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence
public import Mathlib.Logic.Relation

/-!
# Comparing smooth and quasiconformal markings

Actual positive smooth markings have a uniform quasiconformal bound by
compactness. The comparison preserves the original complex atlas and the
marking maps. No genus or uniformization premise is needed for the forward map.
The reference and target initially share the universe required by `MarkedRS`.
-/

@[expose] public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace LiZhongQC

/-- The actual restriction of an open partial homeomorphism is a homeomorphism
onto its image, in the plane QC library's inverse-on-a-set definition. -/
theorem isHomeomorphOnto_openPartialHomeomorph (e : OpenPartialHomeomorph ℂ ℂ) :
    IsHomeomorphOnto e e.source (e '' e.source) := by
  refine ⟨e.continuousOn, e.injOn, rfl, ?_⟩
  rw [e.image_source_eq_target]
  apply e.symm.continuousOn.congr
  intro y hy
  calc
    Function.invFunOn e e.source y =
        Function.invFunOn e e.source (e (e.symm y)) :=
      congrArg (Function.invFunOn e e.source) (e.right_inv hy).symm
    _ = e.symm y := e.injOn.leftInvOn_invFunOn (e.map_target hy)

end LiZhongQC

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

namespace SmoothSurfaceEquiv

/-- Compactness turns the actual continuous Beltrami coefficient of a smooth
positive diffeomorphism into a uniform QC bound. No smoothness or orientation
assumption is replaced by a QC existence premise. -/
theorem isQCRS_of_compact
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] {R : RiemannSurface X} {S : RiemannSurface Y}
    (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := S.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsQCRS f.toHomeomorph := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  obtain ⟨k, hk0, hk1, hk⟩ :=
    (f.beltrami hf).exists_uniform_coeff_bound_lt_one (f.beltrami_coeff_norm_lt_one hf)
  refine ⟨(1 + k) / (1 - k), ?_, fun x => ?_⟩
  · rw [le_div_iff₀ (by linarith : 0 < 1 - k)]
    linarith
  · let e := chartAt ℂ x
    let g := chartAt ℂ (f.toHomeomorph x)
    have he : e ∈ R.charts := chart_mem_atlas ℂ x
    have hg : g ∈ S.charts := chart_mem_atlas ℂ (f.toHomeomorph x)
    let F := riemannHomeomorphChart e f.toHomeomorph g
    have hhomeo : LiZhongQC.IsHomeomorphOnto
        (riemannChartMap e f.toHomeomorph g)
        (riemannChartMapDomain e f.toHomeomorph g)
        ((riemannChartMap e f.toHomeomorph g) ''
          riemannChartMapDomain e f.toHomeomorph g) := by
      have h := LiZhongQC.isHomeomorphOnto_openPartialHomeomorph F
      change LiZhongQC.IsHomeomorphOnto
        (riemannChartMap e f.toHomeomorph g) F.source
        ((riemannChartMap e f.toHomeomorph g) '' F.source) at h
      rwa [show F.source = riemannChartMapDomain e f.toHomeomorph g from
        riemannHomeomorphChart_source e f.toHomeomorph g] at h
    have hC1 := f.chartMap_contDiffOn_real e he g hg
    change LiZhongQC.IsKQC (riemannChartMap e f.toHomeomorph g)
      (riemannChartMapDomain e f.toHomeomorph g) ((1 + k) / (1 - k))
    apply LiZhongQC.isKQC_of_contDiffOn_jacobian_pos_bound
      (riemannChartMapDomain_isOpen e f.toHomeomorph g f.toHomeomorph.continuous)
      hC1 hhomeo _ hk0 hk1
    · intro z hz
      have h := hk ⟨e, he⟩ ⟨z, hz.1⟩
      rwa [f.beltrami_coeff_eq_chartDilatation hf
        ⟨e, he⟩ ⟨z, hz.1⟩ g hg hz.2] at h
    · intro z hz
      have hpos := hf e he g hg z hz
      have hd : DifferentiableAt ℝ (riemannChartMap e f.toHomeomorph g) z :=
        (hC1.differentiableOn one_ne_zero).differentiableAt
          ((riemannChartMapDomain_isOpen e f.toHomeomorph g
            f.toHomeomorph.continuous).mem_nhds hz)
      change 0 < LinearMap.det
        (fderiv ℝ (riemannChartMap e f.toHomeomorph g) z : ℂ →ₗ[ℝ] ℂ) at hpos
      rwa [LiZhongQC.det_fderiv_eq_jacobian hd] at hpos

end SmoothSurfaceEquiv

/-- For a genuine target homeomorphism, all-chart analyticity in the native
atlas is exactly biholomorphicity for its actual atlas-derived manifolds. -/
theorem analyticHomeomorph_iff_sourceBiholomorphic
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannAtlas X) (B : RiemannAtlas Y) (h : X ≃ₜ Y) :
    RiemannAnalyticMap A B h ↔
      letI := A.toChartedSpace
      letI := B.toChartedSpace
      LiZhongQC.IsBiholomorphic (h : X → Y) := by
  let := A.toChartedSpace
  let := B.toChartedSpace
  let := A.isManifold
  let := B.isManifold
  constructor
  · intro hh
    exact ⟨hh.contMDiff.mdifferentiable (by simp), h.symm,
      (riemannAnalyticMap_homeomorph_symm h hh).contMDiff.mdifferentiable (by simp),
      h.symm_apply_apply, h.apply_symm_apply⟩
  · intro hh
    exact riemannAnalyticMap_of_contMDiff A B h
      (LiZhongQC.k22u_mdifferentiable_contMDiff hh.1)

end LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

universe u

/-- The source bundle uses exactly the original carrier, topology, and atlas;
only the packaging of the already established manifold structure changes. -/
def toSourceClosedRS
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) :
    LiZhongQC.ClosedRS.{u} where
  carrier := X
  topologicalSpace := inferInstance
  t2Space := R.t2Space
  connectedSpace := R.connectedSpace
  compactSpace := R.compactSpace
  chartedSpace := R.toRiemannAtlas.toChartedSpace
  isManifold := R.toRiemannAtlas.isManifold

end LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- An actual smooth oriented marking is a QC marking on its compact source.
The homeomorphism and variable target are preserved literally. -/
def toSource (M : MarkedRiemannSurface.{u, u} R) :
    letI := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.MarkedRS X := by
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.compactSpace
  exact
    { X := M.surface.toSourceClosedRS
      marking := M.marking.toHomeomorph
      qc := M.marking.isQCRS_of_compact M.orientation_preserving }

/-- Both marked equivalence relations have precisely the same witnesses on
native smooth markings. The QC proof does not change their marking maps. -/
theorem toSource_equiv_iff (M N : MarkedRiemannSurface.{u, u} R) :
    (let := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.MarkedRS.Equiv M.toSource N.toSource) ↔ Equivalent M N := by
  let := R.toRiemannAtlas.toChartedSpace
  let := M.surface.toRiemannAtlas.toChartedSpace
  let := N.surface.toRiemannAtlas.toChartedSpace
  constructor
  · rintro ⟨h, hh, hhom⟩
    exact ⟨h, (analyticHomeomorph_iff_sourceBiholomorphic
      M.surface.toRiemannAtlas N.surface.toRiemannAtlas h).mpr hh, hhom⟩
  · rintro ⟨h, hh, hhom⟩
    exact ⟨h, (analyticHomeomorph_iff_sourceBiholomorphic
      M.surface.toRiemannAtlas N.surface.toRiemannAtlas h).mp hh, hhom⟩

end MarkedRiemannSurface

namespace TeichmullerSpace

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Forget smoothness and retain the actual QC-marked surface, then descend by
the proved compatibility of the two marked equivalence relations. -/
def toSource :
    TeichmullerSpace.{u, u} R →
      letI := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.TeichSpace X := by
  letI := R.toRiemannAtlas.toChartedSpace
  exact Quotient.lift (fun M => Quot.mk _ M.toSource) (by
    intro M N h
    exact Quot.sound ((MarkedRiemannSurface.toSource_equiv_iff M N).mpr h))

@[simp]
theorem toSource_mk (M : MarkedRiemannSurface.{u, u} R) :
    toSource R (mk M) =
      (let := R.toRiemannAtlas.toChartedSpace;
        Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X)) M.toSource) := rfl

/-- No two distinct native smooth-marked classes are identified by forgetting
smoothness. The source uses `Quot`; its proved equivalence theorem is explicitly
used to recover the original relation from equality in that quotient. -/
theorem toSource_injective : Function.Injective (toSource R) := by
  let := R.toRiemannAtlas.toChartedSpace
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro M N h
  apply Quotient.sound
  apply (MarkedRiemannSurface.toSource_equiv_iff M N).mp
  exact (LiZhongQC.markedRS_equiv_equivalence (S₀ := X)).eqvGen_iff.mp
    (Quot.eqvGen_exact h)

end TeichmullerSpace

end LowDimensionalTopology.Geometry.Teichmuller
