module

public import LowDimensionalTopology.Geometry.Teichmuller.AtlasMetricLocalForms
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Local smooth coordinate forms on the original tangent bundle

The constant real inner product in a genuine tangent trivialization gives a
smooth local bilinear section. Its equality with the original chart form is
proved using the public differential description of that trivialization.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Bundle Set
open scoped Manifold ContDiff InnerProductSpace

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

namespace AtlasMetricConstruction

universe u
variable {X : Type u} [TopologicalSpace X] (R : RiemannSurface X)

/-- The normed model of continuous real bilinear forms in complex coordinates. -/
abbrev FormModel := ℂ →L[ℝ] ℂ →L[ℝ] ℝ

/-- The actual original complex chart chosen at the specified surface point. -/
def chosenChart (j : X) : OriginalComplexChart R := by
  let := R.toRiemannAtlas.toChartedSpace
  exact ⟨chartAt ℂ j, chart_mem_atlas ℂ j⟩

/-- The constant Euclidean form in the nested Hom trivialization of the actual
tangent bundle. Its values outside that trivialization are only totalizations. -/
def localForm (j x : X) : TangentForm R x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let t := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) j
  let c := trivializationAt ℝ (fun _ : X => ℝ) j
  let h := t.continuousLinearMap (RingHom.id ℝ) c
  let T := t.continuousLinearMap (RingHom.id ℝ) h
  exact T.symmL ℝ x (innerSL ℝ : FormModel)

/-- On its actual source, the nested-Hom form is precisely the pullback by the
original complex chart differential. -/
theorem localForm_eq_chartForm (j x : X)
    (hx : x ∈ (chosenChart R j).val.source) :
    localForm R j x = chartForm R (chosenChart R j) x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let t := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) j
  let c := trivializationAt ℝ (fun _ : X => ℝ) j
  let h := t.continuousLinearMap (RingHom.id ℝ) c
  let T := t.continuousLinearMap (RingHom.id ℝ) h
  let : IsNormableSpace ℝ (RealSurfaceTangent R x) :=
    (SmoothSurfaceEquiv.originalChartDifferentialEquiv (chosenChart R j) x hx).isNormableSpace
  let Q : TangentForm R x :=
    (innerSL ℝ : FormModel).bilinearComp
      (t.continuousLinearMapAt ℝ x) (t.continuousLinearMapAt ℝ x)
  have ht : x ∈ t.baseSet := by
    simpa only [t, TangentBundle.trivializationAt_baseSet, chosenChart] using hx
  have hc : x ∈ c.baseSet := by
    have hcx := mem_baseSet_trivializationAt ℝ (fun _ : X => ℝ) x
    simpa only [c, Bundle.Trivial.fiberBundle_trivializationAt'] using hcx
  have hh : x ∈ h.baseSet := ⟨ht, hc⟩
  have hT : x ∈ T.baseSet := ⟨ht, hh⟩
  have hQ : T.continuousLinearMapAt ℝ x Q = (innerSL ℝ : FormModel) := by
    ext a b
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ T hT Q]
    rw [Trivialization.continuousLinearMap_apply]
    change (h.continuousLinearMapAt ℝ x (Q (t.symmL ℝ x a))) b =
      (innerSL ℝ : FormModel) a b
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ h hh]
    rw [Trivialization.continuousLinearMap_apply]
    change c.continuousLinearMapAt ℝ x (Q (t.symmL ℝ x a) (t.symmL ℝ x b)) =
      (innerSL ℝ : FormModel) a b
    simp only [c, Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
    dsimp only [Q]
    rw [ContinuousLinearMap.bilinearComp_apply,
      Trivialization.continuousLinearMapAt_symmL t ht,
      Trivialization.continuousLinearMapAt_symmL t ht]
  have hlocal : localForm R j x = Q := by
    change T.symmL ℝ x (innerSL ℝ : FormModel) = Q
    rw [← hQ]
    exact T.symmL_continuousLinearMapAt hT Q
  have hD : t.continuousLinearMapAt ℝ x =
      originalChartDifferential R (chosenChart R j) x := by
    have hx' : x ∈ (chartAt ℂ j).source := hx
    have hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
        (chartAt ℂ j : X → ℂ) x :=
      mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) (chart_mem_atlas ℂ j) hx'
    change (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) j).continuousLinearMapAt ℝ x =
      mvfderiv 𝓘(ℝ, ℂ) (chartAt ℂ j : X → ℂ) x
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx',
      tangentBundleCore_coordChange_achart, hd.mvfderiv]
    simp only [writtenInExtChartAt, extChartAt_self_eq, extChartAt_coe,
      modelWithCornersSelf_coe, Function.id_comp]
    ext v
    rfl
  rw [hlocal]
  change (innerSL ℝ : FormModel).bilinearComp
      (t.continuousLinearMapAt ℝ x) (t.continuousLinearMapAt ℝ x) =
    (innerSL ℝ : FormModel).bilinearComp
      (originalChartDifferential R (chosenChart R j) x)
      (originalChartDifferential R (chosenChart R j) x)
  rw [hD]

/-- The local form is genuinely infinitely smooth as a section of the original
nested bilinear Hom bundle on the original chart source. -/
theorem localForm_contMDiffOn (j : X) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, FormModel)) ∞
      (fun x => TotalSpace.mk' FormModel
        (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
          TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) x (localForm R j x))
      (chosenChart R j).val.source := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, FormModel)) ∞
    (fun x => TotalSpace.mk' FormModel
      (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) x (localForm R j x))
    (chosenChart R j).val.source
  let t := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) j
  let c := trivializationAt ℝ (fun _ : X => ℝ) j
  let h := t.continuousLinearMap (RingHom.id ℝ) c
  let T := t.continuousLinearMap (RingHom.id ℝ) h
  have hcbase : c.baseSet = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    have hy := mem_baseSet_trivializationAt ℝ (fun _ : X => ℝ) y
    simpa only [c, Bundle.Trivial.fiberBundle_trivializationAt'] using hy
  have hbase : T.baseSet = (chosenChart R j).val.source := by
    simp only [T, h, Trivialization.baseSet_continuousLinearMap,
      hcbase, t, TangentBundle.trivializationAt_baseSet, chosenChart,
      Set.inter_univ, Set.inter_self]
  rw [← hbase]
  apply (T.contMDiffOn_section_baseSet_iff).mpr
  apply contMDiffOn_const.congr
  intro x hx
  change (T ⟨x, T.symmL ℝ x (innerSL ℝ : FormModel)⟩).2 = (innerSL ℝ : FormModel)
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ T hx]
  exact T.continuousLinearMapAt_symmL hx (innerSL ℝ : FormModel)

end AtlasMetricConstruction

end LowDimensionalTopology.Geometry.Teichmuller
