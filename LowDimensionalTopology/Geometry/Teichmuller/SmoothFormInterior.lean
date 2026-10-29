/- Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import LowDimensionalTopology.Geometry.Teichmuller.ComplexCanonicalAtlas
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Analysis.Normed.Module.Alternating.Curry

/-!
# Insertion of smooth vector fields in actual tangent alternating forms

The domain and codomain are smooth sections of the actual alternating tangent
bundles. The construction uses no choice of norm on a tangent fibre.
-/

@[expose] public section

noncomputable section

open Bundle Filter Set Topology
open scoped Manifold Bundle ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.FormInterior

/-- Insert one vector into the first slot without choosing a norm on the fibre. -/
def insertFiber {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] {n : ℕ} (form : V [⋀^Fin (n + 1)]→L[ℝ] ℝ) (X : V) :
    V [⋀^Fin n]→L[ℝ] ℝ :=
  { form.toAlternatingMap.curryLeft X with
    cont := form.cont.comp (continuous_const.matrixVecCons continuous_id) }

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Smooth real differential forms on the actual tangent bundle. -/
abbrev SmoothForm (n : ℕ) :=
  ContMDiffSection I (E [⋀^Fin n]→L[ℝ] ℝ) ∞
    (fun p : M => TangentSpace I p [⋀^Fin n]→L[ℝ] ℝ)

/-- Smooth vector fields on the same actual tangent bundle. -/
abbrev SmoothVectorField := ContMDiffSection I E ∞ (TangentSpace I : M → Type _)

/-- The actual alternating-form bundle chart is the tangent pullback on every slot. -/
theorem form_trivialization {n : ℕ} (p₀ p : M)
    (form : TangentSpace I p [⋀^Fin n]→L[ℝ] ℝ) :
    ((trivializationAt (E [⋀^Fin n]→L[ℝ] ℝ)
      (fun q : M => TangentSpace I q [⋀^Fin n]→L[ℝ] ℝ) p₀) ⟨p, form⟩).2 =
      form.compContinuousLinearMap ((trivializationAt E (TangentSpace I) p₀).symmL ℝ p) := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  change ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ p
    |>.compContinuousAlternatingMap form
    |>.compContinuousLinearMap ((trivializationAt E (TangentSpace I) p₀).symmL ℝ p)) = _
  rw [Bundle.Trivial.continuousLinearMapAt_trivialization]
  ext v
  rfl

/-- Insertion commutes with the actual tangent bundle coordinates. -/
theorem insert_coordinates {n : ℕ} (p₀ p : M)
    (hp : p ∈ (trivializationAt E (TangentSpace I) p₀).baseSet)
    (form : TangentSpace I p [⋀^Fin (n + 1)]→L[ℝ] ℝ) (X : TangentSpace I p) :
    (insertFiber form X).compContinuousLinearMap
        ((trivializationAt E (TangentSpace I) p₀).symmL ℝ p) =
      (form.compContinuousLinearMap ((trivializationAt E (TangentSpace I) p₀).symmL ℝ p)).curryLeft
        ((trivializationAt E (TangentSpace I) p₀).continuousLinearMapAt ℝ p X) := by
  ext v
  change form (Matrix.vecCons X
      (fun i => (trivializationAt E (TangentSpace I) p₀).symmL ℝ p (v i))) =
    form (fun i => (trivializationAt E (TangentSpace I) p₀).symmL ℝ p
      (Matrix.vecCons
        ((trivializationAt E (TangentSpace I) p₀).continuousLinearMapAt ℝ p X) v i))
  congr 1
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  exact ((trivializationAt E (TangentSpace I) p₀).symmL_continuousLinearMapAt hp X).symm

/-- Insertion in the first slot sends every smooth form to a smooth form. -/
def interior {n : ℕ} (X : SmoothVectorField I (M := M))
    (form : SmoothForm I (M := M) (n + 1)) : SmoothForm I (M := M) n := by
  refine ⟨fun p => insertFiber (form p) (X p), ?_⟩
  intro p₀
  apply (Bundle.contMDiffAt_section p₀).mpr
  simp only [form_trivialization]
  let e := trivializationAt E (TangentSpace I) p₀
  have hform : ContMDiffAt I 𝓘(ℝ, E [⋀^Fin (n + 1)]→L[ℝ] ℝ) ∞
      (fun p => (form p).compContinuousLinearMap (e.symmL ℝ p)) p₀ := by
    simpa only [form_trivialization] using
      ((Bundle.contMDiffAt_section p₀).mp (form.contMDiff p₀))
  have hX : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun p => e.continuousLinearMapAt ℝ p (X p)) p₀ := by
    apply ((Bundle.contMDiffAt_section p₀).mp (X.contMDiff p₀)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) p₀)]
      with p hp
    exact e.continuousLinearMapAt_apply_of_mem ℝ hp (X p)
  have h := (((ContinuousAlternatingMap.curryLeftLI
      (𝕜 := ℝ) (E := E) (F := ℝ) (n := n)).toContinuousLinearMap.contDiff
      |>.comp_contMDiffAt hform).clm_apply hX)
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) p₀)]
    with p hp
  exact insert_coordinates I p₀ p hp (form p) (X p)

@[simp] theorem interior_apply {n : ℕ} (X : SmoothVectorField I (M := M))
    (form : SmoothForm I (M := M) (n + 1)) (p : M) (v : Fin n → TangentSpace I p) :
    interior I X form p v = form p (Matrix.vecCons (X p) v) := rfl

end Manifold

open Surfaces TeichmullerSpace

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

/-- The full contraction operator on the original native marked quotient. -/
def nativeInterior (n : ℕ) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    letI : IsManifold 𝓘(ℝ, Fin (3 * g - 3) → ℂ) ∞ (TeichmullerSpace.{u, u} R) :=
      (canonicalBersCoordinates_isOpenEmbedding R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp hsmooth).isManifold_singleton
    SmoothVectorField 𝓘(ℝ, Fin (3 * g - 3) → ℂ) (M := TeichmullerSpace.{u, u} R) →
      SmoothForm 𝓘(ℝ, Fin (3 * g - 3) → ℂ) (M := TeichmullerSpace.{u, u} R) (n + 1) →
      SmoothForm 𝓘(ℝ, Fin (3 * g - 3) → ℂ) (M := TeichmullerSpace.{u, u} R) n := by
  letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  letI : IsManifold 𝓘(ℝ, Fin (3 * g - 3) → ℂ) ∞ (TeichmullerSpace.{u, u} R) :=
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth).isManifold_singleton
  exact interior 𝓘(ℝ, Fin (3 * g - 3) → ℂ)

end LowDimensionalTopology.Geometry.Teichmuller.FormInterior
