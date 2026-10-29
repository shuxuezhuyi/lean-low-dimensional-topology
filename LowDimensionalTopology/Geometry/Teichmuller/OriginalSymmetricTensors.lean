module

public import LowDimensionalTopology.Geometry.Teichmuller.RiemannianConformality
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Original smooth symmetric tensors and conformal metric directions

Both slots are the original real surface tangent spaces. Smoothness is that
of the actual nested Hom bundle. The conformal directions are exactly the
range of multiplication of an arbitrary original metric by a smooth scalar.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- All smooth covariant two-tensors on the original real surface bundle. -/
abbrev SmoothSurfaceTwoTensor :=
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
    (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ]
      TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ)

/-- Symmetry cuts out the actual real vector space S2(R). -/
def symmetricTwoTensorSubmodule :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    Submodule ℝ (SmoothSurfaceTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  letI : ∀ x : X, IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) :=
    fun x => ContinuousLinearMap.isTopologicalAddGroup
      (E := TangentSpace 𝓘(ℝ, ℂ) x) (F := ℝ) (σ := RingHom.id ℝ)
  letI : ∀ x : X, ContinuousAdd (TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) :=
    fun x => (ContinuousLinearMap.isTopologicalAddGroup
      (E := TangentSpace 𝓘(ℝ, ℂ) x) (F := ℝ) (σ := RingHom.id ℝ)).toContinuousAdd
  exact
    { carrier := {h : SmoothSurfaceTwoTensor R |
        ∀ (x : X) (a b : TangentSpace 𝓘(ℝ, ℂ) x), h.toFun x a b = h.toFun x b a}
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        intro x a b
        rfl
      add_mem' := by
        intro h k hh hk
        simp only [Set.mem_ofPred_eq] at hh hk ⊢
        intro x a b
        change h.toFun x a b + k.toFun x a b = h.toFun x b a + k.toFun x b a
        rw [hh x a b, hk x a b]
      smul_mem' := by
        intro c h hh
        simp only [Set.mem_ofPred_eq] at hh ⊢
        intro x a b
        change c * h.toFun x a b = c * h.toFun x b a
        rw [hh x a b] }

/-- Smooth symmetric covariant two-tensors, with the inherited real module. -/
abbrev SmoothSymmetricTwoTensor := ↥(symmetricTwoTensorSubmodule R)

/-- Every original raw smooth metric is an element of S2, with unchanged slots. -/
def SmoothSurfaceMetric.toSymmetricTwoTensor (g : SmoothSurfaceMetric R.toRiemannSurface) :
    SmoothSymmetricTwoTensor R := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  refine ⟨⟨g.inner, g.contMDiff⟩, ?_⟩
  simp only [symmetricTwoTensorSubmodule]
  intro x a b
  exact g.symm x a b

variable {R}

/-- Multiplication by all smooth real scalars, as an actual linear map into S2. -/
def conformalScaleLinear (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    C^∞⟮𝓘(ℝ, ℂ), X; ℝ⟯ →ₗ[ℝ] SmoothSymmetricTwoTensor R := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  refine
    { toFun := fun ψ => ⟨⟨fun x => ψ x • g.inner x,
        ψ.contMDiff.smul_section g.contMDiff⟩, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · simp only [symmetricTwoTensorSubmodule]
    intro x a b
    change ψ x * g.inner x a b = ψ x * g.inner x b a
    rw [g.symm x a b]
  · intro ψ χ
    apply Subtype.ext
    apply ContMDiffSection.ext
    intro x
    ext a b
    change (ψ x + χ x) * g.inner x a b =
      ψ x * g.inner x a b + χ x * g.inner x a b
    exact add_mul _ _ _
  · intro c ψ
    apply Subtype.ext
    apply ContMDiffSection.ext
    intro x
    ext a b
    change (c * ψ x) * g.inner x a b = c * (ψ x * g.inner x a b)
    exact mul_assoc _ _ _

/-- Exactly the conformal-scale directions ψg, without a restriction on ψ. -/
def conformalVerticalTensors (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    Submodule ℝ (SmoothSymmetricTwoTensor R) :=
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  (conformalScaleLinear (R := R) g).range

/-- The range condition retains every smooth scalar and both original slots. -/
theorem mem_conformalVerticalTensors_iff (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    h ∈ conformalVerticalTensors (R := R) g ↔
      ∃ ψ : X → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ ψ ∧
        ∀ (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x),
          h.val x a b = ψ x * g.inner x a b := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ, ψ.contMDiff, ?_⟩
    intro x a b
    rw [← hψ]
    rfl
  · rintro ⟨ψ, hψ, hh⟩
    refine ⟨⟨ψ, hψ⟩, ?_⟩
    apply Subtype.ext
    apply ContMDiffSection.ext
    intro x
    ext a b
    exact (hh x a b).symm

/-- The actual exponential conformal coefficients have the stated first variation. -/
theorem conformal_exponential_firstVariation
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (ψ : let := R.toRiemannAtlas.toChartedSpace; C^∞⟮𝓘(ℝ, ℂ), X; ℝ⟯)
    (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    HasDerivAt (fun t : ℝ => Real.exp (t * ψ x) * g.inner x a b)
      ((conformalScaleLinear (R := R) g ψ).val x a b) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const (ψ x)).exp).mul_const
    (g.inner x a b)
  change HasDerivAt (fun t : ℝ => Real.exp (t * ψ x) * g.inner x a b)
    (ψ x * g.inner x a b) 0
  simpa only [id_eq, zero_mul, Real.exp_zero, one_mul] using h

end LowDimensionalTopology.Geometry.Teichmuller
