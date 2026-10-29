module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslation
public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedPointNaturality
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
public import Mathlib.Tactic.Ring

/-!
# The deformed weighted Bers space depends on the original Teichmüller point

Equal actual upper-half-plane actions differ only by the central sign in a
real special-linear lift. The literal quadratic-differential transformation
law is unchanged by that sign. Consequently the full source automorphic
submodules, and their faithful weighted realizations, are actually equal.

Their continuous complex-linear identification is the identity on every
original weighted vector and is isometric for the unchanged norms. The
actual whole Bers-coordinate translation is natural under this identification.
The final original-point consumer proves the density premise from the actual
compact uniformization; it assumes no equality of matrix-lift subgroups.

The action comparison and normalized source-coordinate arguments reuse Wu
Xiaobin's LiZhongQC development, Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

variable {Γ : Subgroup Deck}

private theorem automorphicPullback_eq_of_same_action {A B : Deck}
    (hact : ∀ z : ℍ, A • z = B • z) (φ : ℂ → ℂ) (z : ℂ) :
    φ (LiZhongQC.mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) z) /
        ((A 1 0 : ℂ) * z + A 1 1) ^ 4 =
      φ (LiZhongQC.mobiusFn (B 0 0) (B 0 1) (B 1 0) (B 1 1) z) /
        ((B 1 0 : ℂ) * z + B 1 1) ^ 4 := by
  rcases LiZhongQC.b33_d_eq_or_eq_neg hact with he | he
  · rw [he]
  · have hfour : (((-B) 1 0 : ℂ) * z + (-B) 1 1) ^ 4 =
        ((B 1 0 : ℂ) * z + B 1 1) ^ 4 := by
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Complex.ofReal_neg]
      ring
    rw [he, LiZhongQC.b33_d_mobiusFn_neg, hfour]

/-- Same original source point gives equality of the full automorphic-function submodules. -/
theorem sourceAutomorphicQD_eq_of_samePoint (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν')) :
    LiZhongQC.automorphicQD (deformedGroup hΓ ν) =
      LiZhongQC.automorphicQD (deformedGroup hΓ ν') := by
  ext φ
  constructor
  · intro hφ
    refine ⟨hφ.1, hφ.2.1, ?_⟩
    intro B hB z hz
    obtain ⟨A, hA, hact⟩ :=
      deformedGroup_actions_of_samePoint hΓ hdense ν' ν hpoint.symm B hB
    change φ (LiZhongQC.mobiusFn (B 0 0) (B 0 1) (B 1 0) (B 1 1) z) /
      ((B 1 0 : ℂ) * z + B 1 1) ^ 4 = φ z
    rw [automorphicPullback_eq_of_same_action hact φ z]
    exact hφ.2.2 A hA z hz
  · intro hφ
    refine ⟨hφ.1, hφ.2.1, ?_⟩
    intro A hA z hz
    obtain ⟨B, hB, hact⟩ :=
      deformedGroup_actions_of_samePoint hΓ hdense ν ν' hpoint A hA
    change φ (LiZhongQC.mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) z) /
      ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = φ z
    rw [automorphicPullback_eq_of_same_action hact φ z]
    exact hφ.2.2 B hB z hz

/-- The faithful weighted submodules are equal through the same literal decoding map. -/
theorem weightedAutomorphicSubmodule_eq_of_samePoint (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν')) :
    BersWeighted.automorphicSubmodule (deformedGroup hΓ ν) =
      BersWeighted.automorphicSubmodule (deformedGroup hΓ ν') := by
  unfold BersWeighted.automorphicSubmodule
  rw [sourceAutomorphicQD_eq_of_samePoint hΓ hdense ν ν' hpoint]

/-- The same-point deformed Bers identification is the identity on actual weighted vectors. -/
def deformedBersEquiv (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν')) :
    BersWeighted.Automorphic (deformedGroup hΓ ν) ≃L[ℂ]
      BersWeighted.Automorphic (deformedGroup hΓ ν') :=
  ContinuousLinearEquiv.ofEq _ _
    (weightedAutomorphicSubmodule_eq_of_samePoint hΓ hdense ν ν' hpoint)

@[simp] theorem deformedBersEquiv_val (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν'))
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) :
    (deformedBersEquiv hΓ hdense ν ν' hpoint φ).val = φ.val :=
  LinearEquiv.coe_ofEq_apply
    (weightedAutomorphicSubmodule_eq_of_samePoint hΓ hdense ν ν' hpoint) φ

/-- The identity identification preserves the complete canonically extended function. -/
theorem deformedBersEquiv_toSource (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν'))
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) :
    ((deformedBersEquiv hΓ hdense ν ν' hpoint φ).toSource : ℂ → ℂ) =
      (φ.toSource : ℂ → ℂ) := by
  change BersWeighted.decode (deformedBersEquiv hΓ hdense ν ν' hpoint φ).val =
    BersWeighted.decode φ.val
  rw [deformedBersEquiv_val]

/-- The actual original weighted norms agree exactly. -/
theorem norm_deformedBersEquiv (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν'))
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) :
    ‖deformedBersEquiv hΓ hdense ν ν' hpoint φ‖ = ‖φ‖ := by
  change ‖(deformedBersEquiv hΓ hdense ν ν' hpoint φ).val‖ = ‖φ.val‖
  rw [deformedBersEquiv_val]

/-- The actual same-point deformed Bers identification is an isometry. -/
theorem isometry_deformedBersEquiv (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν')) :
    Isometry (deformedBersEquiv hΓ hdense ν ν' hpoint) := by
  apply Isometry.of_dist_eq
  intro φ ψ
  change dist (deformedBersEquiv hΓ hdense ν ν' hpoint φ).val
      (deformedBersEquiv hΓ hdense ν ν' hpoint ψ).val = dist φ.val ψ.val
  rw [deformedBersEquiv_val, deformedBersEquiv_val]

/-- The entire actual coordinate map is natural for the true same-point identity identification. -/
theorem deformedBersEquiv_bersTranslation (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν'))
    (φ : BersWeighted.Automorphic Γ) :
    deformedBersEquiv hΓ hdense ν ν' hpoint (bersTranslation hΓ ν φ) =
      bersTranslation hΓ ν' φ := by
  apply BersWeighted.Automorphic.toSource_injective
  apply Subtype.ext
  rw [deformedBersEquiv_toSource, bersTranslation_toSource, bersTranslation_toSource]
  have hχ := sourceBersTranslation_eq_of_sameBoundary (toSourceGamma ν).val
    (toSourceGamma ν').val (Quotient.exact hpoint)
  exact congrFun hχ (φ.toSource : ℂ → ℂ)

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)

/-- Actual original marked-surface point equality gives the identity isometric Bers identification. -/
def nativePointDeformedBersEquiv (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν') :
    BersWeighted.Automorphic (deformedGroup hΓ ν) ≃L[ℂ]
      BersWeighted.Automorphic (deformedGroup hΓ ν') :=
  deformedBersEquiv hΓ (native_fixedPoints_dense R hp) ν ν'
    (sourcePoint_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint)

@[simp] theorem nativePointDeformedBersEquiv_val (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν')
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) :
    (nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint φ).val = φ.val :=
  deformedBersEquiv_val hΓ (native_fixedPoints_dense R hp) ν ν' _ φ

/-- The original-point identification preserves the actual weighted norm. -/
theorem norm_nativePointDeformedBersEquiv (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν')
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) :
    ‖nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint φ‖ = ‖φ‖ :=
  norm_deformedBersEquiv hΓ (native_fixedPoints_dense R hp) ν ν' _ φ

/-- Same original marked-surface point gives naturality for every original Bers input. -/
theorem nativePointDeformedBersEquiv_bersTranslation (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν')
    (φ : BersWeighted.Automorphic Γ) :
    nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
        (bersTranslation hΓ ν φ) =
      bersTranslation hΓ ν' φ :=
  deformedBersEquiv_bersTranslation hΓ (native_fixedPoints_dense R hp) ν ν' _ φ

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
