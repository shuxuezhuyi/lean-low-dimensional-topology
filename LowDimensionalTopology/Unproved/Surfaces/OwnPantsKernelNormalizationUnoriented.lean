module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.PantsNielsenExtension
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenOriginalRegion
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Data.Fintype.Fin

/-! Explicit geometric premise: normalization of ONE original pants' OWN extension.
The input cuff labels are unparameterized sets. Coherent peripheral directions
are chosen existentially; no input curve is fixed pointwise or given an orientation.
There is no comparison between two pants and no uniqueness/isometry conclusion. -/

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Unproved.Surfaces
open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions

/-- Concrete classical normalization of one exact original chosen-lift kernel.
It produces the original extension model and its three intrinsic cuffs, then
normalizes ANY ordering of those unoriented cuff labels. Their full lengths and
ranges are preserved while their coherent orientations are chosen internally.
This concrete geometric premise is not proved by this definition. -/
def OwnPantsKernelNormalizationUnoriented
    {X : Type} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (P : Set X)
    (_hP : IsHyperbolicPairOfPants M P) (z : M.discCover ⁻¹' P) : Prop :=
  let E := PantsNielsenExtension M P z
  let R_E := pantsNielsenExtensionRiemannSurface M P z
  let C := pantsNielsenKernel M P z
  ∃ B : HyperbolicSurfaceModel R_E,
    B.group = pantsNielsenStabilizer M P z ∧
    (∀ w : ℍ, B.halfPlaneCover w =
      mobiusDomainProjection (pantsNielsenExtensionDomain M P z)
        (discFiniteHomeomorph.symm (halfPlaneToDisc w))) ∧
    (∃ L : Fin 3 → Set E, Function.Injective L ∧
      range L = {T | ∃ x ∈ frontier C, connectedComponentIn (frontier C) x = T} ∧
      ∀ i, ∃ b : OriginalClosedGeodesic B,
        Function.Injective (b.periodic.lift : AddCircle (1 : ℝ) → E) ∧
          range b.curve = L i) ∧
    ∀ (L : Fin 3 → Set E) (a : Fin 3 → ENNReal),
      Function.Injective L →
      range L = {T | ∃ x ∈ frontier C, connectedComponentIn (frontier C) x = T} →
      (∀ i, ∃ b : OriginalClosedGeodesic B,
        Function.Injective (b.periodic.lift : AddCircle (1 : ℝ) → E) ∧
          range b.curve = L i ∧ b.length = a i) →
      ∃ (N : HyperbolicSurfaceModel R_E)
        (S D A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (κ : ℝ)
        (e : FreeGroup (Fin 2) ≃* N.group)
        (F : FuchsianDisc N.group) (hNE : IsNonElementary N.group)
        (q : Fin 3 → OriginalClosedGeodesic N),
        (∀ w : ℍ, N.halfPlaneCover w = B.halfPlaneCover (S • w)) ∧
        N.group = subgroupConjugate
          (cayleyMobius * realSLMobius S * cayleyMobius⁻¹)⁻¹ B.group ∧
        1 < κ ∧ D.val = !![κ⁻¹, 0; 0, κ] ∧
        A 0 0 + A 0 1 = A 1 0 + A 1 1 ∧ 1 < A 1 0 + A 1 1 ∧
        0 < A 1 0 ∧ 0 < -(A 0 1) / A 1 0 ∧ -(A 0 1) / A 1 0 < 1 ∧
        0 < Matrix.trace A.val ∧ Matrix.trace (A * D).val < 0 ∧
        (e (FreeGroup.of (0 : Fin 2))).val =
          cayleyMobius * realSLMobius D * cayleyMobius⁻¹ ∧
        (e (FreeGroup.of (1 : Fin 2))).val =
          cayleyMobius * realSLMobius A * cayleyMobius⁻¹ ∧
        N.group = Subgroup.closure
          {cayleyMobius * realSLMobius D * cayleyMobius⁻¹,
           cayleyMobius * realSLMobius A * cayleyMobius⁻¹} ∧
        (∀ i, range (q i).curve = L i ∧ (q i).length = a i ∧
          Function.Injective ((q i).periodic.lift : AddCircle (1 : ℝ) → E) ∧
          (∀ w : ℍ, N.halfPlaneCover ((![D, A, (A * D)⁻¹] i) • w) = N.halfPlaneCover w) ∧
          4 < (Matrix.trace (![D, A, (A * D)⁻¹] i).val) ^ 2 ∧
          LiZhongQC.Covers N.halfPlaneCover (![D, A, (A * D)⁻¹] i) (q i).toLoop) ∧
        IsHyperbolicPairOfPants N C ∧ F.carrier = extendedUnitDisc ∧
        N.homeomorph '' C =
          mobiusDomainProjection (unitDiscMobiusInvariantDomain N.group N.invariant) ''
            (Subtype.val ⁻¹' F.nielsenRegion hNE)

end LowDimensionalTopology.Unproved.Surfaces
