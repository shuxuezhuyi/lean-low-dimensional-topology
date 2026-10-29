module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonIntegral
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Inner product induced by the actual weighted quadratic integral

The integral pairing is complex linear in its first slot. Mathlib's inner product
is conjugate linear in its first slot, so the two slots are exchanged below.
The norm and inner product are explicit data depending on the actual covering
and integration region. No competing global norm instance is installed.

This is a complete finite-dimensional inner product space for a fixed compact
region with nonempty interior. Independence of a fundamental domain and variation
over Teichmuller space are separate questions.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : IsCompact F) (hFne : (interior F).Nonempty)

/-- Positive definiteness and every sesquilinear law come from the actual
weighted integral of original-atlas global holomorphic quadratic differentials. -/
@[instance_reducible]
def nativeQuadraticInnerCore :
    InnerProductSpace.Core ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) where
  inner q r := nativeQuadraticPairing R.toRiemannAtlas p F r q
  conj_inner_symm q r := nativeQuadraticPairing_conj R.toRiemannAtlas p F q r
  re_inner_nonneg q :=
    quadraticPairing_self_nonneg F (liftQuadratic R.toRiemannAtlas p q)
  add_left q r s := nativeQuadraticPairing_add_right R p hp F hF s q r
  smul_left q r a := nativeQuadraticPairing_smul_right R.toRiemannAtlas p F a r q
  definite q h := (nativeQuadraticPairing_self_eq_zero_iff R p hp F hF hFne q).1 h

/-- The genuine normed additive group whose norm is derived from this integral. -/
@[instance_reducible]
def nativeQuadraticNormedAddCommGroup :
    NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) := by
  let : InnerProductSpace.Core ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    nativeQuadraticInnerCore R p hp F hF hFne
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

/-- The actual inner product structure for the integral-induced norm. -/
@[instance_reducible]
def nativeQuadraticInnerProductSpace :
    let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
      nativeQuadraticNormedAddCommGroup R p hp F hF hFne
    InnerProductSpace ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) := by
  let : InnerProductSpace.Core ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    nativeQuadraticInnerCore R p hp F hF hFne
  let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    nativeQuadraticNormedAddCommGroup R p hp F hF hFne
  exact InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ
      (HolomorphicQuadraticDifferential R.toRiemannAtlas))

/-- The constructed Mathlib inner product is precisely the actual integral,
with the slots exchanged to match the conjugate-first convention. -/
theorem nativeQuadraticInner_eq (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
      nativeQuadraticNormedAddCommGroup R p hp F hF hFne
    let : InnerProductSpace ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
      nativeQuadraticInnerProductSpace R p hp F hF hFne
    inner ℂ q r = nativeQuadraticPairing R.toRiemannAtlas p F r q := by
  rfl

/-- The norm is the square root of the actual integral diagonal. -/
theorem nativeQuadraticNorm_eq_sqrt
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
      nativeQuadraticNormedAddCommGroup R p hp F hF hFne
    ‖q‖ = Real.sqrt (nativeQuadraticPairing R.toRiemannAtlas p F q q).re := by
  rfl

/-- Squaring the induced norm recovers exactly the actual positive diagonal. -/
theorem nativeQuadraticNorm_sq
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
      nativeQuadraticNormedAddCommGroup R p hp F hF hFne
    ‖q‖ ^ 2 = (nativeQuadraticPairing R.toRiemannAtlas p F q q).re := by
  let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    nativeQuadraticNormedAddCommGroup R p hp F hF hFne
  change ‖q‖ ^ 2 = (nativeQuadraticPairing R.toRiemannAtlas p F q q).re
  rw [nativeQuadraticNorm_eq_sqrt R p hp F hF hFne]
  exact Real.sq_sqrt
    (quadraticPairing_self_nonneg F (liftQuadratic R.toRiemannAtlas p q))

/-- The norm-square is the literal y^2 weighted Lebesgue integral. -/
theorem nativeQuadraticNorm_sq_integral
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
      nativeQuadraticNormedAddCommGroup R p hp F hF hFne
    ‖q‖ ^ 2 = ∫ z in F, z.im ^ 2 * ‖liftQuadratic R.toRiemannAtlas p q z‖ ^ 2 ∂flatArea := by
  let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    nativeQuadraticNormedAddCommGroup R p hp F hF hFne
  change ‖q‖ ^ 2 = ∫ z in F,
    z.im ^ 2 * ‖liftQuadratic R.toRiemannAtlas p q z‖ ^ 2 ∂flatArea
  rw [nativeQuadraticNorm_sq R p hp F hF hFne]
  change (weightedPairing (flatArea.restrict F) (fun z => z.im ^ 2)
    (liftQuadratic R.toRiemannAtlas p q) (liftQuadratic R.toRiemannAtlas p q)).re = _
  rw [weightedPairing_self, Complex.ofReal_re]

/-- Completeness is derived from the already proved finite-dimensionality of
actual global holomorphic quadratic differentials on the closed surface. -/
theorem nativeQuadratic_completeSpace :
    @CompleteSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas)
      (nativeQuadraticNormedAddCommGroup R p hp F hF hFne).toMetricSpace.toUniformSpace := by
  let G := nativeQuadraticNormedAddCommGroup R p hp F hF hFne
  let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) := G
  let : MetricSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas) := G.toMetricSpace
  let : UniformSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    G.toMetricSpace.toUniformSpace
  let : TopologicalSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    G.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : IsUniformAddGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    G.toSeminormedAddCommGroup.to_isUniformAddGroup
  let : InnerProductSpace ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    nativeQuadraticInnerProductSpace R p hp F hF hFne
  let : FiniteDimensional ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    R.finiteDimensional_holomorphicQuadraticDifferential
  exact FiniteDimensional.complete ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas)

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson
