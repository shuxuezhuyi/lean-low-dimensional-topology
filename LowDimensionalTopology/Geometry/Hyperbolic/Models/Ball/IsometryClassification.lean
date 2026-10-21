/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Basic
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.Subgroup

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Isometry
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.TranslationCoordinates

@[expose] public section

open Set
open scoped RealInnerProductSpace OnePoint

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- A Lorentz linear map fixing the time unit acts orthogonally on spatial coordinates. -/
theorem lorentzLinearMap_spatial_of_fix_timeUnit {n : ℕ}
    (T : LorentzVector n →ₗ[ℝ] LorentzVector n)
    (hT : ∀ x y, lorentzForm (T x) (T y) = lorentzForm x y)
    (h0 : T (lorentzTimeUnit n) = lorentzTimeUnit n) :
    ∃ L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n, ∀ x, T x = (x.1, L x.2) := by
  let S : Inversive.Euclidean n →ₗ[ℝ] Inversive.Euclidean n :=
    (LinearMap.snd ℝ ℝ (Inversive.Euclidean n)).comp
      (T.comp (LinearMap.inr ℝ ℝ (Inversive.Euclidean n)))
  have ht (v : Inversive.Euclidean n) : (T (0, v)).1 = 0 := by
    have he := hT (0, v) (lorentzTimeUnit n)
    rw [h0] at he
    simpa [lorentzForm, lorentzTimeUnit] using he
  have he (r : ℝ) : T (r, 0) = (r, 0) := by
    have hs := T.map_smul r (lorentzTimeUnit n)
    rw [h0] at hs
    simpa [lorentzTimeUnit] using hs
  have hfull (x : LorentzVector n) : T x = (x.1, S x.2) := by
    have hx : x = (x.1, 0) + (0, x.2) := by simp
    conv_lhs => rw [hx, map_add, he]
    apply Prod.ext
    · simp [ht]
    · simp [S]
  have hn (v : Inversive.Euclidean n) : ‖S v‖ = ‖v‖ := by
    have hq := hT (0, v) (0, v)
    rw [hfull] at hq
    simp only [lorentzForm, zero_mul, real_inner_self_eq_norm_sq] at hq
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)
  let I : Inversive.Euclidean n →ₗᵢ[ℝ] Inversive.Euclidean n := { toLinearMap := S, norm_map' := hn }
  let L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n :=
    LinearIsometryEquiv.ofSurjective I (LinearMap.surjective_of_injective I.injective)
  exact ⟨L, hfull⟩

def ballHyperboloidLift {n : ℕ} (f : unitBallDomain n → unitBallDomain n) :
    Hyperboloid n → Hyperboloid n := fun x => ballHyperboloid (f (hyperboloidProject x))

theorem ballHyperboloidLift_preserves_form {n : ℕ}
    (f : unitBallDomain n → unitBallDomain n)
    (hf : ∀ x y, (ballDensity n).pathDist (f x) (f y) = (ballDensity n).pathDist x y)
    (x y : Hyperboloid n) :
    lorentzForm (ballHyperboloidLift f x).val (ballHyperboloidLift f y).val =
      lorentzForm x.val y.val := by
  rw [← hyperboloidPathDist_cosh, ← hyperboloidPathDist_cosh,
    hyperboloidPathDist_eq_ballPathDist, hyperboloidPathDist_eq_ballPathDist]
  simp only [ballHyperboloidLift, hyperboloidProject_ballHyperboloid, hf]

/-- The origin-fixing case needs no preassigned continuity or surjectivity. -/
theorem ball_pathDist_preserver_fix_origin_orthogonal {n : ℕ}
    (f : unitBallDomain n → unitBallDomain n)
    (hf : ∀ x y, (ballDensity n).pathDist (f x) (f y) = (ballDensity n).pathDist x y)
    (h0 : f (ballOrigin n) = ballOrigin n) :
    ∃ L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n, ∀ x, (f x).val = L x.val := by
  let F := ballHyperboloidLift f
  have hF := ballHyperboloidLift_preserves_form f hf
  let q0 : Hyperboloid n := ⟨lorentzTimeUnit n, lorentzTimeUnit_mem n⟩
  have hp0 : hyperboloidProject q0 = ballOrigin n := by
    apply Subtype.ext
    simp [hyperboloidProject, hyperboloidProjectRaw, q0, lorentzTimeUnit, ballOrigin]
  have ht0 : hyperboloidFrameExtension F (lorentzTimeUnit n) = lorentzTimeUnit n := by
    rw [show lorentzTimeUnit n = q0.val from rfl, hyperboloidFrameExtension_eq F hF q0]
    change (ballHyperboloid (f (hyperboloidProject q0))).val = _
    rw [hp0, h0]
    simp [ballHyperboloid, ballHyperboloidRaw, ballOrigin, q0, lorentzTimeUnit]
  obtain ⟨L, hL⟩ := lorentzLinearMap_spatial_of_fix_timeUnit (hyperboloidFrameExtension F)
    (hyperboloidFrameExtension_preserves_form F hF) ht0
  refine ⟨L, fun x => ?_⟩
  let q := ballHyperboloid x
  have hq : hyperboloidFrameExtension F q.val = (ballHyperboloid (f x)).val := by
    simpa only [F, ballHyperboloidLift, q, hyperboloidProject_ballHyperboloid] using
      hyperboloidFrameExtension_eq F hF q
  calc
    (f x).val = hyperboloidProjectRaw (ballHyperboloid (f x)).val :=
      (congrArg Subtype.val (hyperboloidProject_ballHyperboloid (f x))).symm
    _ = hyperboloidProjectRaw (hyperboloidFrameExtension F q.val) := congrArg _ hq.symm
    _ = L (hyperboloidProjectRaw q.val) := by
      rw [hL]
      simp only [hyperboloidProjectRaw, L.map_smul]
    _ = L x.val := congrArg L (congrArg Subtype.val (hyperboloidProject_ballHyperboloid x))

/-- Every distance-preserving map of the actual hyperbolic ball has an actual Möbius realization. -/
theorem ball_pathDist_preserver_exists_mobius {n : ℕ}
    (f : unitBallDomain (n + 1) → unitBallDomain (n + 1))
    (hf : ∀ x y, (ballDensity (n + 1)).pathDist (f x) (f y) =
      (ballDensity (n + 1)).pathDist x y) :
    ∃ g : Inversive.ballPreservingSubgroup n, ∀ x, ballHomeomorph g.val.val g.property x = f x := by
  let a := f (ballOrigin (n + 1))
  let F : unitBallDomain (n + 1) → unitBallDomain (n + 1) :=
    fun x => Inversive.pureTranslationBallHomeomorph a (f x)
  have hF : ∀ x y, (ballDensity (n + 1)).pathDist (F x) (F y) =
      (ballDensity (n + 1)).pathDist x y := by
    intro x y
    exact (Inversive.pureTranslation_pathDist a (f x) (f y)).trans (hf x y)
  have hF0 : F (ballOrigin (n + 1)) = ballOrigin (n + 1) :=
    pureTranslationBallHomeomorph_self a
  obtain ⟨L, hL⟩ := ball_pathDist_preserver_fix_origin_orthogonal F hF hF0
  let g : Inversive.ballPreservingSubgroup n := (Inversive.pureTranslationBall a)⁻¹ * Inversive.orthogonalBallMap L
  refine ⟨g, fun x => ?_⟩
  apply Subtype.ext
  apply OnePoint.coe_injective
  have hB : Inversive.PreservesUnitBall g.val.val := g.property
  refine (ballHomeomorph_coe g.val.val hB x).trans ?_
  change (Inversive.pureTranslation a)⁻¹ ((Inversive.orthogonalBallMap L).val.val (x.val : Inversive.ExtendedEuclidean
    (n + 1))) = _
  rw [Inversive.orthogonalBallMap_coe, Inversive.cartanLinearExtensionHom_coe]
  have hp : Inversive.pureTranslation a (f x).val = (L x.val : Inversive.ExtendedEuclidean (n + 1)) :=
    (ballHomeomorph_coe (Inversive.pureTranslation a) (Inversive.pureTranslation_preservesUnitBall a) (f x)).symm.trans
      (congrArg OnePoint.some (hL x))
  rw [← hp]
  exact (Inversive.pureTranslation a).symm_apply_apply _

abbrev IsBallIsometry {n : ℕ} (f : unitBallDomain n → unitBallDomain n) : Prop :=
  @Isometry (unitBallDomain n) (unitBallDomain n)
    (ballMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace
    (ballMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace f

theorem isBallIsometry_iff_pathDist {n : ℕ} (f : unitBallDomain n → unitBallDomain n) :
    IsBallIsometry f ↔ ∀ x y, (ballDensity n).pathDist (f x) (f y) =
      (ballDensity n).pathDist x y := by
  rw [IsBallIsometry, @isometry_iff_dist_eq (unitBallDomain n) (unitBallDomain n)
    (ballMetricSpace n).toPseudoMetricSpace (ballMetricSpace n).toPseudoMetricSpace]
  simp only [ballMetricSpace_dist]

theorem ball_isometry_exists_mobius {n : ℕ}
    (f : unitBallDomain (n + 1) → unitBallDomain (n + 1)) (hf : IsBallIsometry f) :
    ∃ g : Inversive.ballPreservingSubgroup n, ∀ x, ballHomeomorph g.val.val g.property x = f x :=
  ball_pathDist_preserver_exists_mobius f ((isBallIsometry_iff_pathDist f).mp hf)

theorem ball_pathDist_preserver_surjective {n : ℕ}
    (f : unitBallDomain (n + 1) → unitBallDomain (n + 1))
    (hf : ∀ x y, (ballDensity (n + 1)).pathDist (f x) (f y) =
      (ballDensity (n + 1)).pathDist x y) : Function.Surjective f := by
  obtain ⟨g, hg⟩ := ball_pathDist_preserver_exists_mobius f hf
  have he : (ballHomeomorph g.val.val g.property : unitBallDomain (n + 1) →
      unitBallDomain (n + 1)) = f := funext hg
  rw [← he]
  exact (ballHomeomorph g.val.val g.property).surjective

theorem ball_isometry_surjective {n : ℕ}
    (f : unitBallDomain (n + 1) → unitBallDomain (n + 1)) (hf : IsBallIsometry f) :
    Function.Surjective f :=
  ball_pathDist_preserver_surjective f ((isBallIsometry_iff_pathDist f).mp hf)

end
end LowDimensionalTopology.Geometry.Hyperbolic
