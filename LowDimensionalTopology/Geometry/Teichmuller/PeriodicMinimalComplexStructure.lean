module

public import LowDimensionalTopology.Geometry.Teichmuller.ConditionalEllipticFiniteOrder

/-!
# A minimizing structure in a periodic homotopy class

A QC representative homotopic to an actual finite-order homeomorphism has
finite order in the actual QC homotopy quotient. Cyclic Nielsen realization
then gives an elliptic class and a jointly minimizing complex structure on
the original smooth oriented carrier.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Surfaces LiZhongQC
open LowDimensionalTopology.Unproved.Teichmuller

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)

local notation "AutR" =>
  @SourceQCModular.Aut X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold

private theorem isOfFinOrder_mk_of_homotopic_periodic_homeomorph
    (a : AutR) (h : X ≃ₜ X)
    (hhom : ContinuousMap.Homotopic (_root_.toContinuousMap a.val)
      (_root_.toContinuousMap h)) (hperiodic : IsOfFinOrder h) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    IsOfFinOrder (SourceQCModular.mk a) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  have hOne : (_root_.toContinuousMap (1 : X ≃ₜ X)) = ContinuousMap.id X := by
    ext x
    exact Homeomorph.one_apply x
  have hMul (u v : X ≃ₜ X) :
      (_root_.toContinuousMap (u * v)) =
        (_root_.toContinuousMap u).comp (_root_.toContinuousMap v) := by
    ext x
    exact Homeomorph.mul_apply u v x
  have hhomQC : ContinuousMap.Homotopic (SourceQCModular.continuousMap a)
      (_root_.toContinuousMap h) := by
    simpa only [SourceQCModular.continuousMap] using hhom
  obtain ⟨n, hn, hpow⟩ := hperiodic.exists_pow_eq_one
  have hpowers (k : ℕ) :
      ContinuousMap.Homotopic (SourceQCModular.continuousMap (a ^ k))
        (_root_.toContinuousMap (h ^ k)) := by
    induction k with
    | zero =>
        simpa only [pow_zero, SourceQCModular.continuousMap_one, hOne] using
          (ContinuousMap.Homotopic.refl (ContinuousMap.id X))
    | succ k ih =>
        simpa only [pow_succ', SourceQCModular.continuousMap_mul, hMul] using hhomQC.comp ih
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨n, hn, ?_⟩
  change ((QuotientGroup.mk' (SourceQCModular.homotopyIdentitySubgroup X)) a) ^ n = 1
  rw [← map_pow]
  change SourceQCModular.mk (a ^ n) = SourceQCModular.mk (1 : AutR)
  apply (SourceQCModular.mk_eq_mk_iff_homotopic (a ^ n) 1).2
  simpa only [hpow, SourceQCModular.continuousMap_one, hOne] using hpowers n

/-- An original positive homeomorphism homotopic to an actual positive periodic
homeomorphism admits a jointly minimizing structure under cyclic Nielsen realization. -/
theorem exists_minimalComplexStructure_of_homotopic_positive_periodic_of_nielsen
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hNielsen : FiniteCyclicNielsenRealization R) (f : X ≃ₜ X)
    (hf : letI := R.toRiemannAtlas.toChartedSpace
      letI := R.toRiemannAtlas.isManifold
      IsOrientationPreservingRS f)
    (hperiodic : letI := R.toRiemannAtlas.toChartedSpace
      letI := R.toRiemannAtlas.isManifold
      ∃ h : X ≃ₜ X, IsOrientationPreservingRS h ∧ IsOfFinOrder h ∧
        ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap h)) :
    ∃ σ : PositiveComplexStructure R, IsMinimalComplexStructure R f σ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨h, _hh, horder, hfh⟩ := hperiodic
  obtain ⟨a, ha, _hcomparison, hexists⟩ :=
    originalHomeomorph_minimizer_comparison R hg hgenus f hf
  have hfinite : IsOfFinOrder (SourceQCModular.mk a) :=
    isOfFinOrder_mk_of_homotopic_periodic_homeomorph R a h (ha.symm.trans hfh) horder
  have helliptic : IsElliptic R (SourceQCModular.mk a) :=
    (isElliptic_iff_isOfFinOrder_of_nielsen R hNielsen hg hgenus (SourceQCModular.mk a)).mpr
      hfinite
  exact hexists.mpr (Or.inl helliptic)

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
