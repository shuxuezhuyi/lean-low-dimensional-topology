module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedCoefficientMap
public import LowDimensionalTopology.Geometry.Teichmuller.BersWeightedCoordinates
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge

/-!
# Compact uniformization and dimension for the actual normalized deformed group

The original compact surface and normalized solution construct an actual marked
Riemann surface with a holomorphic covering. Its covering map is retained while
both normalized conjugacy laws identify its fibres with the exact chosen
deformed matrix group. The marking transports the original genus. Actual
quadratic-differential theory then supplies finite coordinates for all native
weighted automorphic forms of this same group, in their original norm.

The analytic deformation and quadratic-differential results are reused from
Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open Surfaces GammaMeasurableBeltrami

universe u

private theorem upper_conjugacy_of_planar
    {Γ : Subgroup Deck} (ν : Ball Γ) (F : ℍ ≃ₜ ℍ)
    (hF : ∀ z : ℍ, (F z : ℂ) = normalizedMap ν z)
    (γ δ : Deck)
    (hrel : ∀ z ∈ LiZhongQC.upperHalf,
      normalizedMap ν (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        LiZhongQC.mobiusFn (δ 0 0) (δ 0 1) (δ 1 0) (δ 1 1) (normalizedMap ν z)) :
    ∀ z : ℍ, F (γ • z) = δ • F z := by
  intro z
  apply UpperHalfPlane.ext
  simpa only [hF, LiZhongQC.h23l_b_coe_smul, LiZhongQC.mobiusFn] using
    hrel (z : ℂ) z.coe_im_pos

private theorem uniformization_exact_deformedGroup
    {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ)
    {p : ℍ → X} (hp : LiZhongQC.IsUniformization Γ p)
    (ν : Ball Γ) (e : X ≃ₜ Y) (F : ℍ ≃ₜ ℍ)
    (hF : ∀ z : ℍ, (F z : ℂ) = normalizedMap ν z)
    (hU : LiZhongQC.IsUniformization (LiZhongQC.s27u_conjGroup Γ F)
      (LiZhongQC.s27u_proj p e F)) :
    LiZhongQC.IsUniformization (deformedGroup hΓ ν) (LiZhongQC.s27u_proj p e F) := by
  refine ⟨hU.1, hU.2.1, hU.2.2.1, fun z w => ?_⟩
  change e (p (F.symm z)) = e (p (F.symm w)) ↔ _
  rw [e.injective.eq_iff, hp.2.2.2]
  constructor
  · rintro ⟨γ, hγ, hγz⟩
    obtain ⟨δ, hδ, hrel⟩ := (deformedGroup_spec hΓ ν).2.1 γ hγ
    have hact := upper_conjugacy_of_planar ν F hF γ δ hrel (F.symm z)
    rw [hγz, F.apply_symm_apply, F.apply_symm_apply] at hact
    exact ⟨δ, hδ, hact.symm⟩
  · rintro ⟨δ, hδ, hδz⟩
    obtain ⟨γ, hγ, hrel⟩ := (deformedGroup_spec hΓ ν).2.2 δ hδ
    refine ⟨γ, hγ, ?_⟩
    apply F.injective
    have hact := upper_conjugacy_of_planar ν F hF γ δ hrel (F.symm z)
    rw [F.apply_symm_apply, hδz] at hact
    rw [F.apply_symm_apply]
    exact hact

/-- The actual normalized coefficient produces an actual compact marked target
of the same genus. The exact chosen deformed group uniformizes that target by
the original covering transported through the same normalized upper map. -/
theorem exists_deformed_uniformization
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (ν : Ball Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ (Y : LiZhongQC.ClosedRS.{u}) (e : X ≃ₜ Y.carrier),
      LiZhongQC.IsKQCRS e ((1 + ‖ν.val.val‖) / (1 - ‖ν.val.val‖)) ∧
      LiZhongQC.IsUniformization (deformedGroup hΓ ν)
        (fun z => e (p ((normalizedUpperEquiv ν).symm z))) ∧
      LiZhongQC.HasGenus Y.carrier g := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let μ := planeRepresentative ν.val.val
  have hk0 : 0 ≤ ‖ν.val.val‖ := norm_nonneg _
  have hk : ‖ν.val.val‖ < 1 := Ball.norm_lt_one ν
  have hμ : LiZhongQC.IsBeltramiCoeff μ LiZhongQC.upperHalf ‖ν.val.val‖ :=
    planeRepresentative_isBeltramiCoeff ν.val.val
  have hcompat : LiZhongQC.IsGammaCompatible Γ μ :=
    planeRepresentative_isGammaCompatible ν.val
  obtain ⟨_, hN, hwK, _⟩ := LiZhongQC.s27u_sym_spec hk0 hk hμ
  obtain ⟨hwU, _, _, hwKU, _⟩ := LiZhongQC.s27u_fSym_upperHalf hk0 hk hμ
  obtain ⟨F, hF⟩ := LiZhongQC.s27u_homeo_upper hwK hN.2.1 hwU
  obtain ⟨Y, e, hhol⟩ := LiZhongQC.s27v_xmu_exists hp hk0 hk hμ hcompat hF
  have hU := LiZhongQC.s27v_isUniformization hp hk0 hk hμ hcompat hF e hhol
  have hL : LiZhongQC.IsLift p (LiZhongQC.s27u_proj p e F) e F := by
    intro z
    change e (p (F.symm (F z))) = e (p z)
    rw [F.symm_apply_apply]
  have hFeq : EqOn (LiZhongQC.liftToC F) (LiZhongQC.s27u_fSym μ)
      LiZhongQC.upperHalf := by
    intro z hz
    rw [LiZhongQC.h23l_liftToC_eq F hz, UpperHalfPlane.ofComplex_apply_of_im_pos
      (show 0 < z.im from hz)]
    exact hF _
  have hFQC : LiZhongQC.IsKQC (LiZhongQC.liftToC F) LiZhongQC.upperHalf
      ((1 + ‖ν.val.val‖) / (1 - ‖ν.val.val‖)) :=
    LiZhongQC.ad_isKQC_congr hwKU hFeq
  have heQC := LiZhongQC.s27v_isKQCRS_of_lift hp hU hL hFQC
  have hFnative : ∀ z : ℍ, (F z : ℂ) = normalizedMap ν z := by
    intro z
    simpa only [LiZhongQC.s33v_fSym_eq, normalizedMap, μ] using hF z
  have hExact := uniformization_exact_deformedGroup hΓ hp ν e F hFnative hU
  have hEquiv : F.toEquiv = normalizedUpperEquiv ν := by
    apply Equiv.ext
    intro z
    apply UpperHalfPlane.ext
    exact hFnative z
  have hInv (z : ℍ) : F.symm z = (normalizedUpperEquiv ν).symm z := by
    change F.toEquiv.symm z = (normalizedUpperEquiv ν).symm z
    rw [hEquiv]
  have hproj : (fun z => e (p ((normalizedUpperEquiv ν).symm z))) =
      LiZhongQC.s27u_proj p e F := by
    funext z
    change e (p ((normalizedUpperEquiv ν).symm z)) = e (p (F.symm z))
    rw [hInv]
  refine ⟨Y, e, heQC, ?_, ?_⟩
  · rw [hproj]
    exact hExact
  · exact LiZhongQC.hasGenus_of_homeomorph (R.hasSourceGenus hgenus) e

/-- Actual compact-surface quadratic theory supplies all-source coordinates
and finite Bers norm for the exact normalized deformed group. -/
theorem exists_deformed_source_coordinates
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (ν : Ball Γ) :
    ∃ _e : LiZhongQC.automorphicQD (deformedGroup hΓ ν) ≃L[ℂ]
        (Fin (3 * g - 3) → ℂ),
      ∀ φ : LiZhongQC.automorphicQD (deformedGroup hΓ ν),
        LiZhongQC.bersNormL (φ : ℂ → ℂ) < ⊤ := by
  obtain ⟨Y, _e, _heQC, hYuniformization, hYgenus⟩ :=
    exists_deformed_uniformization R hgenus hΓ hp ν
  obtain ⟨e, hfinite, _, _⟩ := LiZhongQC.s34m_coords hg hYgenus
    (deformedGroup_spec hΓ ν).1 hYuniformization
  exact ⟨e, hfinite⟩

/-- The actual source automorphic quadratic forms of the same chosen group
have complex dimension determined by the original genus. -/
theorem deformed_source_finrank
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (ν : Ball Γ) :
    Module.finrank ℂ (LiZhongQC.automorphicQD (deformedGroup hΓ ν)) = 3 * g - 3 := by
  obtain ⟨e, _⟩ := exists_deformed_source_coordinates R hg hgenus hΓ hp ν
  simpa only [Module.finrank_fin_fun] using e.toLinearEquiv.finrank_eq

/-- Genuine finite coordinates on the unchanged native weighted automorphic
space of the exact normalized deformed group. No dimension input is supplied. -/
def deformedWeightedCoordinates
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (ν : Ball Γ) :
    BersWeighted.Automorphic (deformedGroup hΓ ν) ≃L[ℂ] (Fin (3 * g - 3) → ℂ) := by
  let L := Classical.choose (exists_deformed_source_coordinates R hg hgenus hΓ hp ν)
  have hfinite := Classical.choose_spec (exists_deformed_source_coordinates R hg hgenus hΓ hp ν)
  let e : BersWeighted.Automorphic (deformedGroup hΓ ν) ≃ₗ[ℂ]
      (Fin (3 * g - 3) → ℂ) :=
    (BersWeighted.sourceEquivOfFiniteNorm (deformedGroup hΓ ν) hfinite).trans L.toLinearEquiv
  have : FiniteDimensional ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν)) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  exact e.toContinuousLinearEquiv

/-- The same original weighted automorphic space is genuinely finite dimensional. -/
theorem deformed_weighted_finiteDimensional
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (ν : Ball Γ) :
    FiniteDimensional ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν)) := by
  let e := deformedWeightedCoordinates R hg hgenus hΓ hp ν
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- The exact deformed group has the original complex dimension in the native weighted norm. -/
theorem deformed_weighted_finrank
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (ν : Ball Γ) :
    Module.finrank ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν)) = 3 * g - 3 := by
  let e := deformedWeightedCoordinates R hg hgenus hΓ hp ν
  simpa only [Module.finrank_fin_fun] using e.toLinearEquiv.finrank_eq

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
