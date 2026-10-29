module

public import LowDimensionalTopology.Geometry.Teichmuller.BersTranslationRecentring
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceChangeDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.SourceFuchsianRegions

/-! Genuine marked target, cover and region witnesses for normalized recentering. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff
namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
open Surfaces GammaMeasurableBeltrami
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ) (ν lam : Ball Γ)
local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "κ" => translatedBall hΓ ν lam
local notation "T" => deformedNativeSurface Y hY hΔ hpY κ
local notation "L" => deformedNativeSurface R hgenus hΓ hp lam
local notation "qT" => deformedTargetCover Y hY hΔ hpY κ
local notation "qL" => deformedTargetCover R hgenus hΓ hp lam
local notation "eν" => deformedTargetMarking R hgenus hΓ hp ν
local notation "eλ" => deformedTargetMarking R hgenus hΓ hp lam
local notation "eκ" => deformedTargetMarking Y hY hΔ hpY κ

/-- The three original chosen markings give the actual comparison homeomorphism. -/
def deformedReferenceTargetHomeomorph :
    (deformedTargetSource Y hY hΔ hpY κ).carrier ≃ₜ
      (deformedTargetSource R hgenus hΓ hp lam).carrier :=
  ((eκ).symm.trans (eν).symm).trans (eλ)
local notation "c" => deformedReferenceTargetHomeomorph R hp hgenus hΓ ν lam

/-- The actual twice-deformed cover is identified by the literal identity lift. -/
theorem deformedReferenceTargetHomeomorph_cover (z : ℍ) : c (qT z) = qL z := by
  have hinv : (normalizedUpperEquiv ν).symm ((normalizedUpperEquiv κ).symm z) =
      (normalizedUpperEquiv lam).symm z := by
    apply (normalizedUpperEquiv lam).injective
    have hc := normalizedUpperEquiv_translatedBall_comp hΓ ν lam
      ((normalizedUpperEquiv ν).symm ((normalizedUpperEquiv κ).symm z))
    have hi : normalizedUpperEquiv lam
        ((normalizedUpperEquiv ν).symm ((normalizedUpperEquiv κ).symm z)) = z := by
      simpa only [Equiv.apply_symm_apply] using hc.symm
    exact hi.trans ((normalizedUpperEquiv lam).apply_symm_apply z).symm
  change (eλ) ((eν).symm ((eκ).symm ((eκ) ((eν)
    (p ((normalizedUpperEquiv ν).symm ((normalizedUpperEquiv κ).symm z))))))) =
      (eλ) (p ((normalizedUpperEquiv lam).symm z))
  simp only [Homeomorph.symm_apply_apply]
  exact congrArg (fun w : ℍ => (eλ) (p w)) hinv

/-- The same actual homeomorphism is analytic in both full native atlas sets. -/
theorem deformedReferenceTargetHomeomorph_analytic :
    RiemannAnalyticMap (T).toRiemannAtlas (L).toRiemannAtlas (c) := by
  let := (T).toRiemannAtlas.toChartedSpace
  let := (L).toRiemannAtlas.toChartedSpace
  let := (T).toRiemannAtlas.isManifold
  let := (L).toRiemannAtlas.isManifold
  have hLift : LiZhongQC.IsLift (qT) (qL) (c) (Homeomorph.refl ℍ) := by
    intro z
    exact (deformedReferenceTargetHomeomorph_cover R hp hgenus hΓ ν lam z).symm
  have hId : LiZhongQC.IsKQC (LiZhongQC.liftToC (Homeomorph.refl ℍ))
      LiZhongQC.upperHalf 1 := by
    apply LiZhongQC.ad_isKQC_congr (LiZhongQC.isKQC_one_of_conformal
      LiZhongQC.isOpen_upperHalf (LiZhongQC.isConformalOnto_id LiZhongQC.upperHalf))
    intro z hz
    rw [LiZhongQC.h23l_liftToC_eq _ hz]
    change (UpperHalfPlane.ofComplex z : ℂ) = z
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
  have hBi := (LiZhongQC.isKQCRS_one_iff (c)).mp
    (LiZhongQC.s27v_isKQCRS_of_lift
      (deformedNativeSurface_uniformization Y hY hΔ hpY κ)
      (deformedNativeSurface_uniformization R hgenus hΓ hp lam) hLift hId)
  have hA := (analyticHomeomorph_ofManifold_iff_sourceBiholomorphic (c)).mpr hBi
  simpa only [RiemannAtlas.ofManifold_toChartedSpace] using hA

/-- Only equality of genuine projective images is used to retain the given region. -/
theorem exists_deformedReferenceTargetRegion
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ lam).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    ∃ P' : Fuchsian.HalfPlaneFuchsianGroup
        ((deformedGroup hΔ κ).map Hyperbolic.realSLMobius),
      Fuchsian.IsHalfPlaneFundamentalRegion P' ((fun z : ℍ => (1 : Deck) • z) ⁻¹' F) := by
  let P' := sourceHalfPlaneFuchsianGroup ((deformedGroup_spec hΔ κ).1)
  refine ⟨P', ?_⟩
  have hRegion := halfPlaneRegion_of_group_eq
    (deformedGroup_translatedBall_projectiveImage hΓ ν lam) P' P hF
  have hpre : ((fun z : ℍ => (1 : Deck) • z) ⁻¹' F) = F := by
    ext z
    simp
  rw [hpre]
  exact hRegion

/-- These are exactly the geometric witnesses used with M=1 in the harmonic law. -/
theorem exists_deformedReferenceGeometricWitness
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ lam).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    ∃ (P' : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΔ κ).map Hyperbolic.realSLMobius))
      (_hF' : Fuchsian.IsHalfPlaneFundamentalRegion P' ((fun z : ℍ => (1 : Deck) • z) ⁻¹' F))
      (c' : (deformedTargetSource Y hY hΔ hpY κ).carrier ≃ₜ
        (deformedTargetSource R hgenus hΓ hp lam).carrier),
      RiemannAnalyticMap (T).toRiemannAtlas (L).toRiemannAtlas c' ∧
        ∀ z : ℍ, c' (qT z) = qL ((1 : Deck) • z) := by
  obtain ⟨P', hF'⟩ := exists_deformedReferenceTargetRegion hΓ ν lam P F hF
  refine ⟨P', hF', c, deformedReferenceTargetHomeomorph_analytic R hp hgenus hΓ ν lam, ?_⟩
  intro z
  simpa only [one_smul] using deformedReferenceTargetHomeomorph_cover R hp hgenus hΓ ν lam z

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
