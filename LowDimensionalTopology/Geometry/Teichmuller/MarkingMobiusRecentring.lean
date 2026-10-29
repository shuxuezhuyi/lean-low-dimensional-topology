module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizerNormalizedComposition
public import LowDimensionalTopology.Geometry.Teichmuller.BersTranslationRecentring
public import LowDimensionalTopology.Geometry.Teichmuller.BersMobiusCoefficientCovariance

/-! Full-image recentering for the original arbitrary QC normalizer action. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
open Surfaces GammaMeasurableBeltrami BersWeighted

private theorem upper_conjugacy {Γ : Subgroup Deck} (ν : Ball Γ) (γ δ : Deck)
    (h : ∀ z ∈ LiZhongQC.upperHalf,
      normalizedMap ν (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        LiZhongQC.mobiusFn (δ 0 0) (δ 0 1) (δ 1 0) (δ 1 1) (normalizedMap ν z))
    (z : ℍ) : normalizedUpperEquiv ν (γ • z) = δ • normalizedUpperEquiv ν z := by
  apply UpperHalfPlane.ext
  simpa only [normalizedUpperEquiv_coe, LiZhongQC.h23l_b_coe_smul,
    LiZhongQC.mobiusFn] using h z z.im_pos

/-- The actual normalized target actions determine the required weighted
submodule equality; independent central signs in SL lifts are allowed. -/
theorem markingRecentring_submodule_eq {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (w : ℍ ≃ₜ ℍ)
    (hw : QCNormalizerModular.NormalizerCondition Γ w) (ν ν' : Ball Γ) (α : Deck)
    (hα : ∀ z : ℍ, normalizedUpperEquiv ν' z =
      α • normalizedUpperEquiv ν (w.symm z)) :
    automorphicSubmodule (deformedGroup hΓ ν) =
      automorphicSubmodule (LiZhongQC.conjGroup (deformedGroup hΓ ν') α⁻¹) := by
  have compare (γ δ A B : Deck)
      (hwγ : ∀ z : ℍ, w (γ • z) = δ • w z)
      (hA : ∀ z : ℍ, normalizedUpperEquiv ν (γ • z) = A • normalizedUpperEquiv ν z)
      (hB : ∀ z : ℍ, normalizedUpperEquiv ν' (δ • z) = B • normalizedUpperEquiv ν' z)
      (z : ℍ) : A • z = (α⁻¹ * B * α) • z := by
    obtain ⟨t, rfl⟩ := (normalizedUpperEquiv ν).surjective z
    have he : α • (A • normalizedUpperEquiv ν t) =
        B • (α • normalizedUpperEquiv ν t) := by
      calc
        _ = α • normalizedUpperEquiv ν (γ • t) := congrArg (fun q : ℍ => α • q) (hA t).symm
        _ = normalizedUpperEquiv ν' (w (γ • t)) := by rw [hα, w.symm_apply_apply]
        _ = normalizedUpperEquiv ν' (δ • w t) := congrArg (normalizedUpperEquiv ν') (hwγ t)
        _ = B • normalizedUpperEquiv ν' (w t) := hB _
        _ = B • (α • normalizedUpperEquiv ν t) := by rw [hα, w.symm_apply_apply]
    have hi := congrArg (fun q : ℍ => α⁻¹ • q) he
    simpa only [mul_smul, inv_smul_smul] using hi
  apply automorphicSubmodule_eq_of_sameActions
  · intro A hA
    obtain ⟨γ, hγ, hν⟩ := (deformedGroup_spec hΓ ν).2.2 A hA
    obtain ⟨δ, hδ, hwγ⟩ := hw.2.1 γ hγ
    obtain ⟨B, hB, hν'⟩ := (deformedGroup_spec hΓ ν').2.1 δ hδ
    refine ⟨α⁻¹ * B * α, ?_, compare γ δ A B hwγ
      (upper_conjugacy ν γ A hν) (upper_conjugacy ν' δ B hν')⟩
    change α⁻¹ * B * α ∈ (deformedGroup hΓ ν').map (MulAut.conj α⁻¹).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨B, hB, by simp⟩
  · intro C hC
    obtain ⟨B, hB, hBC⟩ := Subgroup.mem_map.mp hC
    obtain ⟨δ, hδ, hν'⟩ := (deformedGroup_spec hΓ ν').2.2 B hB
    obtain ⟨γ, hγ, hwi⟩ := hw.2.2 δ hδ
    obtain ⟨A, hA, hν⟩ := (deformedGroup_spec hΓ ν).2.1 γ hγ
    have hwγ (z : ℍ) : w (γ • z) = δ • w z := by
      have he := congrArg w (hwi (w z))
      simpa only [w.apply_symm_apply, w.symm_apply_apply] using he.symm
    refine ⟨A, hA, fun z => ?_⟩
    have hCeq : C = α⁻¹ * B * α := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hBC.symm
    rw [hCeq]
    exact (compare γ δ A B hwγ
      (upper_conjugacy ν γ A hν) (upper_conjugacy ν' δ B hν') z).symm

/-- A finite composition of the existing equality isometry and actual
Möbius isometry, in the unchanged weighted norms. -/
def markingRecentringIsometry {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (w : ℍ ≃ₜ ℍ)
    (hw : QCNormalizerModular.NormalizerCondition Γ w) (ν ν' : Ball Γ) (α : Deck)
    (hα : ∀ z : ℍ, normalizedUpperEquiv ν' z =
      α • normalizedUpperEquiv ν (w.symm z)) :
    Automorphic (deformedGroup hΓ ν) ≃ₗᵢ[ℂ] Automorphic (deformedGroup hΓ ν') :=
  (LinearIsometryEquiv.ofEq _ _ (markingRecentring_submodule_eq hΓ w hw ν ν' α hα)).trans
    (automorphicRealMobiusIsometry (deformedGroup hΓ ν') α⁻¹)

/-- Every literal quadratic value is transported by the point-dependent α⁻¹. -/
theorem markingRecentringIsometry_toSource {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (w : ℍ ≃ₜ ℍ)
    (hw : QCNormalizerModular.NormalizerCondition Γ w) (ν ν' : Ball Γ) (α : Deck)
    (hα : ∀ z : ℍ, normalizedUpperEquiv ν' z =
      α • normalizedUpperEquiv ν (w.symm z)) (φ : Automorphic (deformedGroup hΓ ν)) :
    ((markingRecentringIsometry hΓ w hw ν ν' α hα φ).toSource : ℂ → ℂ) =
      realMobiusPullback α⁻¹ (φ.toSource : ℂ → ℂ) := by
  change ((automorphicRealMobiusIsometry (deformedGroup hΓ ν') α⁻¹
    (LinearIsometryEquiv.ofEq _ _ (markingRecentring_submodule_eq hΓ w hw ν ν' α hα) φ)).toSource :
      ℂ → ℂ) = _
  rw [automorphicRealMobiusIsometry_toSource]
  rfl

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami BersWeighted NormalizedCoefficientTransport
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)

include hg hgenus

/-- Every original QC normalizer has the exact nonlinear recentering square
on the entire genuine Bers image, with its derived point-dependent lift. -/
theorem exists_upperMarkingBersRecentring :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    ∀ w : QCNormalizerModular.Normalizer hp,
      let f := QCNormalizerModular.descendedAut hp w.val w.property
      let hw := QCNormalizerModular.descendedAut_isLift hp w.val w.property
      ∃ (ρ : Ball Γ) (N₀ : Deck)
        (hN₀ : ∀ z : ℍ, normalizedUpperEquiv ρ z = N₀ • w.val z),
        ∀ ν : Ball Γ,
          let ν' := givenReferenceChangedBall hp hp hΓ f.val w.val hw ρ N₀ hN₀ ν
          ∃ (α : Deck) (hα : ∀ z : ℍ, normalizedUpperEquiv ν' z =
              α • normalizedUpperEquiv ν (w.val.symm z)),
            ∀ (φ : Automorphic Γ) (_hφ : φ ∈ coefficientBersImage hΓ),
              bersTranslation hΓ ν'
                  (givenReferenceBersMap hp hp hΓ f.val w.val hw ρ N₀ hN₀ φ) =
                markingRecentringIsometry hΓ w.val w.property ν ν' α hα
                  (bersTranslation hΓ ν φ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  intro w
  have hwNorm : QCNormalizerModular.NormalizerCondition Γ w.val := w.property
  let f : SourceQCModular.Aut X := QCNormalizerModular.descendedAut hp w.val hwNorm
  let hw : LiZhongQC.IsLift p p f.val w.val :=
    QCNormalizerModular.descendedAut_isLift hp w.val hwNorm
  obtain ⟨ρ, N₀, hN₀, _, hall⟩ :=
    exists_upperModularRepresentation_normalizedFormula R hg hgenus hΓ hp w
  refine ⟨ρ, N₀, hN₀, ?_⟩
  intro ν
  let ν' := givenReferenceChangedBall hp hp hΓ f.val w.val hw ρ N₀ hN₀ ν
  obtain ⟨_, _, α, _, hα, _⟩ := hall ν
  refine ⟨α, hα, ?_⟩
  intro φ hφ
  obtain ⟨η, rfl⟩ := (mem_coefficientBersImage_iff_coefficient hΓ φ).mp hφ
  let η' := givenReferenceChangedBall hp hp hΓ f.val w.val hw ρ N₀ hN₀ η
  obtain ⟨_, _, αη, _, hη, _⟩ := hall η
  let κ := translatedBall hΓ ν η
  let κ' := translatedBall hΓ ν' η'
  have hrelative (z : ℍ) : normalizedUpperEquiv κ' z =
      αη • normalizedUpperEquiv κ (α⁻¹ • z) := by
    obtain ⟨x, rfl⟩ := (normalizedUpperEquiv ν').surjective z
    change normalizedUpperEquiv (translatedBall hΓ ν' η') (normalizedUpperEquiv ν' x) =
      αη • normalizedUpperEquiv (translatedBall hΓ ν η) (α⁻¹ • normalizedUpperEquiv ν' x)
    rw [normalizedUpperEquiv_translatedBall_comp, hη]
    have hi : α⁻¹ • normalizedUpperEquiv ν' x = normalizedUpperEquiv ν (w.val.symm x) := by
      rw [hα, inv_smul_smul]
    rw [hi, normalizedUpperEquiv_translatedBall_comp]
  have hraw :
      LiZhongQC.bersFunction (planeRepresentative κ'.val.val) =
        realMobiusPullback α⁻¹ (LiZhongQC.bersFunction (planeRepresentative κ.val.val)) :=
    rawBers_realMobiusPullback_of_symmetricPostcomp
      (toSourceGamma κ).val (toSourceGamma κ').val αη α⁻¹ (fun z hz => by
        change normalizedMap κ' z =
          LiZhongQC.mobiusFn (αη 0 0) (αη 0 1) (αη 1 0) (αη 1 1)
            (normalizedMap κ
              (LiZhongQC.mobiusFn (α⁻¹ 0 0) (α⁻¹ 0 1) (α⁻¹ 1 0) (α⁻¹ 1 1) z))
        have he := congrArg (fun q : ℍ => (q : ℂ)) (hrelative ⟨z, hz⟩)
        simpa only [normalizedUpperEquiv_coe, LiZhongQC.h23l_b_coe_smul,
          LiZhongQC.mobiusFn] using he)
  have hleft :
      bersTranslation hΓ ν'
          (givenReferenceBersMap hp hp hΓ f.val w.val hw ρ N₀ hN₀
            (automorphicProjection hΓ η.val)) =
        automorphicProjection (And.left (deformedGroup_spec hΓ ν')) κ'.val := by
    exact (congrArg (bersTranslation hΓ ν')
      (givenReferenceBersMap_projection hp hp hΓ hΓ f.val w.val hw ρ N₀ hN₀ η)).trans
        (bersTranslation_automorphicProjection hΓ ν' η')
  have hright :
      bersTranslation hΓ ν (automorphicProjection hΓ η.val) =
        automorphicProjection (And.left (deformedGroup_spec hΓ ν)) κ.val :=
    bersTranslation_automorphicProjection hΓ ν η
  apply Automorphic.toSource_injective
  apply Subtype.ext
  calc
    _ = LiZhongQC.bersFunction (planeRepresentative κ'.val.val) :=
      (congrArg (fun ψ : Automorphic (deformedGroup hΓ ν') =>
        (ψ.toSource : ℂ → ℂ)) hleft).trans
          (automorphicProjection_toSource_eq (And.left (deformedGroup_spec hΓ ν'))
            κ'.val (Ball.norm_lt_one κ'))
    _ = realMobiusPullback α⁻¹
        (LiZhongQC.bersFunction (planeRepresentative κ.val.val)) := hraw
    _ = realMobiusPullback α⁻¹
        ((bersTranslation hΓ ν (automorphicProjection hΓ η.val)).toSource : ℂ → ℂ) :=
      congrArg (realMobiusPullback α⁻¹)
        ((congrArg (fun ψ : Automorphic (deformedGroup hΓ ν) =>
          (ψ.toSource : ℂ → ℂ)) hright).trans
            (automorphicProjection_toSource_eq (And.left (deformedGroup_spec hΓ ν))
              κ.val (Ball.norm_lt_one κ))).symm
    _ = _ :=
      (markingRecentringIsometry_toSource hΓ w.val hwNorm ν ν' α hα
        (bersTranslation hΓ ν (automorphicProjection hΓ η.val))).symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
