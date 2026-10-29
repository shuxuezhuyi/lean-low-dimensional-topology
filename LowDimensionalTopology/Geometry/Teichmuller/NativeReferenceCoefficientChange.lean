module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceLiftNormalization
public import LowDimensionalTopology.Geometry.Teichmuller.CoefficientRealMobiusIsometry
public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedCoefficientNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersRealMobiusCovariance

/-!
# The original given reference change on genuine coefficient classes

The derived action correspondence identifies the actual compatible closed
subspaces, independently of central signs. The literal real Möbius pullback
then transports every translated coefficient to the original supplied target
group, with the unchanged L-infinity norm. Its source representative is the
actual source Möbius pullback of the translated coefficient.

Uses Wu Xiaobin's Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

/-- The original coefficient equations depend on actual actions, not on central signs. -/
theorem compatibleSubmodule_eq_of_sameActions (G H : Subgroup Deck)
    (hGH : ∀ γ ∈ G, ∃ δ ∈ H, ∀ τ : ℍ, γ • τ = δ • τ)
    (hHG : ∀ δ ∈ H, ∃ γ ∈ G, ∀ τ : ℍ, δ • τ = γ • τ) :
    compatibleSubmodule G = compatibleSubmodule H := by
  ext μ
  constructor
  · intro hμ δ hδ
    obtain ⟨γ, hγ, hact⟩ := hHG δ hδ
    rw [pullback_eq_of_same_action hact]
    exact hμ γ hγ
  · intro hμ γ hγ
    obtain ⟨δ, hδ, hact⟩ := hGH γ hγ
    rw [pullback_eq_of_same_action hact]
    exact hμ δ hδ

universe u
variable {A B : Type u}
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]
    {Γ Γ1 : Subgroup Deck} {p : ℍ → A} {p1 : ℍ → B}
    (hp : LiZhongQC.IsUniformization Γ p) (hp1 : LiZhongQC.IsUniformization Γ1 p1)
    (hΓ : LiZhongQC.IsFuchsian Γ) (e : A ≃ₜ B) (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p1 e w) (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ)

omit [IsManifold 𝓘(ℂ) ω A] [IsManifold 𝓘(ℂ) ω B]

include hp hp1 e w hw hM in
/-- The normalized given lift identifies the full actual compatible submodules. -/
theorem givenLift_compatibleSubmodule_eq :
    compatibleSubmodule (deformedGroup hΓ ν) =
      compatibleSubmodule (LiZhongQC.conjGroup Γ1 M) := by
  obtain ⟨hGH, hHG⟩ := normalized_given_lift_deck_actions hp hp1 hΓ e w hw ν M hM
  exact compatibleSubmodule_eq_of_sameActions _ _ hGH hHG

/-- The actual all-vector coefficient isometry to the original supplied target group. -/
def givenLiftCoefficientIsometry :
    Space (deformedGroup hΓ ν) ≃ₗᵢ[ℂ] Space Γ1 :=
  (LinearIsometryEquiv.ofEq _ _
    (givenLift_compatibleSubmodule_eq hp hp1 hΓ e w hw ν M hM)).trans
      (coefficientRealMobiusIsometry Γ1 M)

/-- The isometry retains the literal native ambient coefficient pullback. -/
theorem givenLiftCoefficientIsometry_val (κ : Space (deformedGroup hΓ ν)) :
    (givenLiftCoefficientIsometry hp hp1 hΓ e w hw ν M hM κ).val =
      GammaMeasurableBeltrami.pullback M κ.val := by
  let i : Space (deformedGroup hΓ ν) ≃ₗᵢ[ℂ] Space (LiZhongQC.conjGroup Γ1 M) :=
    LinearIsometryEquiv.ofEq _ _
      (givenLift_compatibleSubmodule_eq hp hp1 hΓ e w hw ν M hM)
  have hi : (i κ).val = κ.val :=
    LinearIsometryEquiv.coe_ofEq_apply
      (givenLift_compatibleSubmodule_eq hp hp1 hΓ e w hw ν M hM) κ
  exact (coefficientRealMobiusIsometry_val Γ1 M (i κ)).trans
    (congrArg (GammaMeasurableBeltrami.pullback M) hi)

/-- The complete original coefficient ball is translated into the supplied
original target group's complete ball, not merely a local section. -/
def givenReferenceChangedBall (μ : Ball Γ) : Ball Γ1 :=
  ⟨givenLiftCoefficientIsometry hp hp1 hΓ e w hw ν M hM (gammaTranslation hΓ ν μ.val), by
    rw [Metric.mem_ball, dist_zero_right,
      (givenLiftCoefficientIsometry hp hp1 hΓ e w hw ν M hM).norm_map]
    exact norm_gammaTranslation_lt_one hΓ ν μ⟩

/-- The same original fractional translation and the actual real Möbius
operator determine every value in the genuine coefficient class. -/
theorem givenReferenceChangedBall_val (μ : Ball Γ) :
    (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ).val.val =
      GammaMeasurableBeltrami.pullback M (translation ν μ.val.val) :=
  givenLiftCoefficientIsometry_val hp hp1 hΓ e w hw ν M hM (gammaTranslation hΓ ν μ.val)

/-- The actual changed coefficient class equals the source Möbius pullback of
the literal translated source coefficient. -/
theorem givenReferenceChangedBall_sourceAmbient (μ : Ball Γ) :
    (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ).val.val =
      sourceAmbient (LiZhongQC.b33_e_pb (translatedSource hΓ ν μ).val M) := by
  rw [givenReferenceChangedBall_val, sourceAmbient_realMobiusPullback]
  exact congrArg (GammaMeasurableBeltrami.pullback M)
    (gammaTranslation_val_eq_sourceAmbient hΓ ν μ)

/-- The exact planar source representative is retained in its original upper-plane a.e. class. -/
theorem givenReferenceChangedBall_source_ae (μ : Ball Γ) :
    planeRepresentative (givenReferenceChangedBall hp hp1 hΓ e w hw ν M hM μ).val.val
      =ᵐ[volume.restrict LiZhongQC.upperHalf]
        (LiZhongQC.b33_e_pb (translatedSource hΓ ν μ).val M).val := by
  apply ae_plane_iff.mpr
  filter_upwards [sourceAmbient_coe_ae
    (LiZhongQC.b33_e_pb (translatedSource hΓ ν μ).val M)] with z hz
  rw [planeRepresentative_coe, givenReferenceChangedBall_sourceAmbient]
  exact hz

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
