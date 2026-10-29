module

public import LowDimensionalTopology.Geometry.Teichmuller.QCNormalizerModularGroup
public import LowDimensionalTopology.Geometry.Teichmuller.QCModularGammaAction

/-!
# The original upper-normalizer modular transformations are holomorphic isometries

The acting group is the actual quotient of ALL quasiconformal normalizers
of the original upper-plane deck actions. Its class equality is the proved
right-deck equality on the full extended real boundary. The genuine descent
isomorphism identifies it with the actual surface QC mapping class group.
Every representative acts by the original normalized composition on the
original group Teichmuller space. Every modular class acts biholomorphically
and preserves the original Teichmuller distance and its QC metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

local notation "hfree" => LiZhongQC.s27g_actsFreely hp
local notation "Z" => Fin (3*g-3) → ℂ

/-- The genuine original normalizer quotient acts through the actual descent
isomorphism, on the original group coefficient classes. -/
def upperModularRepresentation :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    QCNormalizerModular.ModularGroup hp →* Equiv.Perm (LiZhongQC.TeichGamma Γ) := by
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  letI := R.t2Space
  letI := R.connectedSpace
  exact (gammaModularRepresentation R hg hgenus hΓ hp).comp
    (QCNormalizerModular.modularEquiv hp).toMonoidHom

/-- Every actual upper normalizer acts by its original descended reference map. -/
theorem upperModularRepresentation_mk :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    ∀ w : QCNormalizerModular.Normalizer hp,
      upperModularRepresentation R hg hgenus hΓ hp (QCNormalizerModular.mk hp w) =
        referenceGammaEquiv R R hg hgenus hgenus
          (QCNormalizerModular.descendedAut hp w.val w.property).val
          (QCNormalizerModular.descendedAut hp w.val w.property).property hΓ hΓ hp hp := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  intro w
  exact (congrArg (gammaModularRepresentation R hg hgenus hΓ hp)
    (QCNormalizerModular.modularEquiv_mk hp w)).trans
      (gammaModularRepresentation_mk R hg hgenus hΓ hp
        (QCNormalizerModular.descendedAut hp w.val w.property))

/-- The original normalizer representative has the actual normalized
composition action on every compatible coefficient class. The coefficient
and real Mobius normalization are derived internally from that same lift. -/
theorem exists_upperModularRepresentation_coefficientFormula :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    ∀ w : QCNormalizerModular.Normalizer hp,
      let f := QCNormalizerModular.descendedAut hp w.val w.property
      let hw := QCNormalizerModular.descendedAut_isLift hp w.val w.property
      ∃ (ν : Ball Γ) (M : Deck)
        (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w.val τ),
        ∀ μ : Ball Γ,
          upperModularRepresentation R hg hgenus hΓ hp (QCNormalizerModular.mk hp w)
              (Quotient.mk _ (toSourceGamma μ)) =
            Quotient.mk _ (toSourceGamma
              (givenReferenceChangedBall hp hp hΓ f.val w.val hw ν M hM μ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  intro w
  let f := QCNormalizerModular.descendedAut hp w.val w.property
  let hw := QCNormalizerModular.descendedAut_isLift hp w.val w.property
  obtain ⟨ν, M, _, hM, _⟩ :=
    exists_native_normalization_of_given_lift hp hp f.val f.property w.val hw
  refine ⟨ν, M, hM, ?_⟩
  intro μ
  exact (congrArg (fun T : Equiv.Perm (LiZhongQC.TeichGamma Γ) =>
    T (Quotient.mk _ (toSourceGamma μ)))
      (upperModularRepresentation_mk R hg hgenus hΓ hp w)).trans
    (referenceGammaEquiv_coefficientProjection R R hg hgenus hgenus f.val f.property
      hΓ hΓ hp hp w.val hw ν M hM μ)

/-- Every element of the original full normalizer modular group gives a
biholomorphic automorphism of the original group space which preserves both
the literal half-log Teichmuller distance and the original QC metric. -/
theorem upperModularRepresentation_biholomorphic_isometry :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := R.compactSpace
    letI := gammaQCMetricSpace R hg hgenus hΓ hfree hp
    letI := gammaBersChartedSpace R hg hgenus hΓ hfree hp
    ∀ γ : QCNormalizerModular.ModularGroup hp,
      (ContMDiff 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω (upperModularRepresentation R hg hgenus hΓ hp γ) ∧
        ContMDiff 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω (upperModularRepresentation R hg hgenus hΓ hp γ).symm) ∧
      Isometry (upperModularRepresentation R hg hgenus hΓ hp γ) ∧
      ∀ a b : LiZhongQC.TeichGamma Γ,
        LiZhongQC.teichDistanceGamma
          (upperModularRepresentation R hg hgenus hΓ hp γ a)
          (upperModularRepresentation R hg hgenus hΓ hp γ b) =
        LiZhongQC.teichDistanceGamma a b := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := gammaQCMetricSpace R hg hgenus hΓ hfree hp
  let := gammaBersChartedSpace R hg hgenus hΓ hfree hp
  intro γ
  exact ⟨(gammaModularRepresentation_biholomorphic_isometry R hg hgenus hΓ hp
      (QCNormalizerModular.modularEquiv hp γ)).1,
    (gammaModularRepresentation_biholomorphic_isometry R hg hgenus hΓ hp
      (QCNormalizerModular.modularEquiv hp γ)).2,
    gammaModularRepresentation_distance R hg hgenus hΓ hp
      (QCNormalizerModular.modularEquiv hp γ)⟩

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
