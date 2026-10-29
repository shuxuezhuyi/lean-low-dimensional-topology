module

public import LowDimensionalTopology.Geometry.Teichmuller.QCNormalizerDescent
public import LowDimensionalTopology.Geometry.Teichmuller.QCNormalizerBoundary

/-!
# The full upper-half-plane modular group and its original surface quotient

The normalizers are all actual quasiconformal upper-half-plane homeomorphisms
with both genuine deck-action conjugacy laws. Their quotient has exactly the
right-deck boundary equivalence relation, including infinity. Actual covering
descent identifies this group with the original surface's full quasiconformal
modular group. Matrix representatives differing by sign are compared only
through their actions.

The covering, quasiconformal and boundary APIs are reused from Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0).
See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.QCNormalizerModular

open LiZhongQC

/-- The literal action-normalizer condition for all upper QC homeomorphisms. -/
def NormalizerCondition (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (w : UpperHalfPlane ≃ₜ UpperHalfPlane) : Prop :=
  IsQuasiconformal (liftToC w) upperHalf ∧
    (∀ γ ∈ Γ, ∃ δ ∈ Γ, ∀ τ : UpperHalfPlane, w (γ • τ) = δ • w τ) ∧
    (∀ δ ∈ Γ, ∃ γ ∈ Γ, ∀ τ : UpperHalfPlane, w.symm (δ • τ) = γ • w.symm τ)

universe u
variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hp : IsUniformization Γ p)

include hp in
/-- Every actual lift of a surface QC automorphism satisfies the full upper
QC normalizer condition, in both deck-action directions. -/
theorem condition_of_surfaceLift (f : SourceQCModular.Aut X)
    {w : UpperHalfPlane ≃ₜ UpperHalfPlane} (hw : IsLift p p f.val w) :
    NormalizerCondition Γ w := by
  obtain ⟨K, hK⟩ := f.property
  refine ⟨⟨K, h23l_lift_isKQC hp hp hK hw⟩, ?_, ?_⟩
  · intro γ hγ
    exact h23l_deck hp hp hw hγ
  · intro δ hδ
    exact h23l_deck hp hp (s27g_isLift_symm hw) hδ

/-- The genuine descended QC automorphism attached to the original normalizer. -/
def descendedAut (w : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hw : NormalizerCondition Γ w) : SourceQCModular.Aut X :=
  ⟨QCNormalizerDescent.descendedHomeomorph hp w hw.2.1 hw.2.2,
    by
      obtain ⟨K, hK⟩ := hw.1
      exact ⟨K, QCNormalizerDescent.descendedHomeomorph_isKQCRS hp w hw.2.1 hw.2.2 hK⟩⟩

/-- The original upper map is literally a lift of its descended QC map. -/
theorem descendedAut_isLift (w : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hw : NormalizerCondition Γ w) :
    IsLift p p (descendedAut hp w hw).val w :=
  QCNormalizerDescent.descendedHomeomorph_isLift hp w hw.2.1 hw.2.2

/-- All actual QC normalizers form a subgroup, with composition as
multiplication. Closure follows from the actual descended QC maps and lifts. -/
def quasiconformalNormalizerSubgroup : Subgroup (UpperHalfPlane ≃ₜ UpperHalfPlane) where
  carrier := {w | NormalizerCondition Γ w}
  one_mem' := condition_of_surfaceLift hp (1 : SourceQCModular.Aut X) (fun _ => rfl)
  mul_mem' := by
    intro w v hw hv
    let f := descendedAut hp w hw
    let g := descendedAut hp v hv
    apply condition_of_surfaceLift hp (f * g)
    intro τ
    change p (w (v τ)) = f.val (g.val (p τ))
    calc
      p (w (v τ)) = f.val (p (v τ)) := descendedAut_isLift hp w hw (v τ)
      _ = f.val (g.val (p τ)) := congrArg f.val (descendedAut_isLift hp v hv τ)
  inv_mem' := by
    intro w hw
    exact condition_of_surfaceLift hp (descendedAut hp w hw)⁻¹
      (s27g_isLift_symm (descendedAut_isLift hp w hw))

/-- The full group of actual QC normalizers, without a smoothness restriction. -/
abbrev Normalizer := quasiconformalNormalizerSubgroup hp

/-- Genuine covering descent preserves the actual order of composition. -/
def descentHom : Normalizer hp →* SourceQCModular.Aut X where
  toFun w := descendedAut hp w.val w.property
  map_one' := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro x
    obtain ⟨τ, rfl⟩ := hp.2.2.1 x
    exact (descendedAut_isLift hp (1 : UpperHalfPlane ≃ₜ UpperHalfPlane)
      (1 : Normalizer hp).property τ).symm
  map_mul' w v := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro x
    obtain ⟨τ, rfl⟩ := hp.2.2.1 x
    change (descendedAut hp (w.val * v.val) (w * v).property).val (p τ) =
      (descendedAut hp w.val w.property).val
        ((descendedAut hp v.val v.property).val (p τ))
    calc
      (descendedAut hp (w.val * v.val) (w * v).property).val (p τ) =
          p (w.val (v.val τ)) :=
        (descendedAut_isLift hp (w.val * v.val) (w * v).property τ).symm
      _ = (descendedAut hp w.val w.property).val (p (v.val τ)) :=
        descendedAut_isLift hp w.val w.property (v.val τ)
      _ = (descendedAut hp w.val w.property).val
          ((descendedAut hp v.val v.property).val (p τ)) :=
        congrArg (descendedAut hp w.val w.property).val
          (descendedAut_isLift hp v.val v.property τ)

variable [T2Space X] [ConnectedSpace X]

/-- Every actual surface QC automorphism has an actual QC normalizer lift. -/
theorem descentHom_surjective : Function.Surjective (descentHom hp) := by
  intro f
  obtain ⟨τ₁, hτ₁⟩ := hp.2.2.1 (f.val (p UpperHalfPlane.I))
  obtain ⟨w, hw, _⟩ := exists_lift hp hp f.val UpperHalfPlane.I τ₁ hτ₁
  let hwc := condition_of_surfaceLift hp f hw
  refine ⟨⟨w, hwc⟩, ?_⟩
  apply Subtype.ext
  exact QCNormalizerDescent.descendedHomeomorph_eq_of_isLift
    hp w hwc.2.1 hwc.2.2 f.val hw

/-- The actual normalizer-to-surface modular homomorphism. -/
def modularHom : Normalizer hp →* SourceQCModular.ModularGroup X :=
  (QuotientGroup.mk' (SourceQCModular.homotopyIdentitySubgroup X)).comp (descentHom hp)

/-- Every full surface modular class is represented by an actual upper QC
normalizer. -/
theorem modularHom_surjective : Function.Surjective (modularHom hp) :=
  (QuotientGroup.mk'_surjective (SourceQCModular.homotopyIdentitySubgroup X)).comp
    (descentHom_surjective hp)

/-- The selected genuine extended-real boundary map of a normalizer. -/
def normalizerBoundary (w : Normalizer hp) : ExtPlane → ExtPlane :=
  QCNormalizerBoundary.boundaryExtension w.val w.property.1

/-- Equality of descended modular classes is exactly the book's full
right-deck boundary relation on the actual normalizers. -/
theorem modularHom_eq_iff_rightDeck [CompactSpace X] (w v : Normalizer hp) :
    modularHom hp w = modularHom hp v ↔
      QCNormalizerBoundary.RightDeckBoundaryRel Γ
        (normalizerBoundary hp w) (normalizerBoundary hp v) := by
  change SourceQCModular.mk (descendedAut hp w.val w.property) =
      SourceQCModular.mk (descendedAut hp v.val v.property) ↔ _
  exact (SourceQCModular.mk_eq_mk_iff_homotopic _ _).trans
    (QCNormalizerBoundary.homotopic_iff_selectedBoundary_rightDeck hp
      (descendedAut hp w.val w.property).val (descendedAut hp v.val v.property).val
      (descendedAut_isLift hp w.val w.property) (descendedAut_isLift hp v.val v.property)
      w.property.1 v.property.1)

/-- The actual upper modular group. The following class-equality theorem
identifies its quotient relation with the literal right-deck boundary one. -/
abbrev ModularGroup := Normalizer hp ⧸ (modularHom hp).ker

/-- The class of an actual upper QC normalizer. -/
def mk (w : Normalizer hp) : ModularGroup hp := QuotientGroup.mk w

/-- The genuine group isomorphism to the full original surface modular group. -/
def modularEquiv : ModularGroup hp ≃* SourceQCModular.ModularGroup X :=
  QuotientGroup.quotientKerEquivOfSurjective (modularHom hp) (modularHom_surjective hp)

/-- The isomorphism sends every actual normalizer to its actual descended
surface modular class. -/
theorem modularEquiv_mk (w : Normalizer hp) :
    modularEquiv hp (mk hp w) = SourceQCModular.mk (descendedAut hp w.val w.property) := by
  change QuotientGroup.kerLift (modularHom hp) (QuotientGroup.mk w) = modularHom hp w
  exact QuotientGroup.kerLift_mk (modularHom hp) w

/-- This quotient has exactly the prescribed boundary equivalence relation,
including the point at infinity and a genuine deck transformation on the right. -/
theorem mk_eq_mk_iff_rightDeck [CompactSpace X] (w v : Normalizer hp) :
    mk hp w = mk hp v ↔ QCNormalizerBoundary.RightDeckBoundaryRel Γ
      (normalizerBoundary hp w) (normalizerBoundary hp v) := by
  calc
    mk hp w = mk hp v ↔ modularEquiv hp (mk hp w) = modularEquiv hp (mk hp v) :=
      (modularEquiv hp).injective.eq_iff.symm
    _ ↔ SourceQCModular.mk (descendedAut hp w.val w.property) =
        SourceQCModular.mk (descendedAut hp v.val v.property) := by
      rw [modularEquiv_mk, modularEquiv_mk]
    _ ↔ QCNormalizerBoundary.RightDeckBoundaryRel Γ
        (normalizerBoundary hp w) (normalizerBoundary hp v) := modularHom_eq_iff_rightDeck hp w v

end LowDimensionalTopology.Geometry.Teichmuller.QCNormalizerModular
