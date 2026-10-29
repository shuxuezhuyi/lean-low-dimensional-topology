/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCTargetUniverse
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCLiftCoefficientTransport
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedMarkingActions

/-!
# Normalized actions for original targets in independent universes

The common-universe representatives come from actual biholomorphic target
identifications. Their normalized lifts are the literal normalized symmetric
solutions for the original markings' coefficients. Their transported coverings
uniformize the original actual targets. The final equivalence concerns equality
in the original marked quotient, without changing its carrier.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Manifold ContDiff UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u v

/-- The actual target identification preserves the literal original coefficient
pointwise, including the common zero value off the upper half-plane. -/
theorem sourceCarrierRepresentative_liftCoeff
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, v} R) :
    s27u_liftCoeff p m.sourceCarrierRepresentative.marking = s27u_liftCoeff p m.marking := by
  have h := liftCoeff_postcompose_biholomorphic hp.1.continuous
    m.sourceCarrierRepresentative.marking.continuous
    m.sourceCarrierProjection m.sourceCarrierProjection_biholomorphic
  have heq : (m.sourceCarrierProjection : m.sourceCarrierTarget.carrier → m.target.carrier) ∘
      (m.sourceCarrierRepresentative.marking : R.carrier → m.sourceCarrierTarget.carrier) =
      (m.marking : R.carrier → m.target.carrier) := by
    funext x
    exact m.sourceCarrierProjection_marking x
  calc
    s27u_liftCoeff p m.sourceCarrierRepresentative.marking =
        s27u_liftCoeff p (m.sourceCarrierProjection ∘ m.sourceCarrierRepresentative.marking) := h.symm
    _ = s27u_liftCoeff p m.marking := congrArg (s27u_liftCoeff p) heq

/-- The canonical normalized lift is constructed internally from the original
marking, using its actual biholomorphic target identification. -/
def canonicalMarkingLiftGeneral
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, v} R) : ℍ ≃ₜ ℍ :=
  canonicalMarkingLift R hp m.sourceCarrierRepresentative

/-- The constructed lift is the literal symmetric solution for the original
coefficient and gives the actual original target's conjugated uniformization.
Its lift equation and all normalization conditions refer to that same marking. -/
theorem canonicalMarkingLiftGeneral_spec
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, v} R) :
    let F := canonicalMarkingLiftGeneral R hp m
    let G := OnePoint.map (s27u_fSym (s27u_liftCoeff p m.marking))
    (∀ τ, (F τ : ℂ) = s27u_fSym (s27u_liftCoeff p m.marking) τ) ∧
    IsUniformization (s27u_conjGroup Γ F) (s27u_proj p m.marking F) ∧
    IsLift p (s27u_proj p m.marking F) m.marking F ∧
    IsHomeoExtension (liftToC F) upperHalf upperHalf G ∧
    G ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
    G ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ G extInf = extInf := by
  dsimp only
  let F := canonicalMarkingLiftGeneral R hp m
  have h := canonicalMarkingLift_spec R hp m.sourceCarrierRepresentative
  have hμ := sourceCarrierRepresentative_liftCoeff R hp m
  have hpoint : ∀ τ, (F τ : ℂ) = s27u_fSym (s27u_liftCoeff p m.marking) τ :=
    fun τ => (h.1 τ).trans
      (congrArg (fun μ : ℂ → ℂ => s27u_fSym μ τ) hμ)
  have hU := uniformization_postcompose_biholomorphic
    (S := m.sourceCarrierTarget) (T := m.target)
    h.2.1 m.sourceCarrierProjection m.sourceCarrierProjection_biholomorphic
  have hproj : (m.sourceCarrierProjection : m.sourceCarrierTarget.carrier → m.target.carrier) ∘
      s27u_proj p m.sourceCarrierRepresentative.marking F = s27u_proj p m.marking F := by
    funext τ
    exact m.sourceCarrierProjection_marking (p (F.symm τ))
  have hU' : IsUniformization (s27u_conjGroup Γ F) (s27u_proj p m.marking F) := hproj ▸ hU
  have hL : IsLift p (s27u_proj p m.marking F) m.marking F := by
    intro τ
    exact congrArg (fun x => m.marking (p x)) (F.symm_apply_apply τ)
  have hG : OnePoint.map (s27u_fSym (s27u_liftCoeff p m.sourceCarrierRepresentative.marking)) =
      OnePoint.map (s27u_fSym (s27u_liftCoeff p m.marking)) :=
    congrArg (fun μ : ℂ → ℂ => OnePoint.map (s27u_fSym μ)) hμ
  have hnorm :
      IsHomeoExtension (liftToC F) upperHalf upperHalf
        (OnePoint.map (s27u_fSym (s27u_liftCoeff p m.marking))) ∧
      OnePoint.map (s27u_fSym (s27u_liftCoeff p m.marking)) ((0 : ℂ) : ExtPlane) =
        ((0 : ℂ) : ExtPlane) ∧
      OnePoint.map (s27u_fSym (s27u_liftCoeff p m.marking)) ((1 : ℂ) : ExtPlane) =
        ((1 : ℂ) : ExtPlane) ∧
      OnePoint.map (s27u_fSym (s27u_liftCoeff p m.marking)) extInf = extInf :=
    hG ▸ h.2.2.2
  exact ⟨hpoint, hU', hL, hnorm⟩

/-- The lift's actual coefficient is the original marking's coefficient almost
everywhere on the upper half-plane, with no replacement coefficient. -/
theorem canonicalMarkingLiftGeneral_dilatationAE
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, v} R) :
    ∀ᵐ z ∂(volume.restrict upperHalf),
      complexDilatation (liftToC (canonicalMarkingLiftGeneral R hp m)) z =
        s27u_liftCoeff p m.marking z := by
  have h : ∀ᵐ z ∂(volume.restrict upperHalf),
      complexDilatation (liftToC (canonicalMarkingLiftGeneral R hp m)) z =
        s27u_liftCoeff p m.sourceCarrierRepresentative.marking z :=
    (Classical.choose_spec
      (s27u_uniformization_transport hp m.sourceCarrierRepresentative.marking
        m.sourceCarrierRepresentative.qc)).2.2.2.2
  filter_upwards [h] with z hz
  exact hz.trans (congrFun (sourceCarrierRepresentative_liftCoeff R hp m) z)

/-- For the original independently sized targets, conformal marked homotopy is
exactly equality of the actual normalized projective deck actions. -/
theorem marked_equivalent_iff_general_canonical_lift_actions
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (m₁ m₂ : Marked.{u, v} R) :
    let F₁ := canonicalMarkingLiftGeneral R hp m₁
    let F₂ := canonicalMarkingLiftGeneral R hp m₂
    m₁.Equivalent m₂ ↔
      ∀ γ ∈ Γ, ∀ τ : ℍ, F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ) :=
  (marked_equivalent_iff_sourceCarrierRepresentatives m₁ m₂).trans
    (marked_equivalent_iff_canonical_lift_actions R hp hfixed
      m₁.sourceCarrierRepresentative m₂.sourceCarrierRepresentative)

/-- The same exact criterion holds in the actual original QC-marked quotient;
its reference carrier and its independent target universe are unchanged. -/
theorem mk_eq_mk_iff_general_canonical_lift_actions
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (m₁ m₂ : Marked.{u, v} R) :
    let F₁ := canonicalMarkingLiftGeneral R hp m₁
    let F₂ := canonicalMarkingLiftGeneral R hp m₂
    mk m₁ = mk m₂ ↔
      ∀ γ ∈ Γ, ∀ τ : ℍ, F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ) :=
  (mk_eq_mk_iff_sourceCarrierRepresentatives m₁ m₂).trans
    (mk_eq_mk_iff_canonical_lift_actions R hp hfixed
      m₁.sourceCarrierRepresentative m₂.sourceCarrierRepresentative)

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
