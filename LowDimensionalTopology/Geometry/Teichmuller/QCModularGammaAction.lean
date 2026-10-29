module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceGammaChange
public import LowDimensionalTopology.Geometry.Teichmuller.SourceQCModularAction
public import Mathlib.Algebra.Group.End

/-!
# The full QC mapping class action on the original group Teichmuller space

The acting group is the actual quotient of ALL quasiconformal surface
self-homeomorphisms by free homotopy to the identity. Its original action
is transported through the actual normalized-lift equivalence. Each
representative acts by the original reference-change map, and every
quotient class acts biholomorphically and preserves the original
Teichmuller distance. The actual original group QC metric is preserved too.

This file does not identify that surface mapping class group with the
separately defined quotient of upper-plane normalizers by a boundary deck
relation. In particular it does not substitute a smooth mapping class group
for the group of all quasiconformal self-homeomorphisms.

The covering and marked-quotient APIs reuse Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

local notation "hP" => canonicalHandleGroupPresentation g
local notation "hfree" => LiZhongQC.s27g_actsFreely hp
local notation "Q" => sourceGammaEquiv R hg hgenus hP hΓ hfree hp
local notation "Z" => Fin (3*g-3) → ℂ

/-- The actual ALL-QC surface quotient group acts on the original group space,
through the proved original normalized-lift equivalence. -/
def gammaModularRepresentation :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    SourceQCModular.ModularGroup X →* Equiv.Perm (LiZhongQC.TeichGamma Γ) := by
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  exact (Q).symm.permCongrHom.toMonoidHom.comp (SourceQCModular.representation X)

/-- Every transformed point has precisely the original surface quotient action. -/
theorem gammaModularRepresentation_source :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ (γ : SourceQCModular.ModularGroup X) (a : LiZhongQC.TeichGamma Γ),
      Q (gammaModularRepresentation R hg hgenus hΓ hp γ a) = γ • Q a := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro γ a
  exact (Q).apply_symm_apply _

/-- The representative's permutation is exactly the original reference map,
with no arbitrary holomorphic map or lift supplied as an extra datum. -/
theorem gammaModularRepresentation_mk :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ f : SourceQCModular.Aut X,
      gammaModularRepresentation R hg hgenus hΓ hp (SourceQCModular.mk f) =
        referenceGammaEquiv R R hg hgenus hgenus f.val f.property hΓ hΓ hp hp := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro f
  let S := sourceEquiv R hg hgenus hP
  let T := SourceReferenceChange.quotientMap f.val f.property
  apply Equiv.ext
  intro a
  change (Q).symm (T (Q a)) =
    (Q).symm (S (S.symm (T (S (S.symm (Q a))))))
  exact (congrArg (Q).symm
    ((S.apply_symm_apply (T (S (S.symm (Q a))))).trans
      (congrArg T (S.apply_symm_apply (Q a))))).symm

/-- Every class of all QC self-homeomorphisms preserves the literal original
half-log Teichmuller distance, on every pair of original group classes. -/
theorem gammaModularRepresentation_distance :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ (γ : SourceQCModular.ModularGroup X) (a b : LiZhongQC.TeichGamma Γ),
      LiZhongQC.teichDistanceGamma
        (gammaModularRepresentation R hg hgenus hΓ hp γ a)
        (gammaModularRepresentation R hg hgenus hΓ hp γ b) =
      LiZhongQC.teichDistanceGamma a b := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro γ a b
  exact (sourceGammaEquiv_distance R hg hgenus hP hΓ hfree hp _ _).trans
    ((congrArg₂ LiZhongQC.teichDistance
      (gammaModularRepresentation_source R hg hgenus hΓ hp γ a)
      (gammaModularRepresentation_source R hg hgenus hΓ hp γ b)).trans
      ((SourceQCModular.teichDistance_smul γ (Q a) (Q b)).trans
        (sourceGammaEquiv_distance R hg hgenus hP hΓ hfree hp a b).symm))

/-- All genuine QC modular classes act biholomorphically and isometrically on
the original group Teichmuller space with its original QC metric and Bers atlas. -/
theorem gammaModularRepresentation_biholomorphic_isometry :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := gammaQCMetricSpace R hg hgenus hΓ hfree hp
    letI := gammaBersChartedSpace R hg hgenus hΓ hfree hp
    ∀ γ : SourceQCModular.ModularGroup X,
      (ContMDiff 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω (gammaModularRepresentation R hg hgenus hΓ hp γ) ∧
        ContMDiff 𝓘(ℂ, Z) 𝓘(ℂ, Z) ω (gammaModularRepresentation R hg hgenus hΓ hp γ).symm) ∧
      Isometry (gammaModularRepresentation R hg hgenus hΓ hp γ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := gammaQCMetricSpace R hg hgenus hΓ hfree hp
  let := gammaBersChartedSpace R hg hgenus hΓ hfree hp
  intro γ
  constructor
  · refine Quotient.inductionOn γ ?_
    intro f
    obtain ⟨τ, hτ⟩ := hp.2.2.1 (f.val (p UpperHalfPlane.I))
    obtain ⟨w, hw, _⟩ := LiZhongQC.exists_lift hp hp f.val UpperHalfPlane.I τ hτ
    have hF := referenceGammaEquiv_contMDiff_bothDirections R R hg hgenus hgenus
      f.val f.property hΓ hΓ hp hp w hw
    have he := gammaModularRepresentation_mk R hg hgenus hΓ hp f
    exact ⟨hF.1.congr (fun a => congrArg (fun T : Equiv.Perm (LiZhongQC.TeichGamma Γ) => T a) he),
      hF.2.congr (fun a => congrArg (fun T : Equiv.Perm (LiZhongQC.TeichGamma Γ) => T.symm a) he)⟩
  · apply Isometry.of_dist_eq
    intro a b
    exact (gammaQCMetricSpace_dist R hg hgenus hΓ hfree hp _ _).trans
      ((congrArg (fun t : ℝ => 2 * t)
        (gammaModularRepresentation_distance R hg hgenus hΓ hp γ a b)).trans
        (gammaQCMetricSpace_dist R hg hgenus hΓ hfree hp a b).symm)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
