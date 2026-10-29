/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCCoefficientRealization
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedMarkingActions
public import Mathlib.Tactic.Linarith

/-!
# The reduced coefficient quotient and actual general marked surfaces

The coefficient carrier consists of all actual compatible measurable
coefficients on the upper half-plane with some bound strictly below one.
The relation compares their actual normalized projective deck actions.
The original marked quotient is identified with this reduced quotient using
actual coefficient realization. Targets may be noncompact. The existing
common-universe normalized-lift interface is stated explicitly; the full
boundary-value coefficient quotient is a separate object.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller

open LiZhongQC

namespace ReducedCoefficient

/-- All raw compatible measurable coefficients with a genuine bound below one.
No target surface, lift, realization or off-half-plane restriction is supplied. -/
def Coefficient (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  {μ : ℂ → ℂ // (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff μ upperHalf k) ∧
    IsGammaCompatible Γ μ}

/-- The actual normalized symmetric solution restricts to a half-plane homeomorphism. -/
theorem exists_halfPlaneLift
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : Coefficient Γ) :
    ∃ F : ℍ ≃ₜ ℍ, ∀ τ, (F τ : ℂ) = s27u_fSym μ.val τ := by
  obtain ⟨k, hk0, hk1, hμ⟩ := μ.property.1
  obtain ⟨-, hN, hwK, -⟩ := s27u_sym_spec hk0 hk1 hμ
  have hU := (s27u_fSym_upperHalf hk0 hk1 hμ).1
  exact s27u_homeo_upper hwK hN.2.1 hU

/-- The chosen homeomorphism is constructed from the coefficient itself. -/
def halfPlaneLift
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : Coefficient Γ) : ℍ ≃ₜ ℍ :=
  Classical.choose (exists_halfPlaneLift μ)

theorem halfPlaneLift_spec
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : Coefficient Γ) :
    ∀ τ, (halfPlaneLift μ τ : ℂ) = s27u_fSym μ.val τ :=
  Classical.choose_spec (exists_halfPlaneLift μ)

/-- Any actual half-plane homeomorphism with this literal normalized solution
is the constructed one; this does not identify unrelated target coverings. -/
theorem halfPlaneLift_eq_of_spec
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : Coefficient Γ)
    {F : ℍ ≃ₜ ℍ} (hF : ∀ τ, (F τ : ℂ) = s27u_fSym μ.val τ) :
    halfPlaneLift μ = F := by
  apply Homeomorph.ext
  intro τ
  exact UpperHalfPlane.ext ((halfPlaneLift_spec μ τ).trans (hF τ).symm)

/-- Equality of every actual normalized projective deck action is the reduced
coefficient relation. It is stronger data than a supplied abstract group isomorphism. -/
def Equivalent {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (μ ν : Coefficient Γ) : Prop :=
  ∀ γ ∈ Γ, ∀ τ : ℍ,
    halfPlaneLift μ (γ • (halfPlaneLift μ).symm τ) =
      halfPlaneLift ν (γ • (halfPlaneLift ν).symm τ)

/-- The literal projective-action relation is an equivalence relation. -/
def setoid (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Setoid (Coefficient Γ) where
  r := Equivalent
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro μ γ hγ τ
      rfl
    · intro μ ν h γ hγ τ
      exact (h γ hγ τ).symm
    · intro μ ν η hμν hνη γ hγ τ
      exact (hμν γ hγ τ).trans (hνη γ hγ τ)

/-- The actual reduced coefficient quotient T#(Γ). -/
def Space (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  Quotient (setoid Γ)

def mk {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (μ : Coefficient Γ) : Space Γ := Quotient.mk _ μ

end ReducedCoefficient

namespace GeneralQC

universe u

/-- The lifted coefficient of the original actual marking, with its measurable
bound and all compatibility equations proved from that marking. -/
def markedCoefficient
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, u} R) :
    ReducedCoefficient.Coefficient Γ := by
  refine ⟨s27u_liftCoeff p m.marking, ?_, s27u_liftCoeff_isGammaCompatible hp m.marking⟩
  obtain ⟨K, hK⟩ := m.qc
  have hK1 : (1 : ℝ) ≤ K := hK.1
  exact ⟨(K - 1) / (K + 1), div_nonneg (by linarith) (by linarith),
    (div_lt_one (by linarith)).2 (by linarith), s27u_liftCoeff_isBeltramiCoeff hp hK⟩

/-- The coefficient construction retains the actual canonical normalized lift
of the very same original marking. -/
theorem halfPlaneLift_markedCoefficient
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, u} R) :
    ReducedCoefficient.halfPlaneLift (markedCoefficient R hp m) = canonicalMarkingLift R hp m := by
  apply ReducedCoefficient.halfPlaneLift_eq_of_spec
  exact (canonicalMarkingLift_spec R hp m).1

/-- Original marked equivalence is exactly the reduced relation of the actual
lifted coefficients. The fixed-triple condition is the original group convention. -/
theorem markedCoefficient_equivalent_iff
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (m n : Marked.{u, u} R) :
    m.Equivalent n ↔ ReducedCoefficient.Equivalent (markedCoefficient R hp m)
      (markedCoefficient R hp n) := by
  unfold ReducedCoefficient.Equivalent
  rw [halfPlaneLift_markedCoefficient R hp m, halfPlaneLift_markedCoefficient R hp n]
  exact marked_equivalent_iff_canonical_lift_actions R hp hfixed m n

/-- The actual marked quotient maps to the actual reduced coefficient quotient. -/
def toReducedCoefficientSpace
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ) :
    Space.{u, u} R → ReducedCoefficient.Space Γ :=
  Quotient.map' (markedCoefficient R hp)
    (fun m n h => (markedCoefficient_equivalent_iff R hp hfixed m n).mp h)

theorem toReducedCoefficientSpace_mk
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (m : Marked.{u, u} R) :
    toReducedCoefficientSpace R hp hfixed (mk m) =
      ReducedCoefficient.mk (markedCoefficient R hp m) := rfl

/-- Distinct actual marked classes cannot collapse in the reduced coefficient quotient. -/
theorem toReducedCoefficientSpace_injective
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ) :
    Function.Injective (toReducedCoefficientSpace R hp hfixed) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro m n h
  change (Quotient.mk (ReducedCoefficient.setoid Γ) (markedCoefficient R hp m)) =
    (Quotient.mk (ReducedCoefficient.setoid Γ) (markedCoefficient R hp n)) at h
  exact Quotient.sound ((markedCoefficient_equivalent_iff R hp hfixed m n).mpr
    (Quotient.exact h))

/-- Every raw valid coefficient has an actual marked representative. Its given
normalized lift and the internally canonical lift induce the same actions,
proved using reflexivity of this same marked surface and both actual coverings. -/
theorem exists_marked_reduced_representative
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (μ : ReducedCoefficient.Coefficient Γ) :
    ∃ m : Marked.{u, u} R,
      ReducedCoefficient.Equivalent (markedCoefficient R hp m) μ := by
  obtain ⟨k, hk0, hk1, hμ⟩ := μ.property.1
  obtain ⟨m, F, hF, hU, -, -, hL, -, -⟩ :=
    exists_marked_of_compatible_coefficient R hp hk0 hk1 hμ μ.property.2
  have hcanonical := canonicalMarkingLift_spec R hp m
  have hrefl : m.Equivalent m :=
    ⟨Homeomorph.refl m.target.carrier, isBiholomorphic_id, ContinuousMap.Homotopic.refl _⟩
  have hactions := (marked_equivalent_iff_normalized_lift_actions R hp hfixed m m
    hcanonical.2.1 hU hcanonical.2.2 hL).mp hrefl
  refine ⟨m, ?_⟩
  unfold ReducedCoefficient.Equivalent
  rw [halfPlaneLift_markedCoefficient R hp m,
    ReducedCoefficient.halfPlaneLift_eq_of_spec μ hF]
  exact hactions

/-- Surjectivity uses the actual realization of every raw coefficient, rather
than restricting the coefficient carrier to a supplied realizable range. -/
theorem toReducedCoefficientSpace_surjective
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ) :
    Function.Surjective (toReducedCoefficientSpace R hp hfixed) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro μ
  obtain ⟨m, hm⟩ := exists_marked_reduced_representative R hp hfixed μ
  refine ⟨mk m, ?_⟩
  change ReducedCoefficient.mk (markedCoefficient R hp m) = ReducedCoefficient.mk μ
  exact Quotient.sound hm

/-- The original actual common-universe QC-marked quotient identifies with the
actual reduced coefficient quotient T#(Γ). No compactness or boundary equality
identification is asserted by this equivalence. -/
def reducedCoefficientEquiv
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ) :
    Space.{u, u} R ≃ ReducedCoefficient.Space Γ :=
  Equiv.ofBijective (toReducedCoefficientSpace R hp hfixed)
    ⟨toReducedCoefficientSpace_injective R hp hfixed,
      toReducedCoefficientSpace_surjective R hp hfixed⟩

end GeneralQC
end LowDimensionalTopology.Geometry.Teichmuller
