/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.ReducedCoefficientSpace
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralNormalizedMarkingActions
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCTargetRetargeting

/-!
# The original marked quotient in any target universe and reduced coefficients

The forward coefficient is definitionally the literal lifted coefficient of
the original marking. All its measurable bounds and compatibility equations
are proved by genuine biholomorphic target transport. Surjectivity realizes
every raw valid coefficient and then moves that actual target into the desired
universe, retaining the same coefficient. The original quotient is unchanged.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u v

/-- The value is the literal coefficient of the unchanged original marking;
only its proved validity is transported from the common-universe target. -/
def markedCoefficientGeneral
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, v} R) :
    ReducedCoefficient.Coefficient Γ :=
  ⟨s27u_liftCoeff p m.marking, (sourceCarrierRepresentative_liftCoeff R hp m) ▸
    (markedCoefficient R hp m.sourceCarrierRepresentative).property⟩

/-- The raw value is definitionally the original marking's coefficient. -/
@[simp] theorem markedCoefficientGeneral_val
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, v} R) :
    (markedCoefficientGeneral R hp m).val = s27u_liftCoeff p m.marking := rfl

/-- Its normalized solution is the actual canonical lift of the same original
marking, with no supplied target covering or lift. -/
theorem halfPlaneLift_markedCoefficientGeneral
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p) (m : Marked.{u, v} R) :
    ReducedCoefficient.halfPlaneLift (markedCoefficientGeneral R hp m) =
      canonicalMarkingLiftGeneral R hp m := by
  apply ReducedCoefficient.halfPlaneLift_eq_of_spec
  exact (canonicalMarkingLiftGeneral_spec R hp m).1

/-- The exact original relation is the reduced relation of its actual raw
coefficients, for independently sized targets. -/
theorem markedCoefficientGeneral_equivalent_iff
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (m n : Marked.{u, v} R) :
    m.Equivalent n ↔ ReducedCoefficient.Equivalent (markedCoefficientGeneral R hp m)
      (markedCoefficientGeneral R hp n) := by
  unfold ReducedCoefficient.Equivalent
  rw [halfPlaneLift_markedCoefficientGeneral R hp m,
    halfPlaneLift_markedCoefficientGeneral R hp n]
  exact marked_equivalent_iff_general_canonical_lift_actions R hp hfixed m n

/-- The forward quotient map sends each original class to the reduced class of
its literal coefficient, with no restriction to a realizable coefficient range. -/
def toReducedCoefficientSpaceGeneral
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ) :
    Space.{u, v} R → ReducedCoefficient.Space Γ :=
  Quotient.map' (markedCoefficientGeneral R hp)
    (fun m n h => (markedCoefficientGeneral_equivalent_iff R hp hfixed m n).mp h)

theorem toReducedCoefficientSpaceGeneral_mk
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (m : Marked.{u, v} R) :
    toReducedCoefficientSpaceGeneral R hp hfixed (mk m) =
      ReducedCoefficient.mk (markedCoefficientGeneral R hp m) := rfl

/-- Equality of the reduced classes reflects the original marked relation. -/
theorem toReducedCoefficientSpaceGeneral_injective
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ) :
    Function.Injective (toReducedCoefficientSpaceGeneral.{u, v} R hp hfixed) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro m n h
  change Quotient.mk (ReducedCoefficient.setoid Γ) (markedCoefficientGeneral R hp m) =
    Quotient.mk (ReducedCoefficient.setoid Γ) (markedCoefficientGeneral R hp n) at h
  exact Quotient.sound ((markedCoefficientGeneral_equivalent_iff R hp hfixed m n).mpr
    (Quotient.exact h))

/-- Every raw valid coefficient has a representative in the requested target
universe. The actual retargeting preserves its original lifted coefficient. -/
theorem toReducedCoefficientSpaceGeneral_surjective
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ) :
    Function.Surjective (toReducedCoefficientSpaceGeneral.{u, v} R hp hfixed) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro μ
  obtain ⟨m, hm⟩ := exists_marked_reduced_representative R hp hfixed μ
  let n : Marked.{u, v} R := Marked.targetUniverseRepresentative R hp m
  have hcoeff : markedCoefficientGeneral R hp n = markedCoefficient R hp m := by
    apply Subtype.ext
    exact targetUniverseRepresentative_liftCoeff R hp m
  refine ⟨mk n, ?_⟩
  change ReducedCoefficient.mk (markedCoefficientGeneral R hp n) = ReducedCoefficient.mk μ
  rw [hcoeff]
  exact Quotient.sound hm

/-- The natural equivalence from the unchanged original marked quotient in any
target universe to the all-raw reduced coefficient space T#(Γ). -/
def reducedCoefficientEquivGeneral
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ) :
    Space.{u, v} R ≃ ReducedCoefficient.Space Γ :=
  Equiv.ofBijective (toReducedCoefficientSpaceGeneral.{u, v} R hp hfixed)
    ⟨toReducedCoefficientSpaceGeneral_injective R hp hfixed,
      toReducedCoefficientSpaceGeneral_surjective R hp hfixed⟩

/-- The equivalence sends each actual original class to its own lifted
coefficient class, rather than to an unrelated cardinality representative. -/
theorem reducedCoefficientEquivGeneral_mk
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)
    (m : Marked.{u, v} R) :
    reducedCoefficientEquivGeneral R hp hfixed (mk m) =
      ReducedCoefficient.mk (markedCoefficientGeneral R hp m) := rfl

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
