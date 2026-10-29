/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.ReducedCoefficientSpace
public import LowDimensionalTopology.Geometry.Teichmuller.GammaSourceCoefficient

/-!
# The raw boundary quotient and the original coefficient Teichmüller space

All raw compatible upper-half-plane coefficients are retained. The actual
measurable encoding chooses a representative of the same almost-everywhere
class and extends it by zero; its normalized symmetric solution is proved
unchanged. This constructs the natural identification with the existing
source TeichGamma quotient. No compactness or reduced-action identification
is used in this module.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.ReducedCoefficient

open LiZhongQC

/-- Equality of the actual normalized boundary functions on the whole real line. -/
def BoundaryEquivalent
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ ν : Coefficient Γ) : Prop :=
  ∀ x : ℝ, s27u_fSym μ.val x = s27u_fSym ν.val x

/-- The boundary-function relation on all raw compatible coefficients. -/
def boundarySetoid (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    Setoid (Coefficient Γ) where
  r := BoundaryEquivalent
  iseqv := ⟨fun _ _ => rfl, fun h x => (h x).symm,
    fun h₁ h₂ x => (h₁ x).trans (h₂ x)⟩

/-- The actual quotient by equality of normalized boundary functions. -/
def BoundarySpace (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  Quotient (boundarySetoid Γ)

def boundaryMk {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (μ : Coefficient Γ) : BoundarySpace Γ := Quotient.mk _ μ

/-- Encode the actual measurable coefficient class and its own zero extension
into the existing source Gamma ball. The bound is chosen from the proved
existence property; it is not an additional input or an elimination into data. -/
def toSourceCoefficient
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : Coefficient Γ) :
    BeltramiGamma Γ :=
  GammaMeasurableBeltrami.toSourceGamma
    (GammaMeasurableBeltrami.ofCoefficientBall
      (Classical.choose_spec μ.property.1).1 (Classical.choose_spec μ.property.1).2.1
      (Classical.choose_spec μ.property.1).2.2 μ.property.2)

/-- The encoded source representative has the same actual coefficient almost
everywhere for restricted planar area on the upper half-plane. -/
theorem toSourceCoefficient_ae
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : Coefficient Γ) :
    (toSourceCoefficient μ).val.val =ᵐ[volume.restrict upperHalf] μ.val := by
  apply GammaMeasurableBeltrami.ae_plane_iff.2
  have hAE := GammaMeasurableBeltrami.ofCoefficient_coe_ae
    (Classical.choose_spec μ.property.1).2.2 μ.property.2
  filter_upwards [hAE] with z hz
  simpa only [toSourceCoefficient, GammaMeasurableBeltrami.toSourceGamma,
    GammaMeasurableBeltrami.ofCoefficientBall,
    GammaMeasurableBeltrami.planeRepresentative_coe] using hz

/-- The actual normalized symmetric solution survives the measurable encoding
as equality on the entire complex plane. -/
theorem toSourceCoefficient_fSym
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : Coefficient Γ) :
    s27u_fSym (toSourceCoefficient μ).val.val = s27u_fSym μ.val := by
  obtain ⟨k, hk0, hk1, hencoded⟩ := bg_beltramiH_upper (toSourceCoefficient μ).val
  obtain ⟨l, hl0, hl1, hμ⟩ := μ.property.1
  exact s27u_fSym_congr_ae hk0 hk1 hencoded hl0 hl1 hμ (toSourceCoefficient_ae μ)

/-- The original source relation is precisely the raw boundary relation,
proved for the actual encoding rather than a supplied set bijection. -/
theorem toSourceCoefficient_related_iff
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ ν : Coefficient Γ) :
    (teichSetoidGamma Γ).r (toSourceCoefficient μ) (toSourceCoefficient ν) ↔
      BoundaryEquivalent μ ν := by
  change (∀ x : ℝ,
    fMuSym (toSourceCoefficient μ).val.val x =
      fMuSym (toSourceCoefficient ν).val.val x) ↔ BoundaryEquivalent μ ν
  simp only [← s33v_fSym_eq, toSourceCoefficient_fSym, BoundaryEquivalent]

/-- The natural map sends each raw boundary class to its actual encoded
coefficient class in the existing source TeichGamma. -/
def boundarySourceMap
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    BoundarySpace Γ → TeichGamma Γ :=
  Quotient.map' toSourceCoefficient
    (fun μ ν h => (toSourceCoefficient_related_iff μ ν).mpr h)

theorem boundarySourceMap_mk
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : Coefficient Γ) :
    boundarySourceMap Γ (boundaryMk μ) =
      Quotient.mk (teichSetoidGamma Γ) (toSourceCoefficient μ) := rfl

/-- The natural map reflects the exact original boundary relation. -/
theorem boundarySourceMap_injective
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    Function.Injective (boundarySourceMap Γ) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro μ ν h
  change Quotient.mk (teichSetoidGamma Γ) (toSourceCoefficient μ) =
    Quotient.mk (teichSetoidGamma Γ) (toSourceCoefficient ν) at h
  exact Quotient.sound ((toSourceCoefficient_related_iff μ ν).mp (Quotient.exact h))

/-- Any original source Gamma coefficient is itself one of the raw compatible
upper-half-plane coefficients; no realizability restriction is added. -/
def ofSourceCoefficient
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (ρ : BeltramiGamma Γ) :
    Coefficient Γ :=
  ⟨ρ.val.val, bg_beltramiH_upper ρ.val, ρ.property⟩

/-- Any original source representative almost everywhere equal to the raw
coefficient gives the same exact source quotient class as its natural encoding. -/
theorem toSourceCoefficient_class_eq_of_ae
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (μ : Coefficient Γ) (ρ : BeltramiGamma Γ)
    (h : μ.val =ᵐ[volume.restrict upperHalf] ρ.val.val) :
    Quotient.mk (teichSetoidGamma Γ) (toSourceCoefficient μ) =
      Quotient.mk (teichSetoidGamma Γ) ρ := by
  obtain ⟨k, hk0, hk1, hencoded⟩ := bg_beltramiH_upper (toSourceCoefficient μ).val
  obtain ⟨l, hl0, hl1, hρ⟩ := bg_beltramiH_upper ρ.val
  have heq := s27u_fSym_congr_ae hk0 hk1 hencoded hl0 hl1 hρ
    ((toSourceCoefficient_ae μ).trans h)
  apply Quotient.sound
  intro x
  simpa only [← s33v_fSym_eq] using congrFun heq (x : ℂ)

/-- Every actual original source class is reached by encoding its own raw
coefficient, with the quotient equality proved from its unchanged AE class. -/
theorem boundarySourceMap_surjective
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    Function.Surjective (boundarySourceMap Γ) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro ρ
  refine ⟨boundaryMk (ofSourceCoefficient ρ), ?_⟩
  change Quotient.mk (teichSetoidGamma Γ)
      (toSourceCoefficient (ofSourceCoefficient ρ)) =
    Quotient.mk (teichSetoidGamma Γ) ρ
  exact toSourceCoefficient_class_eq_of_ae (ofSourceCoefficient ρ) ρ
    (Eventually.of_forall fun _ => rfl)

/-- The natural identification of the all-raw boundary quotient with the
existing original Gamma Teichmüller space. No compactness is required. -/
def boundarySourceEquiv
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    BoundarySpace Γ ≃ TeichGamma Γ :=
  Equiv.ofBijective (boundarySourceMap Γ)
    ⟨boundarySourceMap_injective Γ, boundarySourceMap_surjective Γ⟩

/-- This equivalence sends the given raw class to the literal encoded source
class; the result is not an unrelated cardinality equivalence. -/
theorem boundarySourceEquiv_mk
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : Coefficient Γ) :
    boundarySourceEquiv Γ (boundaryMk μ) =
      Quotient.mk (teichSetoidGamma Γ) (toSourceCoefficient μ) := rfl

end LowDimensionalTopology.Geometry.Teichmuller.ReducedCoefficient
