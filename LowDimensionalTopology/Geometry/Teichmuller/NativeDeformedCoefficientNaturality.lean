module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeGammaCoefficientTransport
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# The deformed coefficient codomain depends on the original Teichmüller point

Actual normalized conjugacy representations agree when the original
coefficients represent the same Teichmüller point. The chosen real special
linear lift subgroups can differ by central signs; their actual native
compatible submodules nevertheless coincide. The resulting identification
retains every coefficient class and its original essential norm.

This proves a codomain identification, not the remaining assertion that
harmonic tangent transports are independent of the representative.
The conjugacy representation comparison uses Wu Xiaobin's LiZhongQC source,
Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The tensor phase is unchanged by the central sign in the real matrix lift. -/
theorem phase_neg (γ : Deck) (z : ℍ) : phase (-γ) z = phase γ z := by
  have hd : denominator (-γ) z = -denominator γ z := by
    simp only [denominator, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply,
      Complex.ofReal_neg]
    ring
  simp only [phase, hd, neg_sq]

/-- Equal genuine upper-half-plane actions induce the same actual coefficient operator. -/
theorem pullback_eq_of_same_action {γ δ : Deck} (h : ∀ z : ℍ, γ • z = δ • z) :
    GammaMeasurableBeltrami.pullback γ = GammaMeasurableBeltrami.pullback δ := by
  rcases LiZhongQC.b33_d_eq_or_eq_neg h with he | he
  · rw [he]
  · rw [he] at h ⊢
    ext μ
    filter_upwards [pullback_coe_ae (-δ) μ, pullback_coe_ae δ μ] with z hneg hpos
    rw [hneg, hpos, phase_neg, h z]

/-- Same original Teichmüller point gives the same actual deformed Möbius actions,
without asserting equality of the chosen special-linear lift subgroups. -/
theorem deformedGroup_actions_of_samePoint (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν')) :
    ∀ A ∈ deformedGroup hΓ ν, ∃ B ∈ deformedGroup hΓ ν',
      ∀ z : ℍ, A • z = B • z := by
  have hc := (LiZhongQC.chi_eq_iff hΓ hdense (toSourceGamma ν)
    (toSourceGamma ν')).2 (Quotient.exact hpoint)
  intro A hA
  obtain ⟨γ, hγ, hrel⟩ := (deformedGroup_spec hΓ ν).2.2 A hA
  obtain ⟨B, hB, hrel'⟩ := (deformedGroup_spec hΓ ν').2.1 γ hγ
  refine ⟨B, hB, ?_⟩
  intro z
  obtain ⟨_, _, _, _, _, _, hU, _⟩ := normalizedMap_spec ν
  obtain ⟨_, _, _, _, _, _, hU', _⟩ := normalizedMap_spec ν'
  have hw : ∃ a ∈ LiZhongQC.upperHalf, normalizedMap ν a = (z : ℂ) := by
    change (z : ℂ) ∈ normalizedMap ν '' LiZhongQC.upperHalf
    rw [hU]
    exact z.im_pos
  have hw' : ∃ a ∈ LiZhongQC.upperHalf, normalizedMap ν' a = (z : ℂ) := by
    change (z : ℂ) ∈ normalizedMap ν' '' LiZhongQC.upperHalf
    rw [hU']
    exact z.im_pos
  have he := hc γ hγ z z.im_pos
  change normalizedMap ν
      (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
        (Function.invFunOn (normalizedMap ν) LiZhongQC.upperHalf z)) =
    normalizedMap ν'
      (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
        (Function.invFunOn (normalizedMap ν') LiZhongQC.upperHalf z)) at he
  rw [hrel _ (Function.invFunOn_mem hw), Function.invFunOn_eq hw,
    hrel' _ (Function.invFunOn_mem hw'), Function.invFunOn_eq hw'] at he
  apply UpperHalfPlane.ext
  simpa only [LiZhongQC.b33_d_mobiusFn_smul] using he

/-- The actual compatible coefficient submodule is independent of the same-point lift choice. -/
theorem compatibleSubmodule_eq_of_samePoint (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν')) :
    compatibleSubmodule (deformedGroup hΓ ν) =
      compatibleSubmodule (deformedGroup hΓ ν') := by
  ext μ
  constructor
  · intro hμ γ' hγ'
    obtain ⟨γ, hγ, hact⟩ :=
      deformedGroup_actions_of_samePoint hΓ hdense ν' ν hpoint.symm γ' hγ'
    rw [pullback_eq_of_same_action hact]
    exact hμ γ hγ
  · intro hμ γ hγ
    obtain ⟨γ', hγ', hact⟩ :=
      deformedGroup_actions_of_samePoint hΓ hdense ν ν' hpoint γ hγ
    rw [pullback_eq_of_same_action hact]
    exact hμ γ' hγ'

/-- The same-point deformed coefficient identification is the identity on actual classes. -/
def deformedCoefficientEquiv (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν')) :
    Space (deformedGroup hΓ ν) ≃L[ℂ] Space (deformedGroup hΓ ν') :=
  ContinuousLinearEquiv.ofEq _ _ (compatibleSubmodule_eq_of_samePoint hΓ hdense ν ν' hpoint)

@[simp] theorem deformedCoefficientEquiv_val (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν'))
    (μ : Space (deformedGroup hΓ ν)) :
    (deformedCoefficientEquiv hΓ hdense ν ν' hpoint μ).val = μ.val :=
  LinearEquiv.coe_ofEq_apply (compatibleSubmodule_eq_of_samePoint hΓ hdense ν ν' hpoint) μ

/-- The genuine same-point identification is isometric for the original infinity norms. -/
theorem norm_deformedCoefficientEquiv (hΓ : LiZhongQC.IsFuchsian Γ)
    (hdense : Dense (LiZhongQC.fuchsianFixedPoints Γ)) (ν ν' : Ball Γ)
    (hpoint : (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν'))
    (μ : Space (deformedGroup hΓ ν)) :
    ‖deformedCoefficientEquiv hΓ hdense ν ν' hpoint μ‖ = ‖μ‖ := by
  change ‖(deformedCoefficientEquiv hΓ hdense ν ν' hpoint μ).val‖ = ‖μ.val‖
  rw [deformedCoefficientEquiv_val]

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
