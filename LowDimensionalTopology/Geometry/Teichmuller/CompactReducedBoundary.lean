/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC covering and normalized-solution APIs,
Apache-2.0, pinned upstream1c0d5473c020b66ed5106331a38a61536760b9b2;
see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.CoefficientBoundarySpace
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedLiftDeckActions
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCClosedCompatibility

/-!
# Compact references identify reduced and full-boundary coefficient classes

Every raw coefficient is actually realized on an original native target.
The actual compact-source boundary comparison then identifies equality of
normalized deck actions with equality on the entire real boundary. The
quotient map keeps the same coefficient. No target compactness, genus,
presentation, smoothing or abstract quotient bijectivity is supplied.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces LiZhongQC

namespace ReducedCoefficient

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)

include R hp in
/-- For this original compact reference, the actual reduced action relation
is exactly equality of the two actual symmetric solutions on every real point. -/
theorem equivalent_iff_boundary (μ ν : Coefficient Γ) :
    Equivalent μ ν ↔ BoundaryEquivalent μ ν := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.compactSpace
  obtain ⟨k, hk0, hk1, hμ⟩ := μ.property.1
  obtain ⟨l, hl0, hl1, hν⟩ := ν.property.1
  obtain ⟨mμ, Fμ, hFμ, hUμ, -, -, hLμ, -, -⟩ :=
    GeneralQC.exists_marked_of_compatible_coefficient
      (GeneralQC.Surface.ofRiemannSurface R.toRiemannSurface)
      hp hk0 hk1 hμ μ.property.2
  obtain ⟨mν, Fν, hFν, hUν, -, -, hLν, -, -⟩ :=
    GeneralQC.exists_marked_of_compatible_coefficient
      (GeneralQC.Surface.ofRiemannSurface R.toRiemannSurface)
      hp hl0 hl1 hν ν.property.2
  have hcompare := normalizedLift_deckActions_eq_iff_boundary hp hUμ hUν
    mμ.marking mν.marking hLμ hLν
  rw [conjugatedCoverAction_eq_iff] at hcompare
  unfold Equivalent BoundaryEquivalent
  rw [halfPlaneLift_eq_of_spec μ hFμ, halfPlaneLift_eq_of_spec ν hFν]
  constructor
  · intro h x
    have he := hcompare.mp h x
    change ((s27u_fSym μ.val x : ℂ) : ExtPlane) =
      ((s27u_fSym ν.val x : ℂ) : ExtPlane) at he
    exact OnePoint.coe_injective he
  · intro h
    apply hcompare.mpr
    intro x
    change ((s27u_fSym μ.val x : ℂ) : ExtPlane) =
      ((s27u_fSym ν.val x : ℂ) : ExtPlane)
    exact congrArg (fun z : ℂ => (z : ExtPlane)) (h x)

/-- The reduced class maps to the full-boundary class of the same coefficient. -/
def toBoundary : Space Γ → BoundarySpace Γ :=
  Quotient.map' id (fun μ ν h => (equivalent_iff_boundary R hp μ ν).mp h)

/-- The same coefficient also defines the inverse quotient map. -/
def fromBoundary : BoundarySpace Γ → Space Γ :=
  Quotient.map' id (fun μ ν h => (equivalent_iff_boundary R hp μ ν).mpr h)

/-- The two quotient relations coincide by the actual compact boundary theorem. -/
def boundaryEquiv : Space Γ ≃ BoundarySpace Γ where
  toFun := toBoundary R hp
  invFun := fromBoundary R hp
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro μ
    rfl
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro μ
    rfl

theorem boundaryEquiv_mk (μ : Coefficient Γ) :
    boundaryEquiv R hp (mk μ) = boundaryMk μ := rfl

theorem boundaryEquiv_symm_mk (μ : Coefficient Γ) :
    (boundaryEquiv R hp).symm (boundaryMk μ) = mk μ := rfl

end ReducedCoefficient

namespace GeneralQC

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)

/-- The actual original QC-marked quotient of the compact reference identifies
with the full-boundary coefficient quotient by the original lifted coefficient. -/
def closedBoundaryEquiv : ClosedSpace R ≃ ReducedCoefficient.BoundarySpace Γ :=
  (reducedCoefficientEquiv (Surface.ofRiemannSurface R.toRiemannSurface) hp hfixed).trans
    (ReducedCoefficient.boundaryEquiv R hp)

theorem closedBoundaryEquiv_mk (m : ClosedMarked R) :
    closedBoundaryEquiv R hp hfixed (mk m) =
      ReducedCoefficient.boundaryMk
        (markedCoefficient (Surface.ofRiemannSurface R.toRiemannSurface) hp m) := rfl

/-- The original coefficient class is sent to the actual source coefficient
quotient, retaining the same normalized boundary values. -/
def closedGammaEquiv : ClosedSpace R ≃ LiZhongQC.TeichGamma Γ :=
  (closedBoundaryEquiv R hp hfixed).trans (ReducedCoefficient.boundarySourceEquiv Γ)

/-- The actual forward map is the original marking's lifted coefficient class. -/
theorem closedGammaEquiv_mk (m : ClosedMarked R) :
    closedGammaEquiv R hp hfixed (mk m) =
      (Quotient.mk _ (ReducedCoefficient.toSourceCoefficient
        (markedCoefficient (Surface.ofRiemannSurface R.toRiemannSurface) hp m)) :
          LiZhongQC.TeichGamma Γ) := by
  change ReducedCoefficient.boundarySourceEquiv Γ
    (ReducedCoefficient.boundaryMk
      (markedCoefficient (Surface.ofRiemannSurface R.toRiemannSurface) hp m)) = _
  exact ReducedCoefficient.boundarySourceEquiv_mk _

/-- There is a representative of this actual source Gamma class whose raw
function is literally the lifted coefficient of the unchanged original marking
in the established closed-source repackaging. -/
theorem closedGammaEquiv_original_coefficient (m : ClosedMarked R) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ μ : LiZhongQC.BeltramiGamma Γ,
      μ.val.val = s27u_liftCoeff p (toClosedMarked R m).marking ∧
      closedGammaEquiv R hp hfixed (mk m) = Quotient.mk _ μ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨B, hB, hΓ⟩ := s27u_liftCoeff_beltramiH hp m.qc
  let μ : LiZhongQC.BeltramiGamma Γ := ⟨B, hΓ⟩
  refine ⟨μ, hB, ?_⟩
  rw [closedGammaEquiv_mk]
  apply ReducedCoefficient.toSourceCoefficient_class_eq_of_ae
  exact Filter.Eventually.of_forall fun z => congrFun hB.symm z

end GeneralQC
end LowDimensionalTopology.Geometry.Teichmuller
