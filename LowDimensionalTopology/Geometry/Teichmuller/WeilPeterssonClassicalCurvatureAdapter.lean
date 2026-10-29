module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonChristoffelTorsion
public import LowDimensionalTopology.Unproved.Teichmuller.FiniteKahlerCoordinateCurvature
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The classical finite Kähler coordinate comparison for the original WP matrix

The independent comparison starts with the real metric, its Koszul expression
and its commutator. The actual WP matrix supplies smoothness, positivity and
closedness of that same real fundamental form on the genuine Bers target.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport
open LowDimensionalTopology.Unproved.Teichmuller

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "H" => nativeWeilPeterssonLocalCoefficient
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "M" => nativeWeilPeterssonCoefficientMatrix
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "G" => nativeWeilPeterssonChristoffelExpression
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "U" => nativeWeilPeterssonMixedCurvatureExpression
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

/-- The actual entire coefficient matrix is smooth on its genuine chart target. -/
theorem contDiffOn_nativeWeilPeterssonClassicalMatrix
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    ContDiffOn ℝ ∞ M (chart (basePoint R)).target := by
  apply contDiffOn_pi.mpr
  intro j
  apply contDiffOn_pi.mpr
  intro k
  exact hWP (basePoint R) j k

/-- The classical contract's fundamental form is exactly the original Ω,
including its first-linear order and the English factor two. -/
theorem nativeWeilPeterssonClassicalOmega_eq (x u v : E) :
    FiniteKahlerCoordinateContract.omega M x u v = Ω x ![u,v] := by
  rw [nativeWeilPeterssonCoordinateForm_eq_finiteRealPairing
    R hp hg hgenus hΓ hfree hsmooth u v x]
  unfold FiniteKahlerCoordinateContract.omega FiniteKahlerCoordinateContract.metric
    FiniteKahlerCoordinateContract.hermitian
  apply congrArg (fun z : ℂ => 2 * z.re)
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change (Complex.I • u) j * H j k x * conj (v k) =
    (Complex.I • u) j * conj (v k) * H j k x
  ring

private theorem wp_classical_basis_I (l : I) :
    Complex.I • (Pi.single l 1 : E) = Pi.single l Complex.I := by
  ext i
  by_cases hi : i = l <;> simp [hi]

private theorem wp_classical_dz_eq (f : E → ℂ) (l : I) (x : E) :
    FiniteKahlerCoordinateContract.dz f l x =
      nativeWeilPeterssonCoordinateDz (g := g) f l x := by
  simp only [FiniteKahlerCoordinateContract.dz, FiniteKahlerCoordinateContract.basis,
    nativeWeilPeterssonCoordinateDz, wp_classical_basis_I]

private theorem wp_classical_dbar_eq (f : E → ℂ) (l : I) (x : E) :
    FiniteKahlerCoordinateContract.dbar f l x =
      nativeWeilPeterssonCoordinateDbar (g := g) f l x := by
  simp only [FiniteKahlerCoordinateContract.dbar, FiniteKahlerCoordinateContract.basis,
    nativeWeilPeterssonCoordinateDbar, wp_classical_basis_I]

/-- The original transposed-inverse convention is the one in the classical Γ. -/
theorem nativeWeilPeterssonClassicalGamma_eq (j k l : I) (x : E) :
    FiniteKahlerCoordinateContract.gamma M x j k l = G j k l x := by
  simp only [FiniteKahlerCoordinateContract.gamma, nativeWeilPeterssonChristoffelExpression,
    nativeWeilPeterssonRaisedInverseCoefficient, nativeWeilPeterssonCoefficientMatrix,
    wp_classical_dz_eq]

/-- The same actual U is minus the antiholomorphic derivative of that same Γ. -/
theorem nativeWeilPeterssonClassicalMixed_eq (j k l m : I) (x : E) :
    FiniteKahlerCoordinateContract.mixed M x j k l m = U j k l m x := by
  have hf : (fun t : E => FiniteKahlerCoordinateContract.gamma M t j k l) =
      (fun t : E => G j k l t) :=
    funext fun t => nativeWeilPeterssonClassicalGamma_eq R hp hg hgenus hΓ hfree hsmooth j k l t
  unfold FiniteKahlerCoordinateContract.mixed nativeWeilPeterssonMixedCurvatureExpression
  rw [hf, wp_classical_dbar_eq]

theorem wp_classical_cyclic_of_closed
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (x : E) (hx : x ∈ (chart (basePoint R)).target)
    (hc : extDerivWithin Ω (chart (basePoint R)).target x = 0) (u v w : E) :
    fderiv ℝ (fun t => FiniteKahlerCoordinateContract.omega M t v w) x u -
      fderiv ℝ (fun t => FiniteKahlerCoordinateContract.omega M t u w) x v +
      fderiv ℝ (fun t => FiniteKahlerCoordinateContract.omega M t u v) x w = 0 := by
  have hd : DifferentiableAt ℝ Ω x :=
    ((contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
      R hp hg hgenus hΓ hfree hsmooth hWP (basePoint R)).contDiffAt
        ((chart (basePoint R)).open_target.mem_nhds hx)).differentiableAt (by simp)
  have he : extDeriv Ω x = 0 := by
    simpa only [extDerivWithin,
      fderivWithin_of_isOpen (chart (basePoint R)).open_target hx, extDeriv] using hc
  have hf (a b : E) : (fun t : E => FiniteKahlerCoordinateContract.omega M t a b) =
      (fun t : E => Ω t ![a,b]) :=
    funext fun t => nativeWeilPeterssonClassicalOmega_eq R hp hg hgenus hΓ hfree hsmooth t a b
  simpa only [hf, fderiv_continuousAlternatingMap_apply_const_apply hd] using
    coordinateClosedTwoForm_cyclic hd he u v w

/-- The independent real Koszul commutator for the SAME original WP matrix
has the full three-direction formula in the actual native mixed coefficient.
Only the independent classical comparison is added to the old analytic inputs. -/
theorem nativeWeilPeterssonRealCurvature_eq_nativeMixed_of_classical
    (hclassical : FiniteKahlerCoordinateContract.ClassicalFiniteKahlerCoordinateCurvature)
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hvariation : ∀ ν : Ball Γ, Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      (deformedNativeSurface R hgenus hΓ hp ν)
      (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) (deformedGroup_spec hΓ ν).1
      (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (x : E) (hx : x ∈ (chart (basePoint R)).target) (u v w : E) (j : I) :
    FiniteKahlerCoordinateContract.realCurvature M x u v w j =
      ∑ k, ∑ l, ∑ m, U j k l m x * w k *
        (u l * conj (v m) - v l * conj (u m)) := by
  have hbook := nativeWeilPeterssonIsBookKahler_of_harmonicVariation
    R hp hg hgenus hΓ hfree hsmooth hWP hvariation hjets
  have hcyclic (t : E) (ht : t ∈ (chart (basePoint R)).target) (a b c : E) :=
    wp_classical_cyclic_of_closed R hp hg hgenus hΓ hfree hsmooth hWP t ht
      (hbook.2.2.2.2.2.2.2 t ht) a b c
  have h := hclassical (3*g-3) (chart (basePoint R)).target M
    (chart (basePoint R)).open_target
    (contDiffOn_nativeWeilPeterssonClassicalMatrix R hp hg hgenus hΓ hfree hsmooth hWP)
    (fun t _ => nativeWeilPeterssonCoefficientMatrix_posDef
      R hp hg hgenus hΓ hfree hsmooth (basePoint R) t) hcyclic
  have hcurv := (h.2 x hx).2.2.2.2.1 u v w j
  simpa only [nativeWeilPeterssonClassicalMixed_eq R hp hg hgenus hΓ hfree hsmooth] using hcurv

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
