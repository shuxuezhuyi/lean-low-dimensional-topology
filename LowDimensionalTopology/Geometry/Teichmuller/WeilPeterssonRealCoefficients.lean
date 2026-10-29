module

public import LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
public import Mathlib.Tactic.Ring

/-!
# Actual real WP coordinate pairings under the explicit analytic input

These consumers prove the real-part and finite-coordinate consequences of
the named local smoothness obligation. They do not prove that obligation.
The original source family, actual chart differential and English factor 2
are retained throughout.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "H" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "coeff" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "realPair" => nativeWeilPeterssonRealCoordinatePairing R hp hg hgenus hΓ hfree hsmooth

/-- Every actual twice-real-part metric coefficient is smooth under the named
analytic input, with the English normalization retained. -/
theorem contDiffOn_nativeWeilPeterssonRealCoefficient_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (j k : Fin (3*g-3)) :
    ContDiffOn ℝ ∞ (fun t => 2 * (coeff a j k t).re) (chart a).target := by
  exact contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn (hWP a j k))

/-- The true original Hermitian form, on arbitrary fixed coordinate vectors,
is its finite coefficient expansion. This uses only the existing Core laws. -/
theorem nativeWeilPeterssonRealCoordinatePairing_eq_sum
    (a : TeichmullerSpace.{0,0} R) (v w t : E) :
    realPair a v w t =
      2 * (∑ j, ∑ k, v j * conj (w k) * coeff a j k t).re := by
  classical
  let := C
  let q := (chart a).symm t
  let c := H q
  let L := K q
  let : InnerProductSpace.Core ℂ (TangentSpace TI q) := c
  have hleft (s : Finset (Fin (3*g-3))) (f : Fin (3*g-3) → TangentSpace TI q)
      (y : TangentSpace TI q) :
      c.inner (∑ i ∈ s, f i) y = ∑ i ∈ s, c.inner (f i) y := by
    let A : TangentSpace TI q →+ ℂ :=
      { toFun := fun x => c.inner x y
        map_zero' := InnerProductSpace.Core.inner_zero_left y
        map_add' := fun x z => c.add_left x z y }
    exact map_sum A f s
  have hright (s : Finset (Fin (3*g-3))) (f : Fin (3*g-3) → TangentSpace TI q)
      (x : TangentSpace TI q) :
      c.inner x (∑ i ∈ s, f i) = ∑ i ∈ s, c.inner x (f i) := by
    calc
      c.inner x (∑ i ∈ s, f i) = conj (c.inner (∑ i ∈ s, f i) x) :=
        (c.conj_inner_symm x _).symm
      _ = conj (∑ i ∈ s, c.inner (f i) x) := congrArg conj (hleft s f x)
      _ = ∑ i ∈ s, c.inner x (f i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ => c.conj_inner_symm x (f i))
  have hdecomp (z : E) : L.symm z = ∑ j, z j • L.symm (Pi.single j 1) := by
    calc
      L.symm z = L.symm (∑ j, z j • Pi.single j 1) := congrArg L.symm (pi_eq_sum_univ' z)
      _ = ∑ j, z j • L.symm (Pi.single j 1) := by simp only [map_sum, map_smul]
  have hexpand : c.inner (L.symm w) (L.symm v) =
      ∑ j, ∑ k, v j * conj (w k) * c.inner
        (L.symm (Pi.single k 1)) (L.symm (Pi.single j 1)) := by
    rw [hdecomp w, hdecomp v, hright]
    apply Finset.sum_congr rfl
    intro j _
    rw [hleft]
    apply Finset.sum_congr rfl
    intro k _
    rw [c.smul_left, InnerProductSpace.Core.inner_smul_right]
    ring
  exact congrArg (fun z : ℂ => 2 * z.re) hexpand

/-- Every fixed actual coordinate pair has a smooth original real WP pairing.
The proof reconstructs it from all coefficients, rather than restating hWP. -/
theorem contDiffOn_nativeWeilPeterssonRealCoordinatePairing_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (v w : E) :
    ContDiffOn ℝ ∞ (realPair a v w) (chart a).target := by
  have hsum : ContDiffOn ℝ ∞
      (fun t => ∑ j, ∑ k, v j * conj (w k) * coeff a j k t) (chart a).target := by
    exact ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
      contDiffOn_const.mul (hWP a j k)
  have hreal : ContDiffOn ℝ ∞
      (fun t => 2 * (∑ j, ∑ k, v j * conj (w k) * coeff a j k t).re) (chart a).target :=
    contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn hsum)
  exact hreal.congr (fun t _ => nativeWeilPeterssonRealCoordinatePairing_eq_sum
    R hp hg hgenus hΓ hfree hsmooth a v w t)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
