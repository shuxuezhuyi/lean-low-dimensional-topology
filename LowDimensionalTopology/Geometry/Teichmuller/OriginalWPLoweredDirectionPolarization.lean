module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSourceKernels
public import Mathlib.Tactic.Ring

/-!
# Finite polarization of the actual lowered WP contraction

With its first two vectors fixed, the unchanged lowered expression is
linear and conjugate linear in the last two vectors. Four diagonal complex
directions recover every mixed pair without a Hermitian-symmetry premise.
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

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C4" => nativeWeilPeterssonLoweredContraction R hp hg hgenus hΓ hfree hsmooth

/-- Four actual diagonal directions recover the last mixed pair of the
original lowered contraction, with all inverse and connection terms intact. -/
theorem nativeWeilPeterssonLoweredContraction_last_polarization
    (a : TeichmullerSpace.{0,0} R) (u v w s t : E) :
    let Q := fun x : E => C4 a u v x x t
    C4 a u v w s t =
      (Q (w + s) - Q (w - s) +
        Complex.I * Q (w + Complex.I • s) - Complex.I * Q (w - Complex.I • s)) / 4 := by
  classical
  dsimp only
  let B := fun x y : E => C4 a u v x y t
  have hadd₁ (x y z : E) : B (x + y) z = B x z + B y z := by
    simp only [B, nativeWeilPeterssonLoweredContraction, Pi.add_apply,
      mul_add, add_mul, Finset.sum_add_distrib]
  have hadd₂ (x y z : E) : B x (y + z) = B x y + B x z := by
    simp only [B, nativeWeilPeterssonLoweredContraction, Pi.add_apply,
      map_add, mul_add, Finset.sum_add_distrib]
  have hsmul₁ (c : ℂ) (x y : E) : B (c • x) y = c * B x y := by
    simp only [B, nativeWeilPeterssonLoweredContraction, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hsmul₂ (c : ℂ) (x y : E) : B x (c • y) = conj c * B x y := by
    simp only [B, nativeWeilPeterssonLoweredContraction, Pi.smul_apply,
      smul_eq_mul, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hsub (x y : E) : x - y = x + (-1 : ℂ) • y := by
    simp only [neg_one_smul, sub_eq_add_neg]
  change B w s =
    (B (w + s) (w + s) - B (w - s) (w - s) +
      Complex.I * B (w + Complex.I • s) (w + Complex.I • s) -
      Complex.I * B (w - Complex.I • s) (w - Complex.I • s)) / 4
  apply (eq_div_iff (by norm_num : (4 : ℂ) ≠ 0)).2
  rw [hsub w s, hsub w (Complex.I • s)]
  simp only [hadd₁, hadd₂, hsmul₁, hsmul₂, map_neg, map_one, Complex.conj_I]
  ring_nf; simp only [Complex.I_sq]; ring

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
