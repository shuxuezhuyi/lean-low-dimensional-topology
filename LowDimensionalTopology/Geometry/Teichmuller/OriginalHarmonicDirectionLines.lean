module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPulledQuadraticRiesz
public import Mathlib.Tactic.Ring

/-!
# Actual harmonic complex lines in the original finite coordinates

The quadratic differential representing a coefficient direction has the
conjugated coordinate weights. This identifies the entire normalized-map
line and its genuine small Ahlfors--Weill parameter, not just a first jet.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane ComplexConjugate BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami QuadraticBergman LiZhongQC

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

private theorem harmonicPlane_conjugate_sum {n : ℕ}
    (q : Fin n → HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (v : Fin n → ℂ) (z : ℂ) :
    harmonicPlane R p (∑ j, conj (v j) • q j) z =
      ∑ j, v j * harmonicPlane R p (q j) z := by
  classical
  simp only [harmonicPlane, uniformizedQuadratic, utm_liftQD,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every original finite coordinate line is the same scalar harmonic family
for the quadratic differential with conjugated coordinate weights. -/
theorem coordinateFamily_complex_line {n : ℕ}
    (q : Fin n → HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (v : Fin n → ℂ) (s : ℂ) :
    coordinateFamily R p q (s • v) =
      canonicalFamily R p (∑ j, conj (v j) • q j) s := by
  classical
  unfold coordinateFamily canonicalFamily
  congr 1
  funext z
  rw [harmonicPlane_conjugate_sum R p q v z]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem ofQuadratic_conjugate_sum {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {n : ℕ} (q : Fin n → HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (v : Fin n → ℂ) :
    NativeHarmonicBeltrami.ofQuadratic R p hp (∑ j, conj (v j) • q j) =
      ∑ j, v j • NativeHarmonicBeltrami.ofQuadratic R p hp (q j) := by
  classical
  have hzero : NativeHarmonicBeltrami.ofQuadratic R p hp
      (0 : HolomorphicQuadraticDifferential R.toRiemannAtlas) = 0 := by
    simpa only [zero_smul, map_zero] using
      NativeHarmonicBeltrami.ofQuadratic_smul R p hp (0 : ℂ)
        (0 : HolomorphicQuadraticDifferential R.toRiemannAtlas)
  have hsum (S : Finset (Fin n)) :
      NativeHarmonicBeltrami.ofQuadratic R p hp (∑ j ∈ S, conj (v j) • q j) =
        ∑ j ∈ S, v j • NativeHarmonicBeltrami.ofQuadratic R p hp (q j) := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using hzero
    | @insert j S hj ih =>
        simp only [Finset.sum_insert hj, NativeHarmonicBeltrami.ofQuadratic_add,
          NativeHarmonicBeltrami.ofQuadratic_smul, Complex.conj_conj, ih]
  exact hsum Finset.univ

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami HarmonicFirstVariation QuadraticBergman
open NormalizedCoefficientTransport LiZhongQC

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : IsFuchsian Γ)

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "q" => nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ
local notation "L" => weightedLinearBersCoordinates R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hp
local notation "N" => nativeWeilPeterssonHarmonicParameter
  (Γ := Γ) (p := p) (g := g) R hp hg hgenus hΓ

/-- The genuine small section parameter on every original complex line has
the same coefficient class and the identical normalized symmetric map. -/
theorem nativeWeilPeterssonHarmonicLine_parameter (v : E) (s : ℂ)
    (ht : ‖(L).symm (s • v)‖ < 1 / 2) :
    let Q := ∑ j, conj (v j) • q j
    let ν := N (s • v) ht
    (planeRepresentative ν.val.val =ᵐ[volume.restrict upperHalf]
      fun w => s * harmonicPlane R p Q w) ∧
      normalizedMap ν = canonicalFamily R p Q s := by
  classical
  dsimp only
  let Q := ∑ j, conj (v j) • q j
  let μ := NativeHarmonicBeltrami.ofQuadratic R p hp Q
  let ν : Ball Γ := N (s • v) ht
  have hQ : μ = BersWeighted.ahlforsWeill ((L).symm v) := by
    change NativeHarmonicBeltrami.ofQuadratic R p hp (∑ j, conj (v j) • q j) = _
    rw [HarmonicFirstVariation.ofQuadratic_conjugate_sum R p hp q v,
      nativeWeilPeterssonHarmonicFrame_sum R hp hg hgenus hΓ v]
  have hclass : ν.val = s • μ := by
    change BersWeighted.ahlforsWeill ((L).symm (s • v)) = s • μ
    rw [map_smul, map_smul, hQ]
  have hsmul : (s • μ).val = s • μ.val :=
    SetLike.val_smul (compatibleClosedSubmodule Γ) s μ
  have hae : planeRepresentative ν.val.val =ᵐ[volume.restrict upperHalf]
      fun w => s * harmonicPlane R p Q w := by
    rw [hclass, hsmul]
    filter_upwards [planeRepresentative_smul_ae s μ.val,
      NativeHarmonicBeltrami.planeRepresentative_ofQuadratic_ae R p hp Q]
      with w hs hQw
    have hs' : planeRepresentative (s • μ.val) w =
        s * planeRepresentative μ.val w := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hs
    exact hs'.trans (congrArg (fun a : ℂ => s * a) hQw)
  have hbound := planeRepresentative_isBeltramiCoeff ν.val.val
  have hraw : IsBeltramiCoeff (fun w => s * harmonicPlane R p Q w)
      upperHalf ‖ν.val.val‖ := by
    refine ⟨hbound.1.congr hae, ?_⟩
    filter_upwards [hae, hbound.2] with w hw hb
    rwa [← hw]
  refine ⟨hae, ?_⟩
  change s27u_fSym (planeRepresentative ν.val.val) =
    s27u_fSym (fun w => s * harmonicPlane R p Q w)
  exact s27u_fSym_congr_ae (norm_nonneg _) (Ball.norm_lt_one ν) hbound
    (norm_nonneg _) (Ball.norm_lt_one ν) hraw hae

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
