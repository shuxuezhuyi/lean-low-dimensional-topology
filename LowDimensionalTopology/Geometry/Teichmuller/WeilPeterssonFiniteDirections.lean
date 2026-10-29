module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSourceBilinearDirections
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSesquilinearAbsolute
public import Mathlib.Tactic.Ring

/-!
# Finite original directions in the actual WP source kernels

The actual ordinary mixed-kernel convergence supplies the finite sums inside
both original integrals. Together with the actual principal-value bilinear
expansion, this gives the same four-direction kernel in the coordinate basis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane Manifold ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

private theorem sesquilinear_congr_ae {u u' v v' : ℍ → ℂ}
    (hu : u =ᵐ[flatArea] u') (hv : v =ᵐ[flatArea] v') (ζ z : ℍ) :
    sesquilinear u v ζ z = sesquilinear u' v' ζ z := by
  unfold sesquilinear
  apply integral_congr_ae
  filter_upwards [hv] with ξ hξ
  apply integral_congr_ae
  filter_upwards [hu] with η hη
  simp only [sesquilinearIntegrand, hη, hξ]

private theorem sesquilinear_finset {n : ℕ} (c d : Fin n → ℂ)
    (μ ν : Fin n → ℍ → ℂ) (ζ z : ℍ)
    (h : ∀ j k, SesquilinearIntegralExists (μ j) (ν k) ζ z) :
    sesquilinear (fun η => ∑ j, c j * μ j η)
        (fun ξ => ∑ k, d k * ν k ξ) ζ z =
      ∑ j, ∑ k, c j * conj (d k) * sesquilinear (μ j) (ν k) ζ z := by
  classical
  let J := fun j k ξ => ∫ η : ℍ, sesquilinearIntegrand (μ j) (ν k) ζ z ξ η ∂flatArea
  have hpoint (ξ η : ℍ) :
      sesquilinearIntegrand (fun η => ∑ j, c j * μ j η)
          (fun ξ => ∑ k, d k * ν k ξ) ζ z ξ η =
        ∑ j, ∑ k, c j * conj (d k) * sesquilinearIntegrand (μ j) (ν k) ζ z ξ η := by
    let Q := cauchySquare (conj (ξ : ℂ)) ζ * cauchySquare (conj (ξ : ℂ)) η *
      cauchySquare η (conj (z : ℂ))
    change Q * (∑ j, c j * μ j η) * conj (∑ k, d k * ν k ξ) =
      ∑ j, ∑ k, c j * conj (d k) * (Q * μ j η * conj (ν k ξ))
    rw [map_sum]
    calc
      _ = Q * ((∑ j, c j * μ j η) * (∑ k, conj (d k * ν k ξ))) := by ring
      _ = Q * (∑ j, ∑ k, (c j * μ j η) * conj (d k * ν k ξ)) := by
        rw [Finset.sum_mul_sum]
      _ = ∑ j, ∑ k, Q * ((c j * μ j η) * conj (d k * ν k ξ)) := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        simp only [map_mul]
        ring
  have hrow (j : Fin n) (ξ : ℍ) :
      Integrable (fun η : ℍ => ∑ k,
        c j * conj (d k) * sesquilinearIntegrand (μ j) (ν k) ζ z ξ η) flatArea :=
    integrable_finsetSum Finset.univ
      (fun k _ => ((h j k).1 ξ).const_mul (c j * conj (d k)))
  have hinner (ξ : ℍ) :
      (∫ η : ℍ, sesquilinearIntegrand (fun η => ∑ j, c j * μ j η)
          (fun ξ => ∑ k, d k * ν k ξ) ζ z ξ η ∂flatArea) =
        ∑ j, ∑ k, c j * conj (d k) * J j k ξ := by
    simp_rw [hpoint]
    rw [integral_finsetSum Finset.univ (fun j _ => hrow j ξ)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum Finset.univ
      (fun k _ => ((h j k).1 ξ).const_mul (c j * conj (d k)))]
    simp only [integral_const_mul, J]
  have hout (j : Fin n) :
      Integrable (fun ξ : ℍ => ∑ k, c j * conj (d k) * J j k ξ) flatArea :=
    integrable_finsetSum Finset.univ
      (fun k _ => (h j k).2.const_mul (c j * conj (d k)))
  change (∫ ξ : ℍ, ∫ η : ℍ,
      sesquilinearIntegrand (fun η => ∑ j, c j * μ j η)
        (fun ξ => ∑ k, d k * ν k ξ) ζ z ξ η ∂flatArea ∂flatArea) =
    ∑ j, ∑ k, c j * conj (d k) * (∫ ξ : ℍ, J j k ξ ∂flatArea)
  simp_rw [hinner]
  rw [integral_finsetSum Finset.univ (fun j _ => hout j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ
    (fun k _ => (h j k).2.const_mul (c j * conj (d k)))]
  simp only [integral_const_mul, J]

private theorem finite_four_contraction {n : ℕ}
    (S B : Fin n → Fin n → ℂ) (u v w s : Fin n → ℂ) :
    (∑ j, ∑ l, u j * w l * S j l) * conj (∑ k, ∑ m, v k * s m * S k m) +
        2 * (∑ j, ∑ k, u j * conj (v k) * B j k) *
          conj (∑ m, ∑ l, s m * conj (w l) * B m l) =
      ∑ j, ∑ k, ∑ l, ∑ m,
        (S j l * conj (S k m) + 2 * B j k * conj (B m l)) *
          u j * conj (v k) * w l * conj (s m) := by
  classical
  have hA : (∑ j, ∑ l, u j * w l * S j l) *
      conj (∑ k, ∑ m, v k * s m * S k m) =
      ∑ j, ∑ k, ∑ l, ∑ m,
        S j l * conj (S k m) * u j * conj (v k) * w l * conj (s m) := by
    simp only [map_sum, map_mul]
    simp_rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hB : (∑ j, ∑ k, u j * conj (v k) * B j k) *
      conj (∑ m, ∑ l, s m * conj (w l) * B m l) =
      ∑ j, ∑ k, ∑ l, ∑ m,
        B j k * conj (B m l) * u j * conj (v k) * w l * conj (s m) := by
    simp only [map_sum, map_mul, Complex.conj_conj]
    simp_rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    ring
  calc
    _ = (∑ j, ∑ l, u j * w l * S j l) *
        conj (∑ k, ∑ m, v k * s m * S k m) +
        2 * ((∑ j, ∑ k, u j * conj (v k) * B j k) *
          conj (∑ m, ∑ l, s m * conj (w l) * B m l)) := by ring
    _ = (∑ j, ∑ k, ∑ l, ∑ m,
        S j l * conj (S k m) * u j * conj (v k) * w l * conj (s m)) +
        2 * (∑ j, ∑ k, ∑ l, ∑ m,
          B j k * conj (B m l) * u j * conj (v k) * w l * conj (s m)) := by
      rw [hA, hB]
    _ = _ := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro m _
      ring

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

/-- The same actual ordinary mixed kernel is the double sesquilinear
coordinate sum, with each inner and outer integral supplied by convergence. -/
theorem nativeWeilPeterssonSourceSesquilinear_coordinate_expansion
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (u v : E) (ζ z : ℍ) :
    SourceKernel.sesquilinear (μ ν P F hF u) (μ ν P F hF v) ζ z =
      ∑ j : I, ∑ k : I, u j * conj (v k) *
        SourceKernel.sesquilinear (μ ν P F hF (Pi.single j 1))
          (μ ν P F hF (Pi.single k 1)) ζ z := by
  classical
  exact (SourceKernel.sesquilinear_congr_ae
    (nativeWeilPeterssonSourceDirection_finset_ae R hp hg hgenus hΓ hfree hsmooth ν P F hF u)
    (nativeWeilPeterssonSourceDirection_finset_ae R hp hg hgenus hΓ hfree hsmooth ν P F hF v)
    ζ z).trans
      (SourceKernel.sesquilinear_finset u v
        (fun j => μ ν P F hF (Pi.single j 1))
        (fun k => μ ν P F hF (Pi.single k 1)) ζ z
        (fun j k => nativeWeilPetersson_sesquilinearIntegralExists
          R hp hg hgenus hΓ hfree hsmooth ν P F hF (Pi.single j 1) (Pi.single k 1) ζ z))

/-- The unchanged actual four-direction kernel has the finite fourfold
coordinate contraction, with its original conjugate and mixed slot order. -/
theorem nativeWeilPeterssonSourceFour_coordinate_expansion
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (u v w s : E) (ζ z : ℍ) :
    SourceKernel.four (μ ν P F hF u) (μ ν P F hF v)
        (μ ν P F hF w) (μ ν P F hF s) ζ z =
      ∑ j : I, ∑ k : I, ∑ l : I, ∑ m : I,
        SourceKernel.four (μ ν P F hF (Pi.single j 1)) (μ ν P F hF (Pi.single k 1))
          (μ ν P F hF (Pi.single l 1)) (μ ν P F hF (Pi.single m 1)) ζ z *
          u j * conj (v k) * w l * conj (s m) := by
  classical
  let A := fun u v : E => SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF v) ζ z
  let B := fun u v : E => SourceKernel.sesquilinear (μ ν P F hF u) (μ ν P F hF v) ζ z
  let AA := fun j l : I => A (Pi.single j 1) (Pi.single l 1)
  let BB := fun j k : I => B (Pi.single j 1) (Pi.single k 1)
  have hA (u w : E) : A u w = ∑ j : I, ∑ l : I, u j * w l * AA j l :=
    nativeWeilPeterssonSourceBilinear_coordinate_expansion
      R hp hg hgenus hΓ hfree hsmooth ν P F hF u w ζ z
  have hB (u v : E) : B u v = ∑ j : I, ∑ k : I, u j * conj (v k) * BB j k :=
    nativeWeilPeterssonSourceSesquilinear_coordinate_expansion
      R hp hg hgenus hΓ hfree hsmooth ν P F hF u v ζ z
  have hSym (u w : E) : A u w + A w u =
      ∑ j : I, ∑ l : I, u j * w l * (AA j l + AA l j) := by
    have hswap : (∑ j : I, ∑ l : I, w j * u l * AA j l) =
        ∑ j : I, ∑ l : I, u j * w l * AA l j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hA u w, hA w u, hswap, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  change (A u w + A w u) * conj (A v s + A s v) + 2 * B u v * conj (B s w) =
    ∑ j, ∑ k, ∑ l, ∑ m,
      ((AA j l + AA l j) * conj (AA k m + AA m k) + 2 * BB j k * conj (BB m l)) *
        u j * conj (v k) * w l * conj (s m)
  rw [hSym u w, hSym v s, hB u v, hB s w]
  exact SourceKernel.finite_four_contraction (fun j l => AA j l + AA l j) BB u v w s

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
