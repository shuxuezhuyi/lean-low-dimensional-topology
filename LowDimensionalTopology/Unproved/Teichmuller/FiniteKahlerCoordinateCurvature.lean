module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Finite Kähler coordinate definitions and classical comparison.
The final Prop is an independent classical theorem obligation, not an axiom.
Importing this file supplies definitions without a proof of that Prop. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder ContDiff Matrix.Norms.Elementwise

namespace LowDimensionalTopology.Unproved.Teichmuller.FiniteKahlerCoordinateContract

abbrev E (n : ℕ) := Fin n → ℂ
abbrev Coeff (n : ℕ) := E n → Matrix (Fin n) (Fin n) ℂ

def basis {n : ℕ} (j : Fin n) : E n := Pi.single j 1

def hermitian {n : ℕ} (H : Coeff n) (x u v : E n) : ℂ :=
  ∑ j, ∑ k, u j * H x j k * conj (v k)

def metric {n : ℕ} (H : Coeff n) (x u v : E n) : ℝ :=
  2 * (hermitian H x u v).re

def omega {n : ℕ} (H : Coeff n) (x u v : E n) : ℝ :=
  metric H x (Complex.I • u) v

def dz {n : ℕ} (f : E n → ℂ) (l : Fin n) (x : E n) : ℂ :=
  (fderiv ℝ f x (basis l) -
    Complex.I * fderiv ℝ f x (Complex.I • basis l)) / 2

def dbar {n : ℕ} (f : E n → ℂ) (l : Fin n) (x : E n) : ℂ :=
  (fderiv ℝ f x (basis l) +
    Complex.I * fderiv ℝ f x (Complex.I • basis l)) / 2

def gamma {n : ℕ} (H : Coeff n) (x : E n) (j k l : Fin n) : ℂ :=
  ∑ m, (H x)⁻¹ m j * dz (fun t => H t k m) l x

def mixed {n : ℕ} (H : Coeff n) (x : E n) (j k l m : Fin n) : ℂ :=
  -dbar (fun t => gamma H t j k l) m x

def lowered {n : ℕ} (H : Coeff n) (x : E n) (j k l m : Fin n) : ℂ :=
  -∑ r, H x j r * conj (mixed H x r k m l)

def lower4 {n : ℕ} (H : Coeff n) (x u v w z : E n) : ℂ :=
  ∑ j, ∑ k, ∑ l, ∑ m,
    lowered H x j k l m * u j * conj (v k) * w l * conj (z m)

def ricci {n : ℕ} (H : Coeff n) (x : E n) (j k : Fin n) : ℂ :=
  ∑ l, mixed H x l j l k

def ricciQ {n : ℕ} (H : Coeff n) (x v : E n) : ℂ :=
  ∑ j, ∑ k, ricci H x j k * v j * conj (v k)

def bookScalar {n : ℕ} (H : Coeff n) (x : E n) : ℂ :=
  ∑ j, ∑ k, (H x)⁻¹ k j * ricci H x j k

-- Real metric duality, independently defined before using gamma or mixed.
-- For positive definite H x and real-linear alpha, this is the unique metric dual of alpha.
def sharp {n : ℕ} (H : Coeff n) (x : E n) (alpha : E n → ℝ) : E n :=
  fun j => ∑ m,
    (((alpha (basis m) : ℂ) +
      Complex.I * (alpha (Complex.I • basis m) : ℂ)) / 2) * (H x)⁻¹ m j

-- Constant-field Koszul formula: this uses only the REAL metric and its dual.
def koszul {n : ℕ} (H : Coeff n) (x u v : E n) : E n :=
  sharp H x (fun w =>
    (fderiv ℝ (fun t => metric H t v w) x u +
      fderiv ℝ (fun t => metric H t u w) x v -
      fderiv ℝ (fun t => metric H t u v) x w) / 2)

def nabla {n : ℕ} (H : Coeff n) (X Y : E n → E n) (x : E n) : E n :=
  fderiv ℝ Y x (X x) + koszul H x (X x) (Y x)

-- R(u,v)w = nabla_u nabla_v w - nabla_v nabla_u w on constant fields.
def realCurvature {n : ℕ} (H : Coeff n) (x u v w : E n) : E n :=
  fderiv ℝ (fun t => koszul H t v w) x u -
    fderiv ℝ (fun t => koszul H t u w) x v +
    koszul H x u (koszul H x v w) - koszul H x v (koszul H x u w)

-- Real trace in the basis e_j, i e_j. No metric orthonormality is assumed.
def realRicci {n : ℕ} (H : Coeff n) (x u v : E n) : ℝ :=
  ∑ j, (((realCurvature H x (basis j) u v) j).re +
    ((realCurvature H x (Complex.I • basis j) u v) j).im)

def realScalar {n : ℕ} (H : Coeff n) (x : E n) : ℝ :=
  ∑ j,
    (realRicci H x (sharp H x (fun w => (w j).re)) (basis j) +
      realRicci H x (sharp H x (fun w => (w j).im)) (Complex.I • basis j))

/-- The independent finite-coordinate Kähler theorem cited by the book.
Every premise is regularity, positivity or closedness of a genuine metric.
Every conclusion is a fixed identity; no sign or WP object occurs. -/
def ClassicalFiniteKahlerCoordinateCurvature : Prop :=
  ∀ (n : ℕ) (domain : Set (E n)) (H : Coeff n),
    IsOpen domain →
    ContDiffOn ℝ ∞ H domain →
    (∀ x ∈ domain, (H x).PosDef) →
    (∀ x ∈ domain, ∀ u v w : E n,
      fderiv ℝ (fun t => omega H t v w) x u -
        fderiv ℝ (fun t => omega H t u w) x v +
        fderiv ℝ (fun t => omega H t u v) x w = 0) →
    (∀ u v : E n, ContDiffOn ℝ ∞ (fun t => koszul H t u v) domain) ∧
    ∀ x ∈ domain,
      (∀ u v : E n, koszul H x u v = koszul H x v u) ∧
      (∀ u v w : E n,
        fderiv ℝ (fun t => metric H t v w) x u =
          metric H x (koszul H x u v) w + metric H x v (koszul H x u w)) ∧
      (∀ u v : E n, koszul H x u (Complex.I • v) =
        Complex.I • koszul H x u v) ∧
      (∀ (u v : E n) (j : Fin n),
        koszul H x u v j = ∑ k, ∑ l, gamma H x j k l * v k * u l) ∧
      (∀ (u v w : E n) (j : Fin n),
        realCurvature H x u v w j = ∑ k, ∑ l, ∑ m,
          mixed H x j k l m * w k * (u l * conj (v m) - v l * conj (u m))) ∧
      (∀ u v : E n, (lower4 H x u u v v).im = 0) ∧
      (∀ v : E n, (ricciQ H x v).im = 0 ∧
        realRicci H x v v = 2 * (ricciQ H x v).re) ∧
      ((bookScalar H x).im = 0 ∧ realScalar H x = 2 * (bookScalar H x).re) ∧
      (∀ v : E n, v ≠ 0 →
        metric H x (realCurvature H x v (Complex.I • v) (Complex.I • v)) v /
          (metric H x v v * metric H x (Complex.I • v) (Complex.I • v) -
            (metric H x v (Complex.I • v)) ^ 2) =
        -(lower4 H x v v v v).re / (hermitian H x v v).re ^ 2)

end LowDimensionalTopology.Unproved.Teichmuller.FiniteKahlerCoordinateContract
