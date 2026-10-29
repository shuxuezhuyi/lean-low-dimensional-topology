module

public import LowDimensionalTopology.External.LiZhongQC.Basic

/-!
# The two signed Green identities for a finite Jordan boundary

These identities reduce to classical real Green, whose proof is not
supplied here. The domain is bounded: an unrestricted open-set statement
is false without conditions at infinity. A disk instance of Green in
a Pompeiu argument does not by itself give this general statement.

The boundary data below are literal finite piecewise-C1 simple closed
paths. Orientation and the domain are determined by the actual normalized
Cauchy-kernel winding integrals. No boundary field asserts Green for an
arbitrary test function. Both area and boundary integrability are part of
the unproved conclusion, so totalized integrals do not replace them.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Complex

namespace LowDimensionalTopology.Unproved.Quasiconformal

/-- A genuine simple closed path with a specified finite C1 partition.
Simplicity is injectivity before the repeated endpoint. -/
structure PiecewiseC1JordanLoop where
  base : ℂ
  path : Path base base
  simple : Set.InjOn path (Ico (0 : unitInterval) 1)
  pieceCount : ℕ
  pieceCount_pos : 0 < pieceCount
  partition : Fin (pieceCount + 1) → ℝ
  partition_strictMono : StrictMono partition
  partition_start : partition 0 = 0
  partition_finish : partition (Fin.last pieceCount) = 1
  smooth_piece : ∀ i : Fin pieceCount,
    ContDiffOn ℝ 1 path.extend (Icc (partition i.castSucc) (partition i.succ))

/-- The actual parameter integrand for `f(z) dz` on one C1 piece. -/
def jordanLoopDzIntegrand (γ : PiecewiseC1JordanLoop)
    (f : ℂ → ℂ) (i : Fin γ.pieceCount) (t : ℝ) : ℂ :=
  f (γ.path.extend t) *
    derivWithin γ.path.extend (Icc (γ.partition i.castSucc) (γ.partition i.succ)) t

/-- The actual parameter integrand for `f(z) d(conj z)` on one C1 piece. -/
def jordanLoopDbarIntegrand (γ : PiecewiseC1JordanLoop)
    (f : ℂ → ℂ) (i : Fin γ.pieceCount) (t : ℝ) : ℂ :=
  f (γ.path.extend t) *
    starRingEnd ℂ
      (derivWithin γ.path.extend (Icc (γ.partition i.castSucc) (γ.partition i.succ)) t)

/-- The signed boundary integral of `f(z) dz`, summed over the finite pieces. -/
def jordanLoopIntegralDz (γ : PiecewiseC1JordanLoop) (f : ℂ → ℂ) : ℂ :=
  ∑ i : Fin γ.pieceCount,
    ∫ t in γ.partition i.castSucc..γ.partition i.succ, jordanLoopDzIntegrand γ f i t

/-- The signed boundary integral of `f(z) d(conj z)`. -/
def jordanLoopIntegralDbar (γ : PiecewiseC1JordanLoop) (f : ℂ → ℂ) : ℂ :=
  ∑ i : Fin γ.pieceCount,
    ∫ t in γ.partition i.castSucc..γ.partition i.succ, jordanLoopDbarIntegrand γ f i t

/-- The classical analytic winding index `(2πi)⁻¹ ∮ dz/(z-w)`.
For an index used in the boundary condition, `w` lies off the trace. -/
def jordanLoopWindingIndex (γ : PiecewiseC1JordanLoop) (w : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) * jordanLoopIntegralDz γ (fun z => 1 / (z - w))

/-- A finite family has exactly the given frontier and its total winding
is one on the domain and zero off its closure. This determines the positive
orientation, including negative orientation around holes. These conditions
involve only the fixed Cauchy kernel, never arbitrary-function Green data. -/
def IsPositiveFiniteJordanBoundary (D : Set ℂ) {m : ℕ}
    (γ : Fin m → PiecewiseC1JordanLoop) : Prop :=
  frontier D = (⋃ j : Fin m, Set.range (γ j).path) ∧
    (∀ w ∈ D, (∑ j : Fin m, jordanLoopWindingIndex (γ j) w) = 1) ∧
    (∀ w ∉ closure D, (∑ j : Fin m, jordanLoopWindingIndex (γ j) w) = 0)

/-- The bounded-domain Green formula. The function is
real C1 on an open neighborhood of the original closure. The conclusion
contains both full signed identities, with actual planar Lebesgue measure,
and genuine integrability of every integral used in those identities.
This is a concrete unproved proposition, not an axiom or a proof. -/
def FiniteBoundaryGreenFormula : Prop :=
  ∀ (D : Set ℂ), IsOpen D → Bornology.IsBounded D →
    ∀ (m : ℕ) (γ : Fin m → PiecewiseC1JordanLoop),
      IsPositiveFiniteJordanBoundary D γ →
      ∀ (U : Set ℂ), IsOpen U → closure D ⊆ U →
        ∀ (f : ℂ → ℂ), ContDiffOn ℝ 1 f U →
          (∀ (j : Fin m) (i : Fin (γ j).pieceCount),
            IntervalIntegrable (jordanLoopDzIntegrand (γ j) f i) volume
                ((γ j).partition i.castSucc) ((γ j).partition i.succ) ∧
              IntervalIntegrable (jordanLoopDbarIntegrand (γ j) f i) volume
                ((γ j).partition i.castSucc) ((γ j).partition i.succ)) ∧
          IntegrableOn (LiZhongQC.dzbar f) D (volume : Measure ℂ) ∧
          IntegrableOn (LiZhongQC.dz f) D (volume : Measure ℂ) ∧
          (2 * Complex.I) * (∫ z in D, LiZhongQC.dzbar f z) =
            (∑ j : Fin m, jordanLoopIntegralDz (γ j) f) ∧
          (-2 * Complex.I) * (∫ z in D, LiZhongQC.dz f z) =
            (∑ j : Fin m, jordanLoopIntegralDbar (γ j) f)

end LowDimensionalTopology.Unproved.Quasiconformal
