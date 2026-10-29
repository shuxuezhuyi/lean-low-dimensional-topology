module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalBetaExpansion
public import LowDimensionalTopology.Geometry.Teichmuller.PositiveFrickeCoordinates

/-!
# Literal first book coordinates of a given normalized canonical model

Only the individual SL signs are changed to make the first generators' lower
left entries positive. The actual projective generators are retained. The
coefficient nonvanishing and every coordinate recovery hypothesis are derived.
The public matrix reconstruction API reuses Wu Xiaobin's credited
Li-Zhong-QC-formalization, commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation Hyperbolic

namespace NormalizedCanonicalFuchsianModel

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m n : MarkedRiemannSurface.{0, 0} R}

/-- The source's first g-1 handle indices, in their unchanged ascending order. -/
def firstBookIndex (i : Fin (g - 1)) : Fin g := i.castLE (Nat.sub_le g 1)

private theorem firstBookIndex_ne_final (i : Fin (g - 1)) :
    firstBookIndex i ≠ finalHandle hg := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = g - 1 at hv
  exact (ne_of_lt i.isLt) hv

/-- Select the genuine positive-c lift of a first canonical generator. -/
def firstBookMatrix (P : NormalizedCanonicalFuchsianModel hg e m)
    (i : Fin (g - 1)) (b : Fin 2) : RealSL :=
  let A := P.matrices (firstBookIndex i, b)
  if 0 < A 1 0 then A else -A

/-- Only an allowed simultaneous determinant-one sign is changed. -/
theorem firstBookMatrix_eq_or_neg (P : NormalizedCanonicalFuchsianModel hg e m)
    (i : Fin (g - 1)) (b : Fin 2) :
    P.firstBookMatrix i b = P.matrices (firstBookIndex i, b) ∨
      P.firstBookMatrix i b = -P.matrices (firstBookIndex i, b) := by
  dsimp only [firstBookMatrix]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The positive coefficient follows from the actual original compact cover
and canonical marking, not from a supplied nonzero or positivity hypothesis. -/
theorem firstBookMatrix_lowerLeft_pos (P : NormalizedCanonicalFuchsianModel hg e m)
    (i : Fin (g - 1)) (b : Fin 2) : 0 < P.firstBookMatrix i b 1 0 := by
  have hD := P.final_beta_diagonal_expanding
  have hbc := m.surface.markedPolygon_matrices_bc_ne_zero hg P.model
    (m.marking.toHomeomorph.symm.trans e) P.liftBase P.liftBase_proj
    P.matrices P.represents hD.1 hD.2.1 (firstBookIndex i, b) (by
      fin_cases b
      · simp
      · change edgeLabelEquiv g (firstBookIndex i, 1) ≠ Sum.inr (finalHandle hg)
        rw [edgeLabelEquiv_b]
        exact fun h => firstBookIndex_ne_final (hg := hg) i (Sum.inr.inj h))
  have hc := (mul_ne_zero_iff.mp hbc).2
  rcases lt_or_gt_of_ne hc with hn | hp
  · simp only [firstBookMatrix, ite_eq_right (not_lt_of_gt hn),
      Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
    exact neg_pos.mpr hn
  · simpa only [firstBookMatrix, ite_eq_left hp] using hp

/-- Sign normalization retains exactly the same actual projective generator. -/
theorem firstBookMatrix_mobius (P : NormalizedCanonicalFuchsianModel hg e m)
    (i : Fin (g - 1)) (b : Fin 2) :
    realSLMobius (P.firstBookMatrix i b) = realSLMobius (P.matrices (firstBookIndex i, b)) := by
  rcases P.firstBookMatrix_eq_or_neg i b with h | h
  · exact congrArg realSLMobius h
  · rw [h, realSLMobius_neg]

/-- The literal (a,c,d,a',c',d') data, ordered by the first g-1 handles. -/
def firstBookCoordinates (P : NormalizedCanonicalFuchsianModel hg e m) :
    Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) :=
  fun i => (bookMatrixCoordinates (P.firstBookMatrix i 0),
    bookMatrixCoordinates (P.firstBookMatrix i 1))

/-- Equal literal book data recover every first actual projective generator. -/
theorem first_generators_eq_of_firstBookCoordinates
    (P : NormalizedCanonicalFuchsianModel hg e m)
    (Q : NormalizedCanonicalFuchsianModel hg e n)
    (hcoords : P.firstBookCoordinates = Q.firstBookCoordinates)
    (i : Fin (g - 1)) (b : Fin 2) :
    realSLMobius (P.matrices (firstBookIndex i, b)) =
      realSLMobius (Q.matrices (firstBookIndex i, b)) := by
  have hi := congrFun hcoords i
  have hc : bookMatrixCoordinates (P.firstBookMatrix i b) =
      bookMatrixCoordinates (Q.firstBookMatrix i b) := by
    fin_cases b
    · exact congrArg Prod.fst hi
    · exact congrArg Prod.snd hi
  have hmat := bookMatrixCoordinates_injective_positive
    (P.firstBookMatrix_lowerLeft_pos i b) (Q.firstBookMatrix_lowerLeft_pos i b) hc
  calc
    realSLMobius (P.matrices (firstBookIndex i, b)) =
        realSLMobius (P.firstBookMatrix i b) := (P.firstBookMatrix_mobius i b).symm
    _ = realSLMobius (Q.firstBookMatrix i b) := congrArg realSLMobius hmat
    _ = realSLMobius (Q.matrices (firstBookIndex i, b)) := Q.firstBookMatrix_mobius i b

end NormalizedCanonicalFuchsianModel
end LowDimensionalTopology.Geometry.Teichmuller
