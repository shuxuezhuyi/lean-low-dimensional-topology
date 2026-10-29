module

public import LowDimensionalTopology.Unproved.Teichmuller.CanonicalLastPairAxisAlternation
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalBookCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalProjectiveRelator
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Conditional recovery of all actual normalized canonical generators

The only unproved input is alternation of each supplied model's actual final
canonical pair. Diagonal expansion, the actual sole projective surface relation,
positive-c representatives and literal first-coordinate recovery are derived.
The last-pair matrix algebra is reused from Wu Xiaobin's credited
Li-Zhong-QC-formalization, commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation Hyperbolic Mobius

namespace NormalizedCanonicalFuchsianModel

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m n : MarkedRiemannSurface.{0, 0} R}

private theorem final_alpha_fixes_one (P : NormalizedCanonicalFuchsianModel hg e m) :
    P.matrices (finalHandle hg, 0) 0 0 + P.matrices (finalHandle hg, 0) 0 1 =
      P.matrices (finalHandle hg, 0) 1 0 + P.matrices (finalHandle hg, 0) 1 1 := by
  let A := P.matrices (finalHandle hg, 0)
  obtain ⟨_, hr⟩ := P.alpha_attracting
  have hpoly := (Mobius.Classification.fractionalLinear_fixed_coe_iff
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom A)) 1).mp
      (show Mobius.fractionalLinear _ ((1 : ℂ) : ExtendedComplex) = (1 : ℂ) by
        simpa only [realSLMobius, MonoidHom.comp_apply,
          Mobius.invariantDisc_specialLinear_action] using hr.2.1)
  change (A 1 0 : ℂ) * (1 * 1) + ((A 1 1 : ℂ) - A 0 0) * 1 +
    -(A 0 1 : ℂ) = 0 at hpoly
  norm_num only [one_mul, mul_one] at hpoly
  have hreal : A 1 0 + (A 1 1 - A 0 0) + -(A 0 1) = 0 := by exact_mod_cast hpoly
  change A 0 0 + A 0 1 = A 1 0 + A 1 1
  linarith

private def firstCommutatorProduct (P : NormalizedCanonicalFuchsianModel hg e m) : RealSL :=
  (List.ofFn fun i : Fin (g - 1) => LiZhongQC.commutatorSL
    (P.matrices (firstBookIndex i, 0)) (P.matrices (firstBookIndex i, 1))).prod

private theorem prefix_relation (P : NormalizedCanonicalFuchsianModel hg e m) :
    firstCommutatorProduct P * LiZhongQC.commutatorSL
        (P.matrices (finalHandle hg, 0)) (P.matrices (finalHandle hg, 1)) = 1 ∨
      firstCommutatorProduct P * LiZhongQC.commutatorSL
        (P.matrices (finalHandle hg, 0)) (P.matrices (finalHandle hg, 1)) = -1 := by
  have h := P.commutatorSL_prod_eq_one_or_neg_one
  have hsplit :
      (List.ofFn fun i : Fin g => LiZhongQC.commutatorSL
        (P.matrices (i, 0)) (P.matrices (i, 1))).prod =
      firstCommutatorProduct P * LiZhongQC.commutatorSL
        (P.matrices (finalHandle hg, 0)) (P.matrices (finalHandle hg, 1)) := by
    cases g with
    | zero => omega
    | succ k =>
      rw [List.ofFn_succ', List.prod_concat]
      rfl
  rw [hsplit] at h
  exact h

/-- The given final alpha fixes one in its original canonical normalization. -/
theorem finalAlpha_fixes_one (P : NormalizedCanonicalFuchsianModel hg e m) :
    P.matrices (finalHandle hg, 0) 0 0 + P.matrices (finalHandle hg, 0) 0 1 =
      P.matrices (finalHandle hg, 0) 1 0 + P.matrices (finalHandle hg, 0) 1 1 :=
  final_alpha_fixes_one P

/-- The actual ordered surface relation splits at its final handle. -/
theorem firstCommutatorProduct_mul_final_commutator
    (P : NormalizedCanonicalFuchsianModel hg e m) :
    (List.ofFn fun i : Fin (g - 1) => LiZhongQC.commutatorSL
        (P.matrices (firstBookIndex i, 0)) (P.matrices (firstBookIndex i, 1))).prod *
        LiZhongQC.commutatorSL
          (P.matrices (finalHandle hg, 0)) (P.matrices (finalHandle hg, 1)) = 1 ∨
      (List.ofFn fun i : Fin (g - 1) => LiZhongQC.commutatorSL
        (P.matrices (firstBookIndex i, 0)) (P.matrices (firstBookIndex i, 1))).prod *
        LiZhongQC.commutatorSL
          (P.matrices (finalHandle hg, 0)) (P.matrices (finalHandle hg, 1)) = -1 :=
  prefix_relation P

/-- For two actual given normalized models, literal equal first book coordinates
recover every ordered projective generator, conditional only on the concrete
canonical last-pair alternation facts. No model availability or marked-class
converse is asserted. -/
theorem generators_eq_of_firstBookCoordinates
    (P : NormalizedCanonicalFuchsianModel hg e m)
    (Q : NormalizedCanonicalFuchsianModel hg e n)
    (hP : Unproved.Teichmuller.CanonicalLastPairAxisAlternation P)
    (hQ : Unproved.Teichmuller.CanonicalLastPairAxisAlternation Q)
    (hcoords : P.firstBookCoordinates = Q.firstBookCoordinates) :
    ∀ d : Edge g, realSLMobius (P.matrices d) = realSLMobius (Q.matrices d) := by
  have hpm (i : Fin (g - 1)) (b : Fin 2) :
      P.matrices (firstBookIndex i, b) = Q.matrices (firstBookIndex i, b) ∨
        P.matrices (firstBookIndex i, b) = -Q.matrices (firstBookIndex i, b) :=
    (realSLMobius_eq_iff_sign (Q.matrices (firstBookIndex i, b))
      (P.matrices (firstBookIndex i, b))).mp
        (P.first_generators_eq_of_firstBookCoordinates Q hcoords i b).symm
  have hη : firstCommutatorProduct P = firstCommutatorProduct Q := by
    unfold firstCommutatorProduct
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    exact LiZhongQC.s27f_comm_pm (hpm i 0) (hpm i 1)
  have hrelQ : firstCommutatorProduct P * LiZhongQC.commutatorSL
        (Q.matrices (finalHandle hg, 0)) (Q.matrices (finalHandle hg, 1)) = 1 ∨
      firstCommutatorProduct P * LiZhongQC.commutatorSL
        (Q.matrices (finalHandle hg, 0)) (Q.matrices (finalHandle hg, 1)) = -1 := by
    rw [hη]
    exact prefix_relation Q
  obtain ⟨hβ, hα⟩ := LiZhongQC.s27t_last_pair_core
    P.final_beta_diagonal_expanding Q.final_beta_diagonal_expanding
    (prefix_relation P) hrelQ (final_alpha_fixes_one P) (final_alpha_fixes_one Q) hP hQ
  rintro ⟨i, b⟩
  by_cases hi : i = finalHandle hg
  · subst i
    fin_cases b
    · rcases hα with h | h
      · exact congrArg realSLMobius h
      · exact (congrArg realSLMobius h).trans (realSLMobius_neg _)
    · rcases hβ with h | h
      · exact congrArg realSLMobius h
      · exact (congrArg realSLMobius h).trans (realSLMobius_neg _)
  · have hip : i.val < g - 1 := by
      have hv : i.val ≠ g - 1 := by
        intro he
        exact hi (Fin.ext he)
      have hit := i.isLt
      omega
    let j : Fin (g - 1) := ⟨i.val, hip⟩
    have hj : firstBookIndex j = i := by apply Fin.ext; rfl
    simpa only [hj] using P.first_generators_eq_of_firstBookCoordinates Q hcoords j b

end NormalizedCanonicalFuchsianModel
end LowDimensionalTopology.Geometry.Teichmuller
