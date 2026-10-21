module
public import LowDimensionalTopology.Geometry.Mobius.CrossRatio.MobiusTriples
public import LowDimensionalTopology.Geometry.Mobius.CrossRatio.CrossRatio

/-!
# Matching complex cross-ratios

Equal complex cross-ratios of two ordered distinct quadruples are equivalent
to a unique matching element of the actual geometric Möbius group.
Normalization by the first, second and fourth points recovers the image of
the third point, including configurations involving infinity.
-/

@[expose] public section
noncomputable section
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Mobius

/-- Four pairwise distinct points, in the fixed ordering for the complex cross-ratio. -/
def QuadrupleDistinct (a b c d : ExtendedComplex) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- Every actual orientation-preserving geometric Möbius transformation preserves the complex ratio. -/
theorem extendedCrossRatio_mobius (f : complexMobiusGroup) (a b c d : ExtendedComplex) :
    extendedCrossRatio ((f : Equiv.Perm ExtendedComplex) a) ((f : Equiv.Perm ExtendedComplex) b)
      ((f : Equiv.Perm ExtendedComplex) c) ((f : Equiv.Perm ExtendedComplex) d) = extendedCrossRatio a b c d := by
  obtain ⟨g, rfl⟩ := mobiusMatrixProjection_surjective f
  simpa only [mobiusMatrixProjection_apply] using extendedCrossRatio_fractionalLinear g a b c d

/-- A third point away from infinity is recovered from its normalized complex ratio. -/
theorem extendedCrossRatio_zero_one_infty_coe (z : ExtendedComplex) (hz : z ≠ ∞) :
    (extendedCrossRatio (0 : ℂ) (1 : ℂ) z ∞ : ExtendedComplex) = z := by
  obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hz
  rw [extendedCrossRatio_zero_one_infty]

/-- Normalization by the first, second and fourth points evaluates the complex ratio as the third image. -/
theorem mobius_normalized_crossRatio (f : complexMobiusGroup) (a b c d : ExtendedComplex)
    (h0 : (f : Equiv.Perm ExtendedComplex) a = (0 : ℂ))
    (h1 : (f : Equiv.Perm ExtendedComplex) b = (1 : ℂ))
    (hi : (f : Equiv.Perm ExtendedComplex) d = ∞) (hcd : c ≠ d) :
    (extendedCrossRatio a b c d : ExtendedComplex) = (f : Equiv.Perm ExtendedComplex) c := by
  have hfin : (f : Equiv.Perm ExtendedComplex) c ≠ ∞ := by
    intro h
    exact hcd ((f : Equiv.Perm ExtendedComplex).injective (h.trans hi.symm))
  have h := extendedCrossRatio_mobius f a b c d
  rw [h0, h1, hi] at h
  rw [← h]
  exact extendedCrossRatio_zero_one_infty_coe _ hfin

/-- With three fixed distinct entries, the complex ratio distinguishes every remaining finite chart point. -/
theorem extendedCrossRatio_injective_third (a b d : ExtendedComplex) (hd : TripleDistinct a b d)
    {c c' : ExtendedComplex} (hcd : c ≠ d) (hc'd : c' ≠ d)
    (h : extendedCrossRatio a b c d = extendedCrossRatio a b c' d) : c = c' := by
  obtain ⟨f, h0, h1, hi⟩ := mobius_normalize_triple a b d hd
  apply (f : Equiv.Perm ExtendedComplex).injective
  rw [← mobius_normalized_crossRatio f a b c d h0 h1 hi hcd,
    ← mobius_normalized_crossRatio f a b c' d h0 h1 hi hc'd, h]

/-- Equal cross-ratios characterize Möbius matching of distinct ordered quadruples. -/
theorem extendedCrossRatio_eq_iff_exists_mobius (a b c d A B C D : ExtendedComplex)
    (hd : QuadrupleDistinct a b c d) (hD : QuadrupleDistinct A B C D) :
    extendedCrossRatio a b c d = extendedCrossRatio A B C D ↔
      ∃ f : complexMobiusGroup, (f : Equiv.Perm ExtendedComplex) a = A ∧
        (f : Equiv.Perm ExtendedComplex) b = B ∧ (f : Equiv.Perm ExtendedComplex) c = C ∧
        (f : Equiv.Perm ExtendedComplex) d = D := by
  constructor
  · intro h
    obtain ⟨f, hf, _⟩ := mobius_existsUnique_map_triple a b d A B D
      ⟨hd.1, hd.2.2.1, hd.2.2.2.2.1⟩ ⟨hD.1, hD.2.2.1, hD.2.2.2.2.1⟩
    refine ⟨f, hf.1, hf.2.1, ?_, hf.2.2⟩
    have hinv := extendedCrossRatio_mobius f a b c d
    rw [hf.1, hf.2.1, hf.2.2, h] at hinv
    exact extendedCrossRatio_injective_third A B D ⟨hD.1, hD.2.2.1, hD.2.2.2.2.1⟩
      (by intro he; exact hd.2.2.2.2.2 ((f : Equiv.Perm ExtendedComplex).injective (he.trans hf.2.2.symm)))
      hD.2.2.2.2.2 hinv
  · rintro ⟨f, ha, hb, hc, hd⟩
    have h := extendedCrossRatio_mobius f a b c d
    rw [ha, hb, hc, hd] at h
    exact h.symm

/-- The matching map for two equal-ratio distinct quadruples is unique. -/
theorem extendedCrossRatio_eq_iff_existsUnique_mobius (a b c d A B C D : ExtendedComplex)
    (hd : QuadrupleDistinct a b c d) (hD : QuadrupleDistinct A B C D) :
    extendedCrossRatio a b c d = extendedCrossRatio A B C D ↔
      ∃! f : complexMobiusGroup, (f : Equiv.Perm ExtendedComplex) a = A ∧
        (f : Equiv.Perm ExtendedComplex) b = B ∧ (f : Equiv.Perm ExtendedComplex) c = C ∧
        (f : Equiv.Perm ExtendedComplex) d = D := by
  rw [extendedCrossRatio_eq_iff_exists_mobius a b c d A B C D hd hD]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, hf, ?_⟩
    intro g hg
    apply mobius_eq_of_agree_triple g f a b d ⟨hd.1, hd.2.2.1, hd.2.2.2.2.1⟩
    · exact hg.1.trans hf.1.symm
    · exact hg.2.1.trans hf.2.1.symm
    · exact hg.2.2.2.trans hf.2.2.2.symm
  · rintro ⟨f, hf, _⟩
    exact ⟨f, hf⟩


/-- A distinct quadruple never has cross-ratio zero. -/
theorem extendedCrossRatio_ne_zero (a b c d : ExtendedComplex) (hd : QuadrupleDistinct a b c d) :
    extendedCrossRatio a b c d ≠ 0 := by
  obtain ⟨f, h0, h1, hi⟩ := mobius_normalize_triple a b d ⟨hd.1, hd.2.2.1, hd.2.2.2.2.1⟩
  have h := mobius_normalized_crossRatio f a b c d h0 h1 hi hd.2.2.2.2.2
  intro hz
  rw [hz] at h
  exact hd.2.1 ((f : Equiv.Perm ExtendedComplex).injective (h0.trans h))

/-- A distinct quadruple never has cross-ratio one. -/
theorem extendedCrossRatio_ne_one (a b c d : ExtendedComplex) (hd : QuadrupleDistinct a b c d) :
    extendedCrossRatio a b c d ≠ 1 := by
  obtain ⟨f, h0, h1, hi⟩ := mobius_normalize_triple a b d ⟨hd.1, hd.2.2.1, hd.2.2.2.2.1⟩
  have h := mobius_normalized_crossRatio f a b c d h0 h1 hi hd.2.2.2.2.2
  intro hz
  rw [hz] at h
  exact hd.2.2.2.1 ((f : Equiv.Perm ExtendedComplex).injective (h1.trans h))

end LowDimensionalTopology.Geometry.Mobius
