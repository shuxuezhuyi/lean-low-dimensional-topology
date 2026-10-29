module

public import LowDimensionalTopology.Geometry.Mobius.Classification.MobiusTypes
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Mobius

/-- The four squared-trace tests, with loxodromic including hyperbolic.
The last test is the complement of the closed real interval [0,4]. -/
theorem mobius_four_types_squaredTrace (f : complexMobiusGroup) (hf : f ≠ 1) :
    (MobiusParabolic f ↔ mobiusSquaredTrace f = 4) ∧
    (MobiusElliptic f ↔ ∃ r : ℝ, 0 ≤ r ∧ r < 4 ∧
      mobiusSquaredTrace f = (r : ℂ)) ∧
    (MobiusHyperbolic f ↔ ∃ r : ℝ, 4 < r ∧
      mobiusSquaredTrace f = (r : ℂ)) ∧
    (MobiusLoxodromic f ↔ ¬∃ r : ℝ, 0 ≤ r ∧ r ≤ 4 ∧
      mobiusSquaredTrace f = (r : ℂ)) := by
  refine ⟨mobius_parabolic_iff_squaredTrace_eq_four f hf,
    mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f hf,
    mobius_hyperbolic_iff_squaredTrace_real_gt_four f hf, ?_⟩
  constructor
  · rintro hl ⟨r, hr0, hr4, ht⟩
    rcases lt_or_eq_of_le hr4 with hlt | heq
    · exact hl.not_elliptic
        ((mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f hf).mpr
          ⟨r, hr0, hlt, ht⟩)
    · apply hl.not_parabolic
      apply (mobius_parabolic_iff_squaredTrace_eq_four f hf).mpr
      rw [ht, heq]
      norm_num
  · intro hn
    rcases mobius_nonidentity_type_trichotomy f hf with hp | hl | he
    · apply False.elim
      apply hn
      exact ⟨4, by norm_num, le_rfl,
        by simpa using (mobius_parabolic_iff_squaredTrace_eq_four f hf).mp hp⟩
    · exact hl
    · obtain ⟨r, hr0, hr4, ht⟩ :=
        (mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f hf).mp he
      exact (hn ⟨r, hr0, hr4.le, ht⟩).elim

end LowDimensionalTopology.Geometry.Mobius
