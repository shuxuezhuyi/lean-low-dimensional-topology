module
public import LowDimensionalTopology.Geometry.Mobius.Trace.MobiusInvariants

/-!
# Ordered triples

The actual orientation-preserving geometric Möbius group acts sharply
transitively on ordered triples of distinct points of the extended complex
plane. A normalization first sends the third point to infinity, then sends
the remaining two finite points to zero and one. The proved real geometric
group equivalence ensures that these matrix actions are actual Möbius maps.
-/

@[expose] public section
noncomputable section
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Mobius

/-- An ordered triple of pairwise distinct points on the actual extended complex plane. -/
def TripleDistinct (a b c : ExtendedComplex) : Prop := a ≠ b ∧ a ≠ c ∧ b ≠ c

/-- An actual orientation-preserving Möbius transformation can send any point to infinity. -/
theorem mobius_exists_send_to_infty (a : ExtendedComplex) :
    ∃ q : complexMobiusGroup, (q : Equiv.Perm ExtendedComplex) a = ∞ := by
  obtain ⟨q, hq⟩ := Mobius.Classification.exists_send_to_infty a
  refine ⟨complexMobiusEquivFractionalLinear.symm q, ?_⟩
  rwa [complexMobiusEquivFractionalLinear_symm_apply]

/-- Every ordered distinct triple can be carried to zero, one and infinity by an actual Möbius transformation. -/
theorem mobius_normalize_triple (a b c : ExtendedComplex) (hd : TripleDistinct a b c) :
    ∃ q : complexMobiusGroup, (q : Equiv.Perm ExtendedComplex) a = (0 : ℂ) ∧
      (q : Equiv.Perm ExtendedComplex) b = (1 : ℂ) ∧ (q : Equiv.Perm ExtendedComplex) c = ∞ := by
  obtain ⟨q, hq⟩ := mobius_exists_send_to_infty c
  have hqa : (q : Equiv.Perm ExtendedComplex) a ≠ ∞ := by
    intro h
    exact hd.2.1 ((q : Equiv.Perm ExtendedComplex).injective (h.trans hq.symm))
  have hqb : (q : Equiv.Perm ExtendedComplex) b ≠ ∞ := by
    intro h
    exact hd.2.2 ((q : Equiv.Perm ExtendedComplex).injective (h.trans hq.symm))
  obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.mp hqa
  obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.mp hqb
  have hvu : v - u ≠ 0 := by
    intro h
    have huv : u = v := (sub_eq_zero.mp h).symm
    have hab : (q : Equiv.Perm ExtendedComplex) a = (q : Equiv.Perm ExtendedComplex) b := by
      rw [← hu, ← hv, huv]
    exact hd.1 ((q : Equiv.Perm ExtendedComplex).injective hab)
  let k : ℂˣ := Units.mk0 ((v - u)⁻¹) (inv_ne_zero hvu)
  let p := mobiusMatrixProjection (Mobius.Classification.affineMatrix k (-u / (v - u)))
  have hp (z : ℂ) : (p : Equiv.Perm ExtendedComplex) z =
      (((v - u)⁻¹ * z + -u / (v - u) : ℂ) : ExtendedComplex) := by
    rw [mobiusMatrixProjection_apply, Mobius.Classification.affineMatrix_coe]
    rfl
  have hpinfty : (p : Equiv.Perm ExtendedComplex) ∞ = ∞ := by
    rw [mobiusMatrixProjection_apply, Mobius.Classification.affineMatrix_infty]
  refine ⟨p * q, ?_, ?_, ?_⟩
  · change (p : Equiv.Perm ExtendedComplex) ((q : Equiv.Perm ExtendedComplex) a) = _
    rw [← hu, hp]
    congr 1
    field_simp
    ring
  · change (p : Equiv.Perm ExtendedComplex) ((q : Equiv.Perm ExtendedComplex) b) = _
    rw [← hv, hp]
    congr 1
    field_simp
    ring
  · change (p : Equiv.Perm ExtendedComplex) ((q : Equiv.Perm ExtendedComplex) c) = _
    rw [hq, hpinfty]

/-- A fractional linear map fixing zero, one and infinity is the identity. -/
theorem fractionalLinear_eq_one_of_fixes_zero_one_infty (f : fractionalLinearGroup)
    (h0 : (f : Equiv.Perm ExtendedComplex) (0 : ℂ) = (0 : ℂ))
    (h1 : (f : Equiv.Perm ExtendedComplex) (1 : ℂ) = (1 : ℂ))
    (hi : (f : Equiv.Perm ExtendedComplex) ∞ = ∞) : f = 1 := by
  obtain ⟨a, b, hf⟩ := Mobius.Classification.affine_of_fixes_infty f hi
  have hb : b = 0 := by
    rw [hf, matrixProjection_apply, Mobius.Classification.affineMatrix_coe, OnePoint.coe_eq_coe] at h0
    simpa using h0
  have ha : (a : ℂ) = 1 := by
    rw [hf, matrixProjection_apply, Mobius.Classification.affineMatrix_coe, OnePoint.coe_eq_coe, hb] at h1
    simpa using h1
  apply Subtype.ext
  apply Equiv.ext
  intro z
  induction z using OnePoint.rec with
  | infty => exact hi
  | coe z =>
    rw [hf, matrixProjection_apply, Mobius.Classification.affineMatrix_coe, ha, hb]
    simp

/-- The actual geometric Möbius group acts freely on ordered distinct triples. -/
theorem mobius_eq_one_of_fixes_zero_one_infty (f : complexMobiusGroup)
    (h0 : (f : Equiv.Perm ExtendedComplex) (0 : ℂ) = (0 : ℂ))
    (h1 : (f : Equiv.Perm ExtendedComplex) (1 : ℂ) = (1 : ℂ))
    (hi : (f : Equiv.Perm ExtendedComplex) ∞ = ∞) : f = 1 := by
  apply complexMobiusEquivFractionalLinear.injective
  rw [map_one]
  apply fractionalLinear_eq_one_of_fixes_zero_one_infty
  · rwa [complexMobiusEquivFractionalLinear_apply]
  · rwa [complexMobiusEquivFractionalLinear_apply]
  · rwa [complexMobiusEquivFractionalLinear_apply]


/-- exactly one actual geometric Möbius transformation matches two ordered distinct triples. -/
theorem mobius_existsUnique_map_triple (a b c A B C : ExtendedComplex)
    (hd : TripleDistinct a b c) (hD : TripleDistinct A B C) :
    ∃! f : complexMobiusGroup, (f : Equiv.Perm ExtendedComplex) a = A ∧
      (f : Equiv.Perm ExtendedComplex) b = B ∧ (f : Equiv.Perm ExtendedComplex) c = C := by
  obtain ⟨p, hpa, hpb, hpc⟩ := mobius_normalize_triple a b c hd
  obtain ⟨q, hqA, hqB, hqC⟩ := mobius_normalize_triple A B C hD
  have hp_inv {z w : ExtendedComplex} (h : (p : Equiv.Perm ExtendedComplex) z = w) :
      (p⁻¹ : Equiv.Perm ExtendedComplex) w = z := by rw [← h]; simp
  refine ⟨q⁻¹ * p, ⟨?_, ?_, ?_⟩, ?_⟩
  · change (q⁻¹ : Equiv.Perm ExtendedComplex) ((p : Equiv.Perm ExtendedComplex) a) = A
    rw [hpa, ← hqA]
    simp
  · change (q⁻¹ : Equiv.Perm ExtendedComplex) ((p : Equiv.Perm ExtendedComplex) b) = B
    rw [hpb, ← hqB]
    simp
  · change (q⁻¹ : Equiv.Perm ExtendedComplex) ((p : Equiv.Perm ExtendedComplex) c) = C
    rw [hpc, ← hqC]
    simp
  · intro g hg
    have h0 : (q * g * p⁻¹ : Equiv.Perm ExtendedComplex) (0 : ℂ) = (0 : ℂ) := by
      change (q : Equiv.Perm ExtendedComplex) ((g : Equiv.Perm ExtendedComplex)
        ((p⁻¹ : Equiv.Perm ExtendedComplex) (0 : ℂ))) = _
      rw [hp_inv hpa, hg.1, hqA]
    have h1 : (q * g * p⁻¹ : Equiv.Perm ExtendedComplex) (1 : ℂ) = (1 : ℂ) := by
      change (q : Equiv.Perm ExtendedComplex) ((g : Equiv.Perm ExtendedComplex)
        ((p⁻¹ : Equiv.Perm ExtendedComplex) (1 : ℂ))) = _
      rw [hp_inv hpb, hg.2.1, hqB]
    have hi : (q * g * p⁻¹ : Equiv.Perm ExtendedComplex) ∞ = ∞ := by
      change (q : Equiv.Perm ExtendedComplex) ((g : Equiv.Perm ExtendedComplex)
        ((p⁻¹ : Equiv.Perm ExtendedComplex) ∞)) = _
      rw [hp_inv hpc, hg.2.2, hqC]
    have hr := mobius_eq_one_of_fixes_zero_one_infty (q * g * p⁻¹) h0 h1 hi
    calc
      g = q⁻¹ * (q * g * p⁻¹) * p := by group
      _ = q⁻¹ * p := by rw [hr, mul_one]

/-- Equality of actual Möbius transformations is determined by their values on any three distinct points. -/
theorem mobius_eq_of_agree_triple (f g : complexMobiusGroup) (a b c : ExtendedComplex)
    (hd : TripleDistinct a b c)
    (ha : (f : Equiv.Perm ExtendedComplex) a = (g : Equiv.Perm ExtendedComplex) a)
    (hb : (f : Equiv.Perm ExtendedComplex) b = (g : Equiv.Perm ExtendedComplex) b)
    (hc : (f : Equiv.Perm ExtendedComplex) c = (g : Equiv.Perm ExtendedComplex) c) : f = g := by
  have hD : TripleDistinct ((g : Equiv.Perm ExtendedComplex) a)
      ((g : Equiv.Perm ExtendedComplex) b) ((g : Equiv.Perm ExtendedComplex) c) :=
    ⟨(g : Equiv.Perm ExtendedComplex).injective.ne hd.1,
      (g : Equiv.Perm ExtendedComplex).injective.ne hd.2.1,
      (g : Equiv.Perm ExtendedComplex).injective.ne hd.2.2⟩
  exact (mobius_existsUnique_map_triple a b c _ _ _ hd hD).unique ⟨ha, hb, hc⟩ ⟨rfl, rfl, rfl⟩

/-- The unique Möbius map matching two ordered distinct triples. -/
theorem exists_unique_mobius_map_distinct_triples (a b c A B C : ExtendedComplex) (hd : TripleDistinct a b c) (hD
    : TripleDistinct A B C) :
    ∃! f : complexMobiusGroup, (f : Equiv.Perm ExtendedComplex) a = A ∧
      (f : Equiv.Perm ExtendedComplex) b = B ∧ (f : Equiv.Perm ExtendedComplex) c = C :=
  mobius_existsUnique_map_triple a b c A B C hd hD

end LowDimensionalTopology.Geometry.Mobius
