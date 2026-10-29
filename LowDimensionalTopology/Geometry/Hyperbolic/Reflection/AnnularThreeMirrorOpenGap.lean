module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularMirrorCapGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeLineReflections
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The three genuine annular mirrors have disjoint open ping-pong sides and
an explicit nonempty open gap, with every required single-reflection inclusion. -/
theorem annular_three_mirror_open_gap (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    let σ : Fin 3 → (ℍ ≃ᵢ ℍ) :=
      ![halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one),
        halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE)),
        halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)]
    let A : Fin 3 → Set ℍ :=
      ![{z : ℍ | ‖(z : ℂ)‖ < 1}, {z : ℍ | E < ‖(z : ℂ)‖},
        {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ < r}]
    let U := {z : ℍ | 1 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < E ∧
      r < ‖(z : ℂ) - (x : ℂ)‖}
    (Pairwise fun i j => Disjoint (A i) (A j)) ∧ IsOpen U ∧ U.Nonempty ∧
      (Pairwise fun i j => σ i '' A j ⊆ A i) ∧
      (∀ i, σ i '' U ⊆ A i) ∧ (∀ i, Disjoint (A i) U) := by
  have hE0 : 0 < E := zero_lt_one.trans hE
  have hx : 0 ≤ x := by linarith
  let σ : Fin 3 → (ℍ ≃ᵢ ℍ) :=
    ![halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one),
      halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 E hE0),
      halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)]
  let A : Fin 3 → Set ℍ :=
    ![{z : ℍ | ‖(z : ℂ)‖ < 1}, {z : ℍ | E < ‖(z : ℂ)‖},
      {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ < r}]
  let C : Fin 3 → Set ℍ :=
    ![{z : ℍ | ‖(z : ℂ)‖ ≤ 1}, {z : ℍ | E ≤ ‖(z : ℂ)‖},
      {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ ≤ r}]
  let U := {z : ℍ | 1 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < E ∧
    r < ‖(z : ℂ) - (x : ℂ)‖}
  change (Pairwise fun i j => Disjoint (A i) (A j)) ∧ IsOpen U ∧ U.Nonempty ∧
    (Pairwise fun i j => σ i '' A j ⊆ A i) ∧
    (∀ i, σ i '' U ⊆ A i) ∧ (∀ i, Disjoint (A i) U)
  have hsum (z : ℍ) : x ≤ ‖(z : ℂ) - (x : ℂ)‖ + ‖(z : ℂ)‖ := by
    have ht := norm_add_le ((x : ℂ) - (z : ℂ)) (z : ℂ)
    simpa only [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx, norm_sub_rev] using ht
  have h01 : Disjoint (C 0) (C 1) := by
    apply disjoint_left.mpr
    intro z hz0 hz1
    exact (not_le_of_gt hE) ((show E ≤ ‖(z : ℂ)‖ from hz1).trans hz0)
  have h02 : Disjoint (C 0) (C 2) := by
    apply disjoint_left.mpr
    intro z hz0 hz2
    have hn : ‖(z : ℂ)‖ ≤ 1 := hz0
    have hd : ‖(z : ℂ) - (x : ℂ)‖ ≤ r := hz2
    linarith [hsum z]
  have h12 : Disjoint (C 1) (C 2) :=
    annular_closed_outer_disjoint_small E r x hx houter
  have hC : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact (hij rfl).elim
      | exact h01
      | exact h01.symm
      | exact h02
      | exact h02.symm
      | exact h12
      | exact h12.symm
  have hAC (i : Fin 3) : A i ⊆ C i := by
    intro z hz
    fin_cases i
    · change ‖(z : ℂ)‖ < 1 at hz
      change ‖(z : ℂ)‖ ≤ 1
      exact hz.le
    · change E < ‖(z : ℂ)‖ at hz
      change E ≤ ‖(z : ℂ)‖
      exact hz.le
    · change ‖(z : ℂ) - (x : ℂ)‖ < r at hz
      change ‖(z : ℂ) - (x : ℂ)‖ ≤ r
      exact hz.le
  have hUC (i : Fin 3) : U ⊆ (C i)ᶜ := by
    fin_cases i
    · exact fun _ hz => not_le_of_gt hz.1
    · exact fun _ hz => not_le_of_gt hz.2.1
    · exact fun _ hz => not_le_of_gt hz.2.2
  have hflip (i : Fin 3) : σ i '' (C i)ᶜ ⊆ A i := by
    fin_cases i
    · rintro _ ⟨z, hz, rfl⟩
      change ¬ ‖(z : ℂ)‖ ≤ 1 at hz
      change ‖((HalfPlaneLine.circle 0 1 zero_lt_one).reflection z : ℂ)‖ < 1
      have hs := circle_reflection_radius_lt_iff 0 1 zero_lt_one z
      simp only [Complex.ofReal_zero, sub_zero] at hs
      exact hs.mpr (lt_of_not_ge hz)
    · rintro _ ⟨z, hz, rfl⟩
      change ¬ E ≤ ‖(z : ℂ)‖ at hz
      change E < ‖((HalfPlaneLine.circle 0 E hE0).reflection z : ℂ)‖
      have ht : ‖(z : ℂ)‖ < E ↔
          E < ‖((HalfPlaneLine.circle 0 E hE0).reflection z : ℂ)‖ := by
        have hi : (HalfPlaneLine.circle 0 E hE0).reflection
            ((HalfPlaneLine.circle 0 E hE0).reflection z) = z :=
          (HalfPlaneLine.circle 0 E hE0).reflection_involutive z
        simpa only [Complex.ofReal_zero, sub_zero, hi] using
          circle_reflection_radius_lt_iff 0 E hE0
            ((HalfPlaneLine.circle 0 E hE0).reflection z)
      exact ht.mp (lt_of_not_ge hz)
    · rintro _ ⟨z, hz, rfl⟩
      change ¬ ‖(z : ℂ) - (x : ℂ)‖ ≤ r at hz
      exact (circle_reflection_radius_lt_iff x r hr z).mpr (lt_of_not_ge hz)
  have hf : Continuous (fun z : ℍ => ‖(z : ℂ)‖) := UpperHalfPlane.continuous_coe.norm
  have hg : Continuous (fun z : ℍ => ‖(z : ℂ) - (x : ℂ)‖) :=
    (UpperHalfPlane.continuous_coe.sub continuous_const).norm
  have hUo : IsOpen U := (isOpen_lt continuous_const hf).inter
    ((isOpen_lt hf continuous_const).inter (isOpen_lt continuous_const hg))
  have hUn : U.Nonempty := by
    let t : ℝ := (1 + E) / 2
    have ht : 0 < t := by dsimp [t]; linarith
    let w : ℍ := ⟨(t : ℂ) * Complex.I, by simpa using ht⟩
    have hn : ‖(w : ℂ)‖ = t := by
      change ‖(t : ℂ) * Complex.I‖ = t
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
        Complex.norm_I, mul_one]
    have hd : x ≤ ‖(w : ℂ) - (x : ℂ)‖ := by
      simpa only [w, UpperHalfPlane.coe_mk, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
        mul_zero, zero_mul, sub_zero, zero_sub, abs_neg, abs_of_nonneg hx] using
        Complex.abs_re_le_norm ((w : ℂ) - (x : ℂ))
    refine ⟨w, ?_, ?_, ?_⟩
    · rw [hn]; dsimp [t]; linarith
    · rw [hn]; dsimp [t]; linarith
    · exact (show r < x by linarith).trans_le hd
  refine ⟨fun i j hij => (hC hij).mono (hAC i) (hAC j), hUo, hUn, ?_, ?_, ?_⟩
  · intro i j hij
    exact (image_mono ((hAC j).trans (hC hij).symm.subset_compl_right)).trans (hflip i)
  · exact fun i => (image_mono (hUC i)).trans (hflip i)
  · exact fun i => disjoint_left.mpr fun _ hz hu => (hUC i hu) (hAC i hz)

end LowDimensionalTopology.Geometry.Hyperbolic
