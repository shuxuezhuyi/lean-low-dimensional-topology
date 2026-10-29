module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.AxisPowerC1Piece
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.C1SourceLength
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-!
# Covered loops realizing the full translation length

The covering matrix is retained throughout the construction. A proper power
therefore gives its own traversed loop, rather than the primitive axis quotient.
The length is attained by an actual Lipschitz lift and agrees with its literal
weighted derivative integral and with the free-homotopy minimum. Its actual C1
lift stays on the genuine native axis throughout the parameter interval.
-/

public section
noncomputable section

open Set MeasureTheory LiZhongQC
open scoped ENNReal NNReal UpperHalfPlane unitInterval MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The explicit source translation length is the native infimum of actual
hyperbolic displacements, for the same original matrix. -/
theorem liZhong_translationLength_eq_native
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hh : LiZhongQC.IsHyperbolic A) :
    LiZhongQC.translationLength A = hTranslationLength (hSLIsometry A) := by
  change LiZhongQC.translationLength A = ⨅ τ : ℍ, dist τ (A • τ)
  exact (LiZhongQC.translationLength_eq_inf_dist hh).1

/-- An actual hyperbolic covering element admits a projected closed loop attaining
its free-class minimum. Its literal Lipschitz lift length, loop length and
free-class length all retain the full covering matrix, including proper powers. -/
theorem exists_covered_loop_realizing_translation_length
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : LiZhongQC.IsUniformization Γ p)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hΓ : A ∈ Γ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2) :
    ∃ α : LiZhongQC.Loop S, LiZhongQC.Covers p A α ∧
      LiZhongQC.poincareLengthLoop p α = ENNReal.ofReal (hTranslationLength (hSLIsometry A)) ∧
      LiZhongQC.freeHomotopyLength p α = ENNReal.ofReal (hTranslationLength (hSLIsometry A)) ∧
      Real.cosh ((LiZhongQC.poincareLengthLoop p α).toReal / 2) ^ 2 =
        (Matrix.trace A.val) ^ 2 / 4 ∧
      ∃ (c : ℝ → ℂ) (_hK : ∃ K : ℝ≥0, LipschitzOnWith K c (Icc 0 1))
        (him : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c t).im),
        (∀ (t : ℝ) (htI : t ∈ Icc (0 : ℝ) 1), p ⟨c t, him t htI⟩ = α.2.extend t) ∧
        LiZhongQC.hypLength c = LiZhongQC.poincareLengthLoop p α ∧
        ∃ τ : ℍ, τ ∈ (hHyperbolicAxis A hA ht).carrier ∧
          c 0 = (τ : ℂ) ∧ c 1 = ((A • τ : ℍ) : ℂ) ∧
          ∃ d : C1CurvePiece, d.a = 0 ∧ d.b = 1 ∧
            (∀ t : ℝ, c t = (d.curve t : ℂ)) ∧
            (∀ t : ℝ, d.curve t ∈ (hHyperbolicAxis A hA ht).carrier) ∧
            d.length = hTranslationLength (hSLIsometry A) := by
  have hh : LiZhongQC.IsHyperbolic A := by
    unfold LiZhongQC.IsHyperbolic LiZhongQC.slTrace
    change 2 < |A.val 0 0 + A.val 1 1|
    rw [← Matrix.trace_fin_two]
    nlinarith [sq_abs (Matrix.trace A.val), abs_nonneg (Matrix.trace A.val)]
  have hT := liZhong_translationLength_eq_native A hh
  obtain ⟨d, ha, hb, haxis, hperiod, hdlen⟩ := exists_axis_power_c1_piece A hA ht 1
  have hdlength : d.length = hTranslationLength (hSLIsometry A) := by
    simpa only [Nat.cast_one, one_mul] using hdlen
  have hdperiod : d.curve 1 = A • d.curve 0 := by
    simpa only [pow_one] using hperiod
  let τ := d.curve 0
  let c : ℝ → ℂ := fun t => (d.curve t : ℂ)
  have hτ : τ ∈ (hHyperbolicAxis A hA ht).carrier := haxis 0
  have hK := d.exists_unit_lipschitz ha hb
  have him (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) : 0 < (c t).im := (d.curve t).im_pos
  have hc0 : c 0 = (τ : ℂ) := rfl
  have hc1 : c 1 = ((A • τ : ℍ) : ℂ) :=
    congrArg (fun z : ℍ => (z : ℂ)) hdperiod
  let e := LiZhongQC.s30a_pathOf c hK him
  have he0 : e 0 = τ := UpperHalfPlane.ext hc0
  have he1 : e 1 = A • τ := UpperHalfPlane.ext hc1
  have he : e 1 = A • e 0 := by rw [he0, he1]
  have hpe : p (e 1) = p (e 0) := by rw [he, LiZhongQC.s30a_p_smul hp hΓ]
  let α := LiZhongQC.s30a_projLoop p hp.1.continuous e hpe
  let E : Path (e 0) (e 1) := ⟨e, rfl, rfl⟩
  have hcov : LiZhongQC.Covers p A α := by
    refine ⟨E.extend, E.continuous_extend.continuousOn, ?_, ?_⟩
    · intro t htI
      calc
        p (E.extend t) = p (E ⟨t, htI⟩) := congrArg p (Path.extend_apply E htI)
        _ = α.2 ⟨t, htI⟩ := rfl
        _ = α.2.extend t := (Path.extend_apply α.2 htI).symm
    · rw [Path.extend_one, Path.extend_zero]
      exact he
  have hproj (t : ℝ) (htI : t ∈ Icc (0 : ℝ) 1) :
      p ⟨c t, him t htI⟩ = α.2.extend t := by
    calc
      p ⟨c t, him t htI⟩ = α.2 ⟨t, htI⟩ := rfl
      _ = α.2.extend t := (Path.extend_apply α.2 htI).symm
  have hfree : LiZhongQC.freeHomotopyLength p α =
      ENNReal.ofReal (hTranslationLength (hSLIsometry A)) := by
    rw [LiZhongQC.s30a_len_hyp hp hΓ hh hcov, hT]
  have hfreelower : LiZhongQC.freeHomotopyLength p α ≤ LiZhongQC.poincareLengthLoop p α :=
    iInf₂_le α (LiZhongQC.s30b_fh_of_eq (fun _ => rfl))
  have hloopupper : LiZhongQC.poincareLengthLoop p α ≤ LiZhongQC.hypLength c := by
    refine iInf₂_le c ⟨hK, him, ?_⟩
    intro t htI hpos
    exact hproj t htI
  have hlenT : LiZhongQC.hypLength c =
      ENNReal.ofReal (hTranslationLength (hSLIsometry A)) := by
    rw [d.hypLength_eq_length ha hb, hdlength]
  have hloop : LiZhongQC.poincareLengthLoop p α =
      ENNReal.ofReal (hTranslationLength (hSLIsometry A)) := by
    exact le_antisymm (hloopupper.trans_eq hlenT) (hfree ▸ hfreelower)
  refine ⟨α, hcov, hloop, hfree, ?_, c, hK, him, hproj, hlenT.trans hloop.symm,
    τ, hτ, hc0, hc1, d, ha, hb, fun _ => rfl, haxis, hdlength⟩
  rw [hloop, ENNReal.toReal_ofReal (hHyperbolic_translationLength_pos A hA ht).le]
  exact hHyperbolic_translation_trace A hA ht

end LowDimensionalTopology.Geometry.Hyperbolic
