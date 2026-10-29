module

public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedTeichmuller
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HalfPlaneUniformization
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sequences

/-!
# Positive lower-left matrix coordinates for actual Fricke generators

The book matrix coordinates retain the actual determinant-one entries `(a,c,d)`
with `c > 0`; the omitted entry is reconstructed from the determinant. The
fixed-point/multiplier coordinates are compared for the same matrices. A
noncommuting deck element of an original compact hyperbolic surface has nonzero
lower-left entry relative to its normalized diagonal deck generator, so these
coordinates apply without assuming the missing coefficient condition.

The fixed-point and multiplier formulas and compact covering-group theorem are
reused from Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0).
The ordered marking and entire Fricke model are not defined by this local bridge.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- Real determinant-one matrices acting on the original upper half-plane. -/
abbrev RealSL := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The literal ordered matrix entries used for one Fricke generator. -/
def bookMatrixCoordinates (A : RealSL) : ℝ × ℝ × ℝ :=
  (A 0 0, A 1 0, A 1 1)

/-- The positive lower-left coefficient is part of the book normalization. -/
def positiveBookCoordinates : Set (ℝ × ℝ × ℝ) := {v | 0 < v.2.1}

/-- Reconstruct the original determinant-one matrix, including its omitted entry. -/
def matrixFromBookCoordinates (v : positiveBookCoordinates) : RealSL :=
  ⟨!![v.val.1, (v.val.1 * v.val.2.2 - 1) / v.val.2.1;
    v.val.2.1, v.val.2.2], by
      rw [Matrix.det_fin_two_of]
      have hc : v.val.2.1 ≠ 0 := v.property.ne'
      field_simp
      ring⟩

@[simp] theorem bookCoordinates_matrixFromBook (v : positiveBookCoordinates) :
    bookMatrixCoordinates (matrixFromBookCoordinates v) = v := rfl

/-- The determinant recovers the omitted entry on the genuine positive-c branch. -/
theorem matrixFromBook_bookCoordinates (A : RealSL) (hc : 0 < A 1 0) :
    matrixFromBookCoordinates ⟨bookMatrixCoordinates A, hc⟩ = A := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · change (A 0 0 * A 1 1 - 1) / A 1 0 = A 0 1
    apply (div_eq_iff hc.ne').mpr
    linear_combination LiZhongQC.hnf_sl2_det A
  · rfl
  · rfl

/-- Positive-c matrix coordinates determine the actual matrix, not just its action. -/
theorem bookMatrixCoordinates_injective_positive
    {A B : RealSL} (hA : 0 < A 1 0) (hB : 0 < B 1 0)
    (h : bookMatrixCoordinates A = bookMatrixCoordinates B) : A = B := by
  have hv : (⟨bookMatrixCoordinates A, hA⟩ : positiveBookCoordinates) =
      ⟨bookMatrixCoordinates B, hB⟩ := Subtype.ext h
  have hm := congrArg matrixFromBookCoordinates hv
  simpa only [matrixFromBook_bookCoordinates] using hm

theorem continuous_matrixFromBookCoordinates : Continuous matrixFromBookCoordinates := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · exact continuous_fst.comp continuous_subtype_val
  · change Continuous fun v : positiveBookCoordinates =>
      (v.val.1 * v.val.2.2 - 1) / v.val.2.1
    exact (((continuous_fst.comp continuous_subtype_val).mul
      (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))).sub
      continuous_const).div
        (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
        (fun v => v.property.ne')
  · exact continuous_fst.comp (continuous_snd.comp continuous_subtype_val)
  · exact continuous_snd.comp (continuous_snd.comp continuous_subtype_val)

/-- The actual determinant-one positive-c matrices and their book coordinates
are homeomorphic with their original subspace topologies. -/
def positiveMatrixCoordinatesHomeomorph :
    {A : RealSL // 0 < A 1 0} ≃ₜ positiveBookCoordinates where
  toFun A := ⟨bookMatrixCoordinates A.val, A.property⟩
  invFun v := ⟨matrixFromBookCoordinates v, v.property⟩
  left_inv A := Subtype.ext (matrixFromBook_bookCoordinates A.val A.property)
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous fun A : {A : RealSL // 0 < A 1 0} =>
      (A.val 0 0, A.val 1 0, A.val 1 1)
    fun_prop
  continuous_invFun := continuous_matrixFromBookCoordinates.subtype_mk _

/-- The open part corresponding to hyperbolic matrices in positive-c normalization. -/
def hyperbolicBookCoordinates : Set (ℝ × ℝ × ℝ) :=
  {v | 0 < v.2.1 ∧ 2 < |v.1 + v.2.2|}

theorem isOpen_hyperbolicBookCoordinates : IsOpen hyperbolicBookCoordinates := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
  · exact isOpen_lt continuous_const (continuous_fst.add
      (continuous_snd.comp continuous_snd)).abs

/-- Fixed-point/multiplier data of the actual reconstructed book matrix. -/
def fixedMultiplierCoordinates (v : hyperbolicBookCoordinates) : ℝ × ℝ × ℝ :=
  LiZhongQC.frickeTriple (matrixFromBookCoordinates ⟨v.val, v.property.1⟩)

private theorem frickeTriple_injective_positive
    {A B : RealSL} (hAc : 0 < A 1 0) (hBc : 0 < B 1 0)
    (hA : 2 < |A 0 0 + A 1 1|) (hB : 2 < |B 0 0 + B 1 1|)
    (h : LiZhongQC.frickeTriple A = LiZhongQC.frickeTriple B) : A = B := by
  obtain ⟨σA, hσA⟩ := LiZhongQC.hnf_attr_exists hAc.ne'
  obtain ⟨τA, hτA⟩ := LiZhongQC.hnf_rep_exists hAc.ne'
  obtain ⟨σB, hσB⟩ := LiZhongQC.hnf_attr_exists hBc.ne'
  obtain ⟨τB, hτB⟩ := LiZhongQC.hnf_rep_exists hBc.ne'
  have hσ : σA = σB := by
    have he := congrArg (fun v : ℝ × ℝ × ℝ => v.1) h
    change (LiZhongQC.extToC (LiZhongQC.attractingFixedPoint A)).re =
      (LiZhongQC.extToC (LiZhongQC.attractingFixedPoint B)).re at he
    rw [hσA, hσB] at he
    exact he
  have hτ : τA = τB := by
    have he := congrArg (fun v : ℝ × ℝ × ℝ => v.2.1) h
    change (LiZhongQC.extToC (LiZhongQC.repellingFixedPoint A)).re =
      (LiZhongQC.extToC (LiZhongQC.repellingFixedPoint B)).re at he
    rw [hτA, hτB] at he
    exact he
  have hm : LiZhongQC.multiplier A = LiZhongQC.multiplier B :=
    congrArg (fun v : ℝ × ℝ × ℝ => v.2.2) h
  have ha : LiZhongQC.attractingFixedPoint A = LiZhongQC.attractingFixedPoint B :=
    hσA.trans (by rw [hσ]; exact hσB.symm)
  have hr : LiZhongQC.repellingFixedPoint A = LiZhongQC.repellingFixedPoint B :=
    hτA.trans (by rw [hτ]; exact hτB.symm)
  rcases (LiZhongQC.hyperbolic_normal_form hB).2.2.2.2.2 A hA ha hr hm with h | h
  · exact h
  · have hc : A 1 0 = -B 1 0 := by
      simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] using
        congrArg (fun C : RealSL => C 1 0) h
    linarith

/-- No information about the actual normalized hyperbolic matrix is lost by
using the existing fixed-point/multiplier coordinates. -/
theorem fixedMultiplierCoordinates_injective : Function.Injective fixedMultiplierCoordinates := by
  intro v w h
  have hm := frickeTriple_injective_positive v.property.1 w.property.1
    v.property.2 w.property.2 h
  apply Subtype.ext
  simpa only [bookCoordinates_matrixFromBook] using congrArg bookMatrixCoordinates hm

theorem continuous_fixedMultiplierCoordinates : Continuous fixedMultiplierCoordinates := by
  apply continuous_iff_seqContinuous.mpr
  intro vn v hvn
  let lift : hyperbolicBookCoordinates → RealSL :=
    fun w => matrixFromBookCoordinates ⟨w.val, w.property.1⟩
  have hlift : Continuous lift := continuous_matrixFromBookCoordinates.comp
    (continuous_subtype_val.subtype_mk fun w => w.property.1)
  exact LiZhongQC.s27v_frickeTriple_tendsto (hlift.continuousAt.tendsto.comp hvn)
    v.property.2 (fun n => by
      constructor
      · intro hzero
        exact (vn n).property.1.ne' hzero |>.elim
      · intro hzero
        exact v.property.1.ne' hzero |>.elim)

/-- The finite fixed-point and multiplier formulas in literal book entries.
The formula is total; only its genuine hyperbolic positive-c branch is used. -/
def fixedMultiplierFormula (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ((v.1 - v.2.2 + Real.sign (v.1 + v.2.2) *
      Real.sqrt ((v.1 + v.2.2) ^ 2 - 4)) / (2 * v.2.1),
    (v.1 - v.2.2 - Real.sign (v.1 + v.2.2) *
      Real.sqrt ((v.1 + v.2.2) ^ 2 - 4)) / (2 * v.2.1),
    ((|v.1 + v.2.2| + Real.sqrt ((v.1 + v.2.2) ^ 2 - 4)) / 2) ^ 2)

theorem fixedMultiplierCoordinates_eq_formula (v : hyperbolicBookCoordinates) :
    fixedMultiplierCoordinates v = fixedMultiplierFormula v := by
  have hc : v.val.2.1 ≠ 0 := v.property.1.ne'
  simp [fixedMultiplierCoordinates, fixedMultiplierFormula, matrixFromBookCoordinates,
    LiZhongQC.frickeTriple, LiZhongQC.attractingFixedPoint,
    LiZhongQC.repellingFixedPoint, LiZhongQC.multiplier, LiZhongQC.extToC, hc,
    -Complex.ofReal_ofNat, -Complex.ofReal_mul, Complex.div_ofReal_re]

/-- The actual fixed-point/multiplier map is an open embedding of the original
positive-c hyperbolic book-coordinate region, with its Euclidean subspace topology. -/
theorem fixedMultiplierCoordinates_isOpenEmbedding :
    Topology.IsOpenEmbedding fixedMultiplierCoordinates := by
  have hcont : ContinuousOn fixedMultiplierFormula hyperbolicBookCoordinates := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun v : hyperbolicBookCoordinates => fixedMultiplierFormula v.val)
    have he : (fun v : hyperbolicBookCoordinates => fixedMultiplierFormula v.val) =
        fixedMultiplierCoordinates :=
      funext fun v => (fixedMultiplierCoordinates_eq_formula v).symm
    rw [he]
    exact continuous_fixedMultiplierCoordinates
  have hinj : InjOn fixedMultiplierFormula hyperbolicBookCoordinates := by
    intro v hv w hw he
    have hsub : (⟨v, hv⟩ : hyperbolicBookCoordinates) = ⟨w, hw⟩ :=
      fixedMultiplierCoordinates_injective (by
        rw [fixedMultiplierCoordinates_eq_formula, fixedMultiplierCoordinates_eq_formula]
        exact he)
    exact congrArg Subtype.val hsub
  have hopen : IsOpenMap fixedMultiplierCoordinates := by
    intro V hV
    have hW : IsOpen (Subtype.val '' V : Set (ℝ × ℝ × ℝ)) :=
      isOpen_hyperbolicBookCoordinates.isOpenMap_subtype_val V hV
    have hsub : Subtype.val '' V ⊆ hyperbolicBookCoordinates := by
      rintro x ⟨v, _hv, rfl⟩
      exact v.property
    have ho := LiZhongExternal.Topology.invariance_of_domain_finiteDimensional
      fixedMultiplierFormula (Subtype.val '' V) hW (hcont.mono hsub) (hinj.mono hsub)
    have himage : fixedMultiplierCoordinates '' V =
        fixedMultiplierFormula '' (Subtype.val '' V) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v.val, ⟨v, hv, rfl⟩, (fixedMultiplierCoordinates_eq_formula v).symm⟩
      · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, fixedMultiplierCoordinates_eq_formula v⟩
    exact himage.symm ▸ ho
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    continuous_fixedMultiplierCoordinates fixedMultiplierCoordinates_injective hopen

/-- The original book entries and the actual corresponding fixed-point/multiplier
data are homeomorphic. The target is the actual range, not a prescribed model. -/
def fixedMultiplierCoordinatesHomeomorph : hyperbolicBookCoordinates ≃ₜ
    Set.range fixedMultiplierCoordinates :=
  fixedMultiplierCoordinates_isOpenEmbedding.isEmbedding.toHomeomorph

private theorem triangular_commutator_diagonal
    (A D : RealSL) (hc : A 1 0 = 0)
    (hDb : D 0 1 = 0) (hDc : D 1 0 = 0) :
    LiZhongQC.commutatorSL A D 0 0 = 1 ∧
      LiZhongQC.commutatorSL A D 1 1 = 1 := by
  have hdetA : A 0 0 * A 1 1 = 1 := by
    simpa only [hc, mul_zero, sub_zero] using LiZhongQC.hnf_sl2_det A
  have hdetD : D 0 0 * D 1 1 = 1 := by
    simpa only [hDb, zero_mul, sub_zero] using LiZhongQC.hnf_sl2_det D
  have hAi := LiZhongQC.s27t_inv_apply A
  have hDi := LiZhongQC.s27t_inv_apply D
  constructor
  · simp only [LiZhongQC.commutatorSL, LiZhongQC.s27t_mul_apply,
      hAi.1, hAi.2.1, hAi.2.2.1, hAi.2.2.2,
      hDi.1, hDi.2.2.1,
      hc, hDb, hDc, neg_zero, mul_zero, add_zero, zero_add]
    calc
      _ = (A 0 0 * A 1 1) * (D 0 0 * D 1 1) := by ring
      _ = 1 := by rw [hdetA, hdetD]; norm_num
  · simp only [LiZhongQC.commutatorSL, LiZhongQC.s27t_mul_apply,
      hAi.1, hAi.2.1, hAi.2.2.1, hAi.2.2.2,
      hDi.2.1, hDi.2.2.2,
      hc, hDb, hDc, neg_zero, mul_zero, zero_mul, add_zero, zero_add]
    calc
      _ = (A 0 0 * A 1 1) * (D 0 0 * D 1 1) := by ring
      _ = 1 := by rw [hdetA, hdetD]; norm_num

/-- An actual noncommuting deck element has nonzero lower-left entry relative
to a diagonal deck generator of the same compact surface. The diagonal generator
itself is deliberately excluded by the noncommutation condition. -/
theorem lowerLeft_ne_zero_of_noncommuting_diagonal_deck
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X]
    {Γ : Subgroup RealSL} {p : UpperHalfPlane → X}
    (hp : LiZhongQC.IsUniformization Γ p)
    (A D : RealSL) (hA : A ∈ Γ) (hD : D ∈ Γ)
    (hDb : D 0 1 = 0) (hDc : D 1 0 = 0) (hAD : ¬Commute A D) :
    A 1 0 ≠ 0 := by
  intro hc
  let K := LiZhongQC.commutatorSL A D
  obtain ⟨hK00, hK11⟩ := triangular_commutator_diagonal A D hc hDb hDc
  have hK : K ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hA hD)
    (Γ.inv_mem hA)) (Γ.inv_mem hD)
  have hK1 : K ≠ 1 := by
    intro he
    apply hAD
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [commutatorElement_def, LiZhongQC.commutatorSL, K] using he
  have hKm1 : K ≠ -1 := by
    intro he
    have he00 := congrArg (fun B : RealSL => B 0 0) he
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at he00
    change LiZhongQC.commutatorSL A D 0 0 = -1 at he00
    linarith
  have hh := LiZhongQC.s27f_hyp hp hK hK1 hKm1
  change 2 < |LiZhongQC.commutatorSL A D 0 0 + LiZhongQC.commutatorSL A D 1 1| at hh
  rw [hK00, hK11] at hh
  norm_num at hh

end LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry.Teichmuller

/-- For a genuine element of the same original compact hyperbolic surface,
the normalized diagonal deck generator produces actual positive-c book
coordinates. Hyperbolicity, the missing nonzero coefficient, and preservation
of the original covering are all proved from the actual deck data. -/
theorem HyperbolicSurfaceModel.exists_positive_book_generator_coordinates
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel R)
    (A D : RealSL)
    (hAdeck : ∀ z : UpperHalfPlane, M.halfPlaneCover (A • z) = M.halfPlaneCover z)
    (hDdeck : ∀ z : UpperHalfPlane, M.halfPlaneCover (D • z) = M.halfPlaneCover z)
    (hD : D 0 1 = 0 ∧ D 1 0 = 0 ∧ 1 < D 0 0 ^ 2)
    (hAD : ¬Commute A D) :
    ∃ v : hyperbolicBookCoordinates,
      (matrixFromBookCoordinates ⟨v.val, v.property.1⟩ = A ∨
        matrixFromBookCoordinates ⟨v.val, v.property.1⟩ = -A) ∧
      (∀ z : UpperHalfPlane,
        M.halfPlaneCover (matrixFromBookCoordinates ⟨v.val, v.property.1⟩ • z) =
          M.halfPlaneCover z) ∧
      fixedMultiplierCoordinates v = LiZhongQC.frickeTriple A := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  have hAΓ := (hΓ A).mpr hAdeck
  have hDΓ := (hΓ D).mpr hDdeck
  have hc := lowerLeft_ne_zero_of_noncommuting_diagonal_deck hp A D hAΓ hDΓ
    hD.1 hD.2.1 hAD
  have hA1 : A ≠ 1 := by
    intro he
    apply hc
    simp [he]
  have hAm1 : A ≠ -1 := by
    intro he
    apply hc
    simp [he, Matrix.SpecialLinearGroup.coe_neg]
  have hh := LiZhongQC.s27f_hyp hp hAΓ hA1 hAm1
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hpc : 0 < (-A) 1 0 := by
      simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] using neg_pos.mpr hneg
    have hph : 2 < |(-A) 0 0 + (-A) 1 1| := by
      simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, ← neg_add, abs_neg] using hh
    let v : hyperbolicBookCoordinates := ⟨bookMatrixCoordinates (-A), hpc, hph⟩
    have hv : matrixFromBookCoordinates ⟨v.val, v.property.1⟩ = -A :=
      matrixFromBook_bookCoordinates (-A) hpc
    refine ⟨v, Or.inr hv, ?_, ?_⟩
    · intro z
      rw [hv, LiZhongQC.s27v_c_neg_smul]
      exact hAdeck z
    · change LiZhongQC.frickeTriple (matrixFromBookCoordinates ⟨v.val, v.property.1⟩) = _
      rw [hv, LiZhongQC.s27f_frickeTriple_neg]
  · let v : hyperbolicBookCoordinates := ⟨bookMatrixCoordinates A, hpos, hh⟩
    have hv : matrixFromBookCoordinates ⟨v.val, v.property.1⟩ = A :=
      matrixFromBook_bookCoordinates A hpos
    refine ⟨v, Or.inl hv, ?_, ?_⟩
    · intro z
      rw [hv]
      exact hAdeck z
    · change LiZhongQC.frickeTriple (matrixFromBookCoordinates ⟨v.val, v.property.1⟩) = _
      rw [hv]

end LowDimensionalTopology.Geometry.Surfaces
