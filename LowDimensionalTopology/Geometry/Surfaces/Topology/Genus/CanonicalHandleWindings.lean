module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.HandleModels
public import LowDimensionalTopology.Geometry.Surfaces.Topology.RankObstructions
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Set Topology
namespace LowDimensionalTopology.Geometry.Surfaces

/-- A bounded continuous ramp used to specify the literal polygon boundary coordinates. -/
def handleRamp (r : ℝ) : ℝ := max 0 (min 1 r)

theorem handleRamp_continuous : Continuous handleRamp :=
  continuous_const.max (continuous_const.min continuous_id)

theorem handleRamp_of_nonpos {r : ℝ} (hr : r ≤ 0) : handleRamp r = 0 := by
  dsimp [handleRamp]
  rw [min_eq_right (by linarith), max_eq_left hr]

theorem handleRamp_of_mem_unit {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : handleRamp r = r := by
  simp only [handleRamp, min_eq_right hr.2, max_eq_right hr.1]

theorem handleRamp_of_one_le {r : ℝ} (hr : 1 ≤ r) : handleRamp r = 1 := by
  simp only [handleRamp, min_eq_left hr, max_eq_right zero_le_one]

/-- The two real boundary lifts of a handle's a- and b-edges. -/
def handleAPeriodLift (k : ℕ) (r : ℝ) : ℝ :=
  handleRamp (r - 4 * k) - handleRamp (r - 4 * k - 2)

def handleBPeriodLift (k : ℕ) (r : ℝ) : ℝ :=
  handleRamp (r - 4 * k - 1) - handleRamp (r - 4 * k - 3)

theorem handleAPeriodLift_continuous (k : ℕ) : Continuous (handleAPeriodLift k) := by
  exact (handleRamp_continuous.comp (continuous_id.sub continuous_const)).sub
    (handleRamp_continuous.comp ((continuous_id.sub continuous_const).sub continuous_const))

theorem handleBPeriodLift_continuous (k : ℕ) : Continuous (handleBPeriodLift k) := by
  exact (handleRamp_continuous.comp ((continuous_id.sub continuous_const).sub continuous_const)).sub
    (handleRamp_continuous.comp ((continuous_id.sub continuous_const).sub continuous_const))

/-- The closed-interval formula for a real boundary lift is respected at both identified endpoints. -/
theorem unitBoundaryLift_apply {n : ℕ} (f : ℝ → Fin n → ℝ) (hf : f 0 = f 1)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : AddCircle.liftIco (1 : ℝ) 0 f (r : AddCircle (1 : ℝ)) = f r := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  by_cases he : r = 1
  · subst r
    rw [AddCircle.coe_period]
    change AddCircle.liftIco (1 : ℝ) 0 f (0 : AddCircle (1 : ℝ)) = f 1
    rw [show (0 : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) by rfl,
      AddCircle.liftIco_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 (0 + 1))]
    exact hf
  · exact AddCircle.liftIco_coe_apply ⟨hr.1, by simpa only [zero_add] using hr.2.lt_of_ne he⟩

/-- Every actual periodic real polygon-boundary lift extends continuously across the disc.
This uses Tietze on the real coordinates; it assumes no topological property of the quotient. -/
theorem exists_handleBoundaryExtension {n : ℕ} (f : ℝ → Fin n → ℝ)
    (hf : Continuous f) (hend : f 0 = f 1) :
    ∃ F : C(ℂ, Fin n → ℝ), ∀ r ∈ Icc (0 : ℝ) 1, F (handleBoundaryPoint r).val = f r := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  let φ : C(Circle, Fin n → ℝ) :=
    ⟨AddCircle.liftIco (1 : ℝ) 0 f ∘ e.symm,
      (AddCircle.liftIco_zero_continuous hend hf.continuousOn).comp e.symm.continuous⟩
  have hi : IsClosedEmbedding (fun z : Circle => z.val) :=
    Metric.isClosed_sphere.isClosedEmbedding_subtypeVal
  obtain ⟨F, hF⟩ := φ.exists_extension' hi
  refine ⟨F, ?_⟩
  intro r hr
  have he : e (r : AddCircle (1 : ℝ)) = Circle.exp (2 * Real.pi * r) := by
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, div_one]
  have hh := congrFun hF (Circle.exp (2 * Real.pi * r))
  change F (handleBoundaryPoint r).val =
    AddCircle.liftIco (1 : ℝ) 0 f (e.symm (Circle.exp (2 * Real.pi * r))) at hh
  rw [← he, e.symm_apply_apply, unitBoundaryLift_apply f hend hr] at hh
  exact hh

theorem handleAPeriodLift_shift (k : ℕ) (r : ℝ) :
    handleAPeriodLift k (4 * k + r) = handleAPeriodLift 0 r := by
  unfold handleAPeriodLift
  rw [show 4 * (k : ℝ) + r - 4 * k = r by ring]
  simp only [Nat.cast_zero, mul_zero, sub_zero]

theorem handleBPeriodLift_shift (k : ℕ) (r : ℝ) :
    handleBPeriodLift k (4 * k + r) = handleBPeriodLift 0 r := by
  unfold handleBPeriodLift
  rw [show 4 * (k : ℝ) + r - 4 * k - 1 = r - 1 by ring,
    show 4 * (k : ℝ) + r - 4 * k - 3 = r - 3 by ring]
  simp only [Nat.cast_zero, mul_zero, sub_zero]

/-- Exact real boundary lifts along the positively oriented a-edge. -/
theorem handlePeriodLifts_a (k : ℕ) (t : unitInterval) :
    (handleAPeriodLift k (4 * k + t.val), handleBPeriodLift k (4 * k + t.val)) = (t.val, 0) := by
  rw [handleAPeriodLift_shift, handleBPeriodLift_shift]
  simp only [handleAPeriodLift, handleBPeriodLift, Nat.cast_zero, mul_zero, sub_zero]
  rw [handleRamp_of_mem_unit t.property,
    handleRamp_of_nonpos (by linarith [t.property.2] : t.val - 2 ≤ 0),
    handleRamp_of_nonpos (by linarith [t.property.2] : t.val - 1 ≤ 0),
    handleRamp_of_nonpos (by linarith [t.property.2] : t.val - 3 ≤ 0)]
  simp

/-- The paired reverse a-edge differs from its partner only by an integral b-coordinate. -/
theorem handlePeriodLifts_a_pair (k : ℕ) (t : unitInterval) :
    (handleAPeriodLift k (4 * k + (3 - t.val)),
      handleBPeriodLift k (4 * k + (3 - t.val))) = (t.val, 1) := by
  rw [handleAPeriodLift_shift, handleBPeriodLift_shift]
  simp only [handleAPeriodLift, handleBPeriodLift, Nat.cast_zero, mul_zero, sub_zero]
  have h0 : handleRamp (3 - t.val) = 1 := handleRamp_of_one_le (by linarith [t.property.2])
  have h1 : handleRamp (3 - t.val - 2) = 1 - t.val := by
    rw [show 3 - t.val - 2 = 1 - t.val by ring]
    exact handleRamp_of_mem_unit ⟨by linarith [t.property.2], by linarith [t.property.1]⟩
  have h2 : handleRamp (3 - t.val - 1) = 1 := handleRamp_of_one_le (by linarith [t.property.2])
  have h3 : handleRamp (3 - t.val - 3) = 0 := handleRamp_of_nonpos (by linarith [t.property.1])
  rw [h0,h1,h2,h3]
  ext <;> ring

/-- Exact real boundary lifts along the positively oriented b-edge. -/
theorem handlePeriodLifts_b (k : ℕ) (t : unitInterval) :
    (handleAPeriodLift k (4 * k + (1 + t.val)),
      handleBPeriodLift k (4 * k + (1 + t.val))) = (1, t.val) := by
  rw [handleAPeriodLift_shift, handleBPeriodLift_shift]
  simp only [handleAPeriodLift, handleBPeriodLift, Nat.cast_zero, mul_zero, sub_zero]
  have h0 : handleRamp (1 + t.val) = 1 := handleRamp_of_one_le (by linarith [t.property.1])
  have h1 : handleRamp (1 + t.val - 2) = 0 := handleRamp_of_nonpos (by linarith [t.property.2])
  have h2 : handleRamp (1 + t.val - 1) = t.val := by
    rw [show 1 + t.val - 1 = t.val by ring]
    exact handleRamp_of_mem_unit t.property
  have h3 : handleRamp (1 + t.val - 3) = 0 := handleRamp_of_nonpos (by linarith [t.property.2])
  rw [h0,h1,h2,h3]
  simp

/-- The paired reverse b-edge differs only by an integral a-coordinate. -/
theorem handlePeriodLifts_b_pair (k : ℕ) (t : unitInterval) :
    (handleAPeriodLift k (4 * k + (4 - t.val)),
      handleBPeriodLift k (4 * k + (4 - t.val))) = (0, t.val) := by
  rw [handleAPeriodLift_shift, handleBPeriodLift_shift]
  simp only [handleAPeriodLift, handleBPeriodLift, Nat.cast_zero, mul_zero, sub_zero]
  have h0 : handleRamp (4 - t.val) = 1 := handleRamp_of_one_le (by linarith [t.property.2])
  have h1 : handleRamp (4 - t.val - 2) = 1 := handleRamp_of_one_le (by linarith [t.property.2])
  have h2 : handleRamp (4 - t.val - 1) = 1 := handleRamp_of_one_le (by linarith [t.property.2])
  have h3 : handleRamp (4 - t.val - 3) = 1 - t.val := by
    rw [show 4 - t.val - 3 = 1 - t.val by ring]
    exact handleRamp_of_mem_unit ⟨by linarith [t.property.2], by linarith [t.property.1]⟩
  rw [h0,h1,h2,h3]
  ext <;> ring

/-- Boundary lifts for one handle vanish identically on every different handle block. -/
theorem handlePeriodLifts_other (k i : ℕ) (hne : i ≠ k) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 4) :
    (handleAPeriodLift k (4 * i + r), handleBPeriodLift k (4 * i + r)) = (0, 0) := by
  rcases lt_or_gt_of_ne hne with hi | hi
  · have hik : (i : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hi
    have h0 : 4 * (i : ℝ) + r - 4 * k ≤ 0 := by nlinarith [hr.2]
    simp only [handleAPeriodLift, handleBPeriodLift]
    rw [handleRamp_of_nonpos h0,
      handleRamp_of_nonpos (by linarith : 4 * (i : ℝ) + r - 4 * k - 2 ≤ 0),
      handleRamp_of_nonpos (by linarith : 4 * (i : ℝ) + r - 4 * k - 1 ≤ 0),
      handleRamp_of_nonpos (by linarith : 4 * (i : ℝ) + r - 4 * k - 3 ≤ 0)]
    simp
  · have hik : (k : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt hi
    have h0 : 4 ≤ 4 * (i : ℝ) + r - 4 * k := by nlinarith [hr.1]
    simp only [handleAPeriodLift, handleBPeriodLift]
    rw [handleRamp_of_one_le (by linarith : 1 ≤ 4 * (i : ℝ) + r - 4 * k),
      handleRamp_of_one_le (by linarith : 1 ≤ 4 * (i : ℝ) + r - 4 * k - 2),
      handleRamp_of_one_le (by linarith : 1 ≤ 4 * (i : ℝ) + r - 4 * k - 1),
      handleRamp_of_one_le (by linarith : 1 ≤ 4 * (i : ℝ) + r - 4 * k - 3)]
    simp

/-- Three real boundary coordinates: the first handle's a,b and the second handle's a. -/
def handleThreeBoundaryLift (g : ℕ) (r : ℝ) : Fin 3 → ℝ :=
  ![handleAPeriodLift 0 (4 * g * r), handleBPeriodLift 0 (4 * g * r),
    handleAPeriodLift 1 (4 * g * r)]

theorem handleThreeBoundaryLift_continuous (g : ℕ) : Continuous (handleThreeBoundaryLift g) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact (handleAPeriodLift_continuous 0).comp (continuous_const.mul continuous_id)
  · exact (handleBPeriodLift_continuous 0).comp (continuous_const.mul continuous_id)
  · exact (handleAPeriodLift_continuous 1).comp (continuous_const.mul continuous_id)

theorem handleThreeBoundaryLift_zero (g : ℕ) : handleThreeBoundaryLift g 0 = 0 := by
  ext i
  fin_cases i <;> norm_num [handleThreeBoundaryLift, handleAPeriodLift, handleBPeriodLift, handleRamp]

theorem handleThreeBoundaryLift_one {g : ℕ} (hg : 2 ≤ g) : handleThreeBoundaryLift g 1 = 0 := by
  have h0 : g ≠ 0 := by omega
  have h1 : g ≠ 1 := by omega
  have hr : (0 : ℝ) ∈ Icc (0 : ℝ) 4 := by norm_num
  have ha := ((Prod.mk.inj (handlePeriodLifts_other 0 g h0 hr)).1)
  have hb := ((Prod.mk.inj (handlePeriodLifts_other 0 g h0 hr)).2)
  have hc := ((Prod.mk.inj (handlePeriodLifts_other 1 g h1 hr)).1)
  simp only [add_zero] at ha hb hc
  ext i
  fin_cases i <;> simpa only [handleThreeBoundaryLift, mul_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply] using (by first | exact ha | exact hb | exact hc)

theorem handleAPeriodLift_circle_a (k i : ℕ) (t : unitInterval) :
    (handleAPeriodLift k (4 * i + t.val) : AddCircle (1 : ℝ)) =
      (handleAPeriodLift k (4 * i + (3 - t.val)) : AddCircle (1 : ℝ)) := by
  by_cases he : i = k
  · subst i
    rw [((Prod.mk.inj (handlePeriodLifts_a k t)).1),
      ((Prod.mk.inj (handlePeriodLifts_a_pair k t)).1)]
  · rw [((Prod.mk.inj (handlePeriodLifts_other k i he
        (show t.val ∈ Icc (0 : ℝ) 4 from ⟨t.property.1, by linarith [t.property.2]⟩))).1),
      ((Prod.mk.inj (handlePeriodLifts_other k i he
        (show 3 - t.val ∈ Icc (0 : ℝ) 4 from ⟨by linarith [t.property.2], by linarith [t.property.1]⟩))).1)]

theorem handleBPeriodLift_circle_a (k i : ℕ) (t : unitInterval) :
    (handleBPeriodLift k (4 * i + t.val) : AddCircle (1 : ℝ)) =
      (handleBPeriodLift k (4 * i + (3 - t.val)) : AddCircle (1 : ℝ)) := by
  by_cases he : i = k
  · subst i
    rw [((Prod.mk.inj (handlePeriodLifts_a k t)).2),
      ((Prod.mk.inj (handlePeriodLifts_a_pair k t)).2)]
    simp only [AddCircle.coe_zero, AddCircle.coe_period]
  · rw [((Prod.mk.inj (handlePeriodLifts_other k i he
        (show t.val ∈ Icc (0 : ℝ) 4 from ⟨t.property.1, by linarith [t.property.2]⟩))).2),
      ((Prod.mk.inj (handlePeriodLifts_other k i he
        (show 3 - t.val ∈ Icc (0 : ℝ) 4 from ⟨by linarith [t.property.2], by linarith [t.property.1]⟩))).2)]

theorem handleAPeriodLift_circle_b (k i : ℕ) (t : unitInterval) :
    (handleAPeriodLift k (4 * i + (1 + t.val)) : AddCircle (1 : ℝ)) =
      (handleAPeriodLift k (4 * i + (4 - t.val)) : AddCircle (1 : ℝ)) := by
  by_cases he : i = k
  · subst i
    rw [((Prod.mk.inj (handlePeriodLifts_b k t)).1),
      ((Prod.mk.inj (handlePeriodLifts_b_pair k t)).1)]
    simp only [AddCircle.coe_zero, AddCircle.coe_period]
  · rw [((Prod.mk.inj (handlePeriodLifts_other k i he
        (show 1 + t.val ∈ Icc (0 : ℝ) 4 from ⟨by linarith [t.property.1], by linarith [t.property.2]⟩))).1),
      ((Prod.mk.inj (handlePeriodLifts_other k i he
        (show 4 - t.val ∈ Icc (0 : ℝ) 4 from ⟨by linarith [t.property.2], by linarith [t.property.1]⟩))).1)]

theorem handleBPeriodLift_circle_b (k i : ℕ) (t : unitInterval) :
    (handleBPeriodLift k (4 * i + (1 + t.val)) : AddCircle (1 : ℝ)) =
      (handleBPeriodLift k (4 * i + (4 - t.val)) : AddCircle (1 : ℝ)) := by
  by_cases he : i = k
  · subst i
    rw [((Prod.mk.inj (handlePeriodLifts_b k t)).2),
      ((Prod.mk.inj (handlePeriodLifts_b_pair k t)).2)]
  · rw [((Prod.mk.inj (handlePeriodLifts_other k i he
        (show 1 + t.val ∈ Icc (0 : ℝ) 4 from ⟨by linarith [t.property.1], by linarith [t.property.2]⟩))).2),
      ((Prod.mk.inj (handlePeriodLifts_other k i he
        (show 4 - t.val ∈ Icc (0 : ℝ) 4 from ⟨by linarith [t.property.2], by linarith [t.property.1]⟩))).2)]

/-- Choose the genuine continuous real extension of the three periodic boundary lifts. -/
def handleThreeExtension (g : ℕ) (hg : 2 ≤ g) : C(ℂ, Fin 3 → ℝ) :=
  Classical.choose (exists_handleBoundaryExtension (handleThreeBoundaryLift g)
    (handleThreeBoundaryLift_continuous g) (by rw [handleThreeBoundaryLift_zero, handleThreeBoundaryLift_one hg]))

theorem handleThreeExtension_boundary (g : ℕ) (hg : 2 ≤ g) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    handleThreeExtension g hg (handleBoundaryPoint r).val = handleThreeBoundaryLift g r :=
  Classical.choose_spec (exists_handleBoundaryExtension (handleThreeBoundaryLift g)
    (handleThreeBoundaryLift_continuous g) (by rw [handleThreeBoundaryLift_zero, handleThreeBoundaryLift_one hg])) r hr

/-- Actual closed-disc coordinates in the product of three real circles. -/
def handleThreeDiscMap (g : ℕ) (hg : 2 ≤ g) : C(Metric.closedBall (0 : ℂ) 1, Fin 3 → AddCircle (1 : ℝ)) where
  toFun z i := (handleThreeExtension g hg z.val i : AddCircle (1 : ℝ))
  continuous_toFun := continuous_pi fun i =>
    QuotientAddGroup.continuous_mk.comp
      ((continuous_apply i).comp ((handleThreeExtension g hg).continuous.comp continuous_subtype_val))

theorem handleThreeDiscMap_boundary (g : ℕ) (hg : 2 ≤ g) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    handleThreeDiscMap g hg (handleBoundaryPoint r) =
      fun i => (handleThreeBoundaryLift g r i : AddCircle (1 : ℝ)) := by
  funext i
  change (handleThreeExtension g hg (handleBoundaryPoint r).val i : AddCircle (1 : ℝ)) = _
  rw [handleThreeExtension_boundary g hg hr]

/-- Every literal point of a canonical polygon side has a parameter in the full boundary interval. -/
theorem handleSideFraction_mem_unit {g : ℕ} (hg : 0 < g) (i : Fin g) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 4) :
    (4 * (i.val : ℝ) + r) / (4 * (g : ℝ)) ∈ Icc (0 : ℝ) 1 := by
  have hgr : 0 < (g : ℝ) := by exact_mod_cast hg
  have hi : (i.val : ℝ) + 1 ≤ g := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  have hden : 0 < 4 * (g : ℝ) := by positivity
  exact ⟨div_nonneg (add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg i.val)) hr.1) hden.le,
    (div_le_one hden).mpr (by nlinarith [hr.2])⟩

/-- Exact torus coordinates on every literal canonical polygon side. -/
theorem handleThreeDiscMap_on_side {g : ℕ} (hg : 2 ≤ g) (i : Fin g) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 4) :
    handleThreeDiscMap g hg (handleBoundaryPoint ((4 * (i.val : ℝ) + r) / (4 * (g : ℝ)))) =
      ![(handleAPeriodLift 0 (4 * i.val + r) : AddCircle (1 : ℝ)),
        (handleBPeriodLift 0 (4 * i.val + r) : AddCircle (1 : ℝ)),
        (handleAPeriodLift 1 (4 * i.val + r) : AddCircle (1 : ℝ))] := by
  have hden : 4 * (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : 4 * g ≠ 0)
  rw [handleThreeDiscMap_boundary g hg (handleSideFraction_mem_unit (by omega) i hr)]
  simp only [handleThreeBoundaryLift, mul_div_cancel₀ _ hden]
  funext j
  fin_cases j <;> rfl

/-- The three actual circle coordinates respect every original oriented 4g-polygon generator. -/
theorem handleThreeDiscMap_respects {g : ℕ} (hg : 2 ≤ g)
    {z w : Metric.closedBall (0 : ℂ) 1} (h : CanonicalHandleIdent g z w) :
    handleThreeDiscMap g hg z = handleThreeDiscMap g hg w := by
  cases h with
  | a t i =>
    rw [show 4 * (i.val : ℝ) + 3 - t.val = 4 * i.val + (3 - t.val) by ring]
    rw [handleThreeDiscMap_on_side hg i
        (show t.val ∈ Icc (0 : ℝ) 4 from ⟨t.property.1, by linarith [t.property.2]⟩),
      handleThreeDiscMap_on_side hg i
        (show 3 - t.val ∈ Icc (0 : ℝ) 4 from ⟨by linarith [t.property.2], by linarith [t.property.1]⟩)]
    funext j
    fin_cases j
    · exact handleAPeriodLift_circle_a 0 i.val t
    · exact handleBPeriodLift_circle_a 0 i.val t
    · exact handleAPeriodLift_circle_a 1 i.val t
  | b t i =>
    rw [show 4 * (i.val : ℝ) + 1 + t.val = 4 * i.val + (1 + t.val) by ring,
      show 4 * (i.val : ℝ) + 4 - t.val = 4 * i.val + (4 - t.val) by ring]
    rw [handleThreeDiscMap_on_side hg i
        (show 1 + t.val ∈ Icc (0 : ℝ) 4 from ⟨by linarith [t.property.1], by linarith [t.property.2]⟩),
      handleThreeDiscMap_on_side hg i
        (show 4 - t.val ∈ Icc (0 : ℝ) 4 from ⟨by linarith [t.property.2], by linarith [t.property.1]⟩)]
    funext j
    fin_cases j
    · exact handleAPeriodLift_circle_b 0 i.val t
    · exact handleBPeriodLift_circle_b 0 i.val t
    · exact handleAPeriodLift_circle_b 1 i.val t

/-- A genuine continuous map from the actual canonical handle quotient into the actual three-torus. -/
def canonicalHandleThreeTorusMap (g : ℕ) (hg : 2 ≤ g) :
    C(Quot (CanonicalHandleIdent g), Fin 3 → AddCircle (1 : ℝ)) where
  toFun := Quot.lift (handleThreeDiscMap g hg) (fun _ _ h => handleThreeDiscMap_respects hg h)
  continuous_toFun := continuous_quot_lift _ (handleThreeDiscMap g hg).continuous

/-- Literal quotient vertex with real polygon clock coordinate. -/
def canonicalHandleVertex (g : ℕ) (r : ℝ) : Quot (CanonicalHandleIdent g) :=
  Quot.mk _ (handleBoundaryPoint (r / (4 * g)))

theorem canonicalHandleVertex_a (g : ℕ) (i : Fin g) (t : unitInterval) :
    canonicalHandleVertex g (4 * i.val + t.val) =
      canonicalHandleVertex g (4 * i.val + 3 - t.val) :=
  Quot.sound (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent.a t i)

theorem canonicalHandleVertex_b (g : ℕ) (i : Fin g) (t : unitInterval) :
    canonicalHandleVertex g (4 * i.val + 1 + t.val) =
      canonicalHandleVertex g (4 * i.val + 4 - t.val) :=
  Quot.sound (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent.b t i)

/-- All four vertices of a handle block become the same actual quotient point. -/
theorem canonicalHandleVertex_block (g : ℕ) (i : Fin g) :
    canonicalHandleVertex g (4 * i.val + 1) = canonicalHandleVertex g (4 * i.val) ∧
    canonicalHandleVertex g (4 * i.val + 2) = canonicalHandleVertex g (4 * i.val) ∧
    canonicalHandleVertex g (4 * i.val + 4) = canonicalHandleVertex g (4 * i.val) := by
  have ha0 := canonicalHandleVertex_a g i 0
  have ha1 := canonicalHandleVertex_a g i 1
  have hb0 := canonicalHandleVertex_b g i 0
  have hb1 := canonicalHandleVertex_b g i 1
  simp only [Set.Icc.coe_zero, Set.Icc.coe_one, add_zero, sub_zero] at ha0 ha1 hb0 hb1
  have h31 : 4 * (i.val : ℝ) + 3 - 1 = 4 * i.val + 2 := by ring
  have h41 : 4 * (i.val : ℝ) + 4 - 1 = 4 * i.val + 3 := by ring
  have h11 : 4 * (i.val : ℝ) + 1 + 1 = 4 * i.val + 2 := by ring
  rw [h31] at ha1
  rw [h11, h41] at hb1
  have h1 := ha1.trans (hb1.trans ha0.symm)
  exact ⟨h1, hb1.trans ha0.symm, hb0.symm.trans h1⟩

theorem handleBoundaryPoint_continuous : Continuous handleBoundaryPoint := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id))

/-- A genuine boundary edge becomes a based loop when its endpoint vertices agree with the base. -/
def canonicalHandleEdgeLoop (g : ℕ) (r : ℝ)
    (h0 : canonicalHandleVertex g r = canonicalHandleVertex g 0)
    (h1 : canonicalHandleVertex g (r + 1) = canonicalHandleVertex g 0) :
    Path (canonicalHandleVertex g 0) (canonicalHandleVertex g 0) where
  toFun t := canonicalHandleVertex g (r + t.val)
  continuous_toFun := continuous_quot_mk.comp
    (handleBoundaryPoint_continuous.comp
      ((continuous_const.add continuous_subtype_val).div_const (4 * (g : ℝ))))
  source' := by simpa only [Set.Icc.coe_zero, add_zero] using h0
  target' := by simpa only [Set.Icc.coe_one] using h1

/-- The three chosen handle-edge clock positions. -/
def handleThreeEdgeClock : Fin 3 → ℝ := ![0, 1, 4]

theorem handleThreeEdge_endpoints {g : ℕ} (hg : 2 ≤ g) (j : Fin 3) :
    canonicalHandleVertex g (handleThreeEdgeClock j) = canonicalHandleVertex g 0 ∧
    canonicalHandleVertex g (handleThreeEdgeClock j + 1) = canonicalHandleVertex g 0 := by
  have h0 := canonicalHandleVertex_block g ⟨0, by omega⟩
  have h1 := canonicalHandleVertex_block g ⟨1, by omega⟩
  norm_num at h0 h1
  fin_cases j
  · norm_num [handleThreeEdgeClock]
    exact h0.1
  · norm_num [handleThreeEdgeClock]
    exact ⟨h0.1, h0.2.1⟩
  · norm_num [handleThreeEdgeClock]
    exact ⟨h0.2.2, h1.1.trans h0.2.2⟩

/-- Three actual based loops on the actual high-handle quotient. -/
def canonicalHandleThreeEdgeLoop (g : ℕ) (hg : 2 ≤ g) (j : Fin 3) :
    Path (canonicalHandleVertex g 0) (canonicalHandleVertex g 0) :=
  canonicalHandleEdgeLoop g (handleThreeEdgeClock j)
    (handleThreeEdge_endpoints hg j).1 (handleThreeEdge_endpoints hg j).2

/-- The three integral winding numbers induced by the true continuous quotient map. -/
def canonicalHandleThreeWindingHom (g : ℕ) (hg : 2 ≤ g) :
    FundamentalGroup (Quot (CanonicalHandleIdent g)) (canonicalHandleVertex g 0) →*
      (Fin 3 → Multiplicative ℤ) where
  toFun p j := AddCircle.windingNumberIso _
    (FundamentalGroup.map
      ⟨fun q => canonicalHandleThreeTorusMap g hg q j,
        (continuous_apply j).comp (canonicalHandleThreeTorusMap g hg).continuous⟩
      (canonicalHandleVertex g 0) p)
  map_one' := by funext j; simp
  map_mul' p q := by funext j; simp

/-- Explicit real lifts along the three chosen geometric boundary loops. -/
def handleThreeEdgeRealLift (j k : Fin 3) : C(unitInterval, ℝ) where
  toFun t := ![handleAPeriodLift 0 (handleThreeEdgeClock j + t.val),
    handleBPeriodLift 0 (handleThreeEdgeClock j + t.val),
    handleAPeriodLift 1 (handleThreeEdgeClock j + t.val)] k
  continuous_toFun := by
    fin_cases k
    · exact (handleAPeriodLift_continuous 0).comp (continuous_const.add continuous_subtype_val)
    · exact (handleBPeriodLift_continuous 0).comp (continuous_const.add continuous_subtype_val)
    · exact (handleAPeriodLift_continuous 1).comp (continuous_const.add continuous_subtype_val)

theorem handleThreeEdgeRealLift_endpoint_difference (j k : Fin 3) :
    handleThreeEdgeRealLift j k 1 - handleThreeEdgeRealLift j k 0 =
      if j = k then 1 else 0 := by
  fin_cases j <;> fin_cases k <;>
    norm_num [handleThreeEdgeRealLift, handleThreeEdgeClock,
      handleAPeriodLift, handleBPeriodLift, handleRamp]

/-- Coordinate evaluation of the genuine continuous three-torus quotient map. -/
def canonicalHandleCircleMap (g : ℕ) (hg : 2 ≤ g) (k : Fin 3) :
    C(Quot (CanonicalHandleIdent g), AddCircle (1 : ℝ)) :=
  ⟨fun q => canonicalHandleThreeTorusMap g hg q k,
    (continuous_apply k).comp (canonicalHandleThreeTorusMap g hg).continuous⟩

theorem handleThreeEdgeRealLift_is_lift {g : ℕ} (hg : 2 ≤ g) (j k : Fin 3) :
    (fun t => (handleThreeEdgeRealLift j k t : AddCircle (1 : ℝ))) =
      (canonicalHandleThreeEdgeLoop g hg j).map (canonicalHandleCircleMap g hg k).continuous := by
  funext t
  have hden : 0 < 4 * (g : ℝ) := by
    have hgr : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    positivity
  have hclock : 0 ≤ handleThreeEdgeClock j ∧ handleThreeEdgeClock j ≤ 4 := by
    fin_cases j <;> norm_num [handleThreeEdgeClock]
  have ht : (handleThreeEdgeClock j + t.val) / (4 * (g : ℝ)) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by linarith [t.property.1]) hden.le, (div_le_one hden).mpr ?_⟩
    have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
    linarith [t.property.2]
  change _ = handleThreeDiscMap g hg (handleBoundaryPoint _) k
  rw [handleThreeDiscMap_boundary g hg ht]
  simp only [handleThreeBoundaryLift, mul_div_cancel₀ _ hden.ne']
  rfl

/-- Each of the three actual edge loops contributes exactly one independent integral winding. -/
theorem canonicalHandleThreeWindingHom_edge {g : ℕ} (hg : 2 ≤ g) (j k : Fin 3) :
    (canonicalHandleThreeWindingHom g hg
      (.of (.mk (canonicalHandleThreeEdgeLoop g hg j))) k).toAdd =
      if j = k then 1 else 0 := by
  have h := AddCircle.windingNumber_eq_div
    ((canonicalHandleThreeEdgeLoop g hg j).map (canonicalHandleCircleMap g hg k).continuous)
    (handleThreeEdgeRealLift j k) (handleThreeEdgeRealLift_is_lift hg j k)
  rw [handleThreeEdgeRealLift_endpoint_difference, div_one] at h
  change ((canonicalHandleThreeWindingHom g hg
      (.of (.mk (canonicalHandleThreeEdgeLoop g hg j))) k).toAdd : ℝ) = _ at h
  exact_mod_cast h

/-- The homotopy classes of the three literal polygon edge loops. -/
def canonicalHandleThreeLoopClass (g : ℕ) (hg : 2 ≤ g) (j : Fin 3) :
    FundamentalGroup (Quot (CanonicalHandleIdent g)) (canonicalHandleVertex g 0) :=
  .of (.mk (canonicalHandleThreeEdgeLoop g hg j))

theorem canonicalHandleThreeWindingHom_loopClass {g : ℕ} (hg : 2 ≤ g) (j : Fin 3) :
    canonicalHandleThreeWindingHom g hg (canonicalHandleThreeLoopClass g hg j) =
      fun k => Multiplicative.ofAdd (if j = k then (1 : ℤ) else 0) := by
  funext k
  apply Multiplicative.toAdd.injective
  exact canonicalHandleThreeWindingHom_edge hg j k

/-- The actual canonical high-handle surface has three independent winding numbers. -/
theorem canonicalHandleThreeWindingHom_surjective {g : ℕ} (hg : 2 ≤ g) :
    Function.Surjective (canonicalHandleThreeWindingHom g hg) := by
  intro v
  refine ⟨canonicalHandleThreeLoopClass g hg 0 ^ (v 0).toAdd *
      canonicalHandleThreeLoopClass g hg 1 ^ (v 1).toAdd *
      canonicalHandleThreeLoopClass g hg 2 ^ (v 2).toAdd, ?_⟩
  simp only [map_mul, map_zpow, canonicalHandleThreeWindingHom_loopClass]
  funext k
  fin_cases k <;> simp <;> apply Multiplicative.toAdd.injective <;>
    simp

/-- Three genuine independent winding numbers prevent a high-handle quotient from being a sphere. -/
theorem canonicalHandleQuot_not_homeomorphic_sphere {g : ℕ} (hg : 2 ≤ g) :
    ¬Nonempty (Quot (CanonicalHandleIdent g) ≃ₜ OnePoint ℂ) := by
  rintro ⟨e⟩
  let := riemannSphere_simplyConnected
  let : SimplyConnectedSpace (Quot (CanonicalHandleIdent g)) :=
    e.toHomotopyEquiv.simplyConnectedSpace
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.fundamentalGroup_not_surjective_three_windings_of_simplyConnected
    (canonicalHandleVertex g 0) (canonicalHandleThreeWindingHom g hg)
    (canonicalHandleThreeWindingHom_surjective hg)

/-- Three genuine independent winding numbers prevent a high-handle quotient from being a two-torus. -/
theorem canonicalHandleQuot_not_homeomorphic_torus {g : ℕ} (hg : 2 ≤ g) :
    ¬Nonempty (Quot (CanonicalHandleIdent g) ≃ₜ AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.not_homeomorphic_torus_of_surjective_three_windings
    (canonicalHandleVertex g 0) (canonicalHandleThreeWindingHom g hg)
    (canonicalHandleThreeWindingHom_surjective hg)

theorem canonicalHandleSurface_highGenus_not_sphere {g : ℕ} (hg : 2 ≤ g) :
    ¬Nonempty (CanonicalHandleSurface g ≃ₜ OnePoint ℂ) := by
  cases g with
  | zero => omega
  | succ k => exact canonicalHandleQuot_not_homeomorphic_sphere hg

theorem canonicalHandleSurface_highGenus_not_torus {g : ℕ} (hg : 2 ≤ g) :
    ¬Nonempty (CanonicalHandleSurface g ≃ₜ AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) := by
  cases g with
  | zero => omega
  | succ k => exact canonicalHandleQuot_not_homeomorphic_torus hg

/-- An actual handle-model genus at least two excludes both exceptional compact cover models. -/
theorem hasTopologicalGenus_ge_two_not_sphere_not_torus
    {X : Type*} [TopologicalSpace X] {g : ℕ} (hg : 2 ≤ g) (hX : HasTopologicalGenus X g) :
    (¬Nonempty (X ≃ₜ OnePoint ℂ)) ∧
      (¬Nonempty (X ≃ₜ AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  obtain ⟨e⟩ := hX
  exact ⟨fun ⟨f⟩ => canonicalHandleSurface_highGenus_not_sphere hg ⟨e.symm.trans f⟩,
    fun ⟨f⟩ => canonicalHandleSurface_highGenus_not_torus hg ⟨e.symm.trans f⟩⟩

/--
The genuine universal cover of a compact surface at least two handles
is conformally the disc, proved from the actual polygon topology rather than an analytic genus name.
-/
theorem RiemannUniversalCover.disc_model_of_topologicalGenus_ge_two
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {R : RiemannSurface X} (C : RiemannUniversalCover R)
    {g : ℕ} (hg : 2 ≤ g) (hX : HasTopologicalGenus X g) :
    @RiemannConformallyEquivalent C.space _ C.topology _ C.surface discRiemannSurface :=
  C.disc_model_iff_not_sphere_not_torus.mpr
    (hasTopologicalGenus_ge_two_not_sphere_not_torus hg hX)

/--
The compact zero-, one-, and higher-handle cases give the actual sphere,
plane, and disc universal covers.
-/
theorem RiemannUniversalCover.compact_topological_genus_models
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {R : RiemannSurface X} (C : RiemannUniversalCover R)
    (g : ℕ) (hX : HasTopologicalGenus X g) :
    (g = 0 → @RiemannConformallyEquivalent C.space (OnePoint ℂ) C.topology _ C.surface sphereRiemannSurface) ∧
    (g = 1 → @RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface complexPlaneRiemannSurface) ∧
    (2 ≤ g → @RiemannConformallyEquivalent C.space _ C.topology _ C.surface discRiemannSurface) := by
  refine ⟨?_, ?_, fun hg => C.disc_model_of_topologicalGenus_ge_two hg hX⟩
  · rintro rfl
    exact C.sphere_model_iff_topologicalGenus_zero.mpr hX
  · rintro rfl
    exact C.plane_model_iff_topologicalGenus_one.mpr hX

end LowDimensionalTopology.Geometry.Surfaces
