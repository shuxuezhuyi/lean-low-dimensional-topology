/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy

Only the oriented polygon edge-definition pattern is adapted from
LeanPool.ClassificationOfSurfaces.LeanEval.ChallengeDeps at
86da5902e640ceb44e53f88c4a04f870dc062126. The explicit gauge, square,
quotient and boundary-comparison proofs below are original project work.
-/
module
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CompactGenusTypes
@[expose] public section
noncomputable section
open Set Metric Filter Topology Bornology
namespace LowDimensionalTopology.Geometry.Surfaces

def complexDiamondSeminorm : Seminorm ℝ ℂ :=
  (normSeminorm ℝ ℝ).comp Complex.reCLM.toLinearMap +
    (normSeminorm ℝ ℝ).comp Complex.imCLM.toLinearMap

theorem complexDiamondSeminorm_apply (z : ℂ) :
    complexDiamondSeminorm z = |z.re| + |z.im| := rfl

theorem complexDiamondSeminorm_continuous : Continuous complexDiamondSeminorm :=
  Complex.continuous_re.abs.add Complex.continuous_im.abs

def discDiamondHomeomorph : ℂ ≃ₜ ℂ := by
  let s : Set ℂ := Metric.ball 0 1
  let t : Set ℂ := complexDiamondSeminorm.ball 0 1
  have hs : s ∈ 𝓝 0 := Metric.ball_mem_nhds _ zero_lt_one
  have ht : t ∈ 𝓝 0 := by
    dsimp only [t]
    rw [Seminorm.ball_zero_eq]
    exact (isOpen_lt complexDiamondSeminorm_continuous continuous_const).mem_nhds (by simp)
  have hb : IsVonNBounded ℝ t := by
    refine IsVonNBounded.subset ?_ (NormedSpace.isVonNBounded_ball ℝ ℂ 1)
    intro z hz
    rw [mem_ball_zero_iff]
    exact (Complex.norm_le_abs_re_add_abs_im z).trans_lt (by
      simpa only [t, Seminorm.mem_ball, sub_zero, complexDiamondSeminorm_apply] using hz)
  exact gaugeRescaleHomeomorph s t (convex_ball 0 1) hs
    (NormedSpace.isVonNBounded_ball ℝ ℂ 1) (complexDiamondSeminorm.convex_ball 0 1) ht hb

theorem discDiamondHomeomorph_apply (z : ℂ) :
    discDiamondHomeomorph z = (‖z‖ / (|z.re| + |z.im|)) • z := by
  change gaugeRescale (Metric.ball 0 1) (complexDiamondSeminorm.ball 0 1) z = _
  simp only [gaugeRescale, gauge_ball zero_le_one, div_one, Seminorm.gauge_ball,
    complexDiamondSeminorm_apply]

/-- Rescaling preserves radial distance as diamond distance. -/
theorem discDiamondHomeomorph_gauge (z : ℂ) :
    complexDiamondSeminorm (discDiamondHomeomorph z) = ‖z‖ := by
  rw [discDiamondHomeomorph_apply]
  by_cases hz : z = 0
  · simp [hz]
  have hp : 0 < complexDiamondSeminorm z :=
    (norm_pos_iff.mpr hz).trans_le (Complex.norm_le_abs_re_add_abs_im z)
  change complexDiamondSeminorm ((‖z‖ / complexDiamondSeminorm z) • z) = ‖z‖
  rw [map_smul_eq_mul, Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hp.le),
    div_mul_cancel₀ _ hp.ne']

/-- The disc is carried onto the true closed diamond. -/
theorem discDiamondHomeomorph_image_closedDisc :
    discDiamondHomeomorph '' Metric.closedBall (0 : ℂ) 1 =
      {z : ℂ | complexDiamondSeminorm z ≤ 1} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [mem_ofPred_eq, discDiamondHomeomorph_gauge] using mem_closedBall_zero_iff.mp hw
  · intro hz
    obtain ⟨w, rfl⟩ := discDiamondHomeomorph.surjective z
    exact ⟨w, mem_closedBall_zero_iff.mpr (by
      simpa only [mem_ofPred_eq, discDiamondHomeomorph_gauge] using hz), rfl⟩

/-- An affine plane homeomorphism sends the diamond's four vertices to the square's four vertices. -/
def diamondSquareAffine : ℂ ≃ₜ ℝ × ℝ where
  toFun z := ((1 - z.re + z.im) / 2, (1 - z.re - z.im) / 2)
  invFun w := ((1 - w.1 - w.2 : ℝ) : ℂ) + ((w.1 - w.2 : ℝ) : ℂ) * Complex.I
  left_inv z := by apply Complex.ext <;> dsimp <;> simp <;> ring
  right_inv w := by apply Prod.ext <;> dsimp <;> simp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The diamond condition is exactly the pair of unit interval coordinate conditions. -/
theorem diamondSquareAffine_mem_square_iff (z : ℂ) :
    diamondSquareAffine z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ↔
      complexDiamondSeminorm z ≤ 1 := by
  change (0 ≤ (1 - z.re + z.im) / 2 ∧ (1 - z.re + z.im) / 2 ≤ 1) ∧
    (0 ≤ (1 - z.re - z.im) / 2 ∧ (1 - z.re - z.im) / 2 ≤ 1) ↔
      |z.re| + |z.im| ≤ 1
  constructor
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
    rcases le_total 0 z.re with hx | hx <;>
      rcases le_total 0 z.im with hy | hy <;>
      simp only [abs_of_nonneg, abs_of_nonpos, hx, hy] <;> linarith
  · intro hz
    have hx := le_abs_self z.re
    have hnx := neg_le_abs z.re
    have hy := le_abs_self z.im
    have hny := neg_le_abs z.im
    constructor <;> constructor <;> linarith

/-- The affine diamond-to-square change sends exactly the diamond onto the unit square. -/
theorem diamondSquareAffine_image_diamond :
    diamondSquareAffine '' {z : ℂ | complexDiamondSeminorm z ≤ 1} =
      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (diamondSquareAffine_mem_square_iff z).mpr hz
  · intro hw
    obtain ⟨z, rfl⟩ := diamondSquareAffine.surjective w
    exact ⟨z, (diamondSquareAffine_mem_square_iff z).mp hw, rfl⟩

/-- A concrete closed-disc to closed-square homeomorphism with the boundary corners in cyclic order. -/
def closedDiscSquareHomeomorph : Metric.closedBall (0 : ℂ) 1 ≃ₜ
    unitInterval × unitInterval := by
  let e := discDiamondHomeomorph.trans diamondSquareAffine
  have he : e '' Metric.closedBall (0 : ℂ) 1 =
      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    calc (e : ℂ → ℝ × ℝ) '' Metric.closedBall (0 : ℂ) 1
        = diamondSquareAffine '' (discDiamondHomeomorph '' Metric.closedBall (0 : ℂ) 1) :=
          by
            change (diamondSquareAffine ∘ discDiamondHomeomorph) '' _ = _
            exact (Set.image_image (diamondSquareAffine : ℂ → ℝ × ℝ)
              (discDiamondHomeomorph : ℂ → ℂ) (Metric.closedBall (0 : ℂ) 1)).symm
      _ = _ := by rw [discDiamondHomeomorph_image_closedDisc, diamondSquareAffine_image_diamond]
  exact (e.image _).trans ((Homeomorph.setCongr he).trans (Homeomorph.Set.prod _ _))

/-- The closed-disc to square map commutes with the first opposite-edge reflection. -/
theorem discDiamondHomeomorph_opposite_a (z : ℂ) :
    discDiamondHomeomorph (-Complex.I * star z) =
      -Complex.I * star (discDiamondHomeomorph z) := by
  have hn : ‖-Complex.I * star z‖ = ‖z‖ := by simp
  have hp : |(-Complex.I * star z).re| + |(-Complex.I * star z).im| =
      |z.re| + |z.im| := by simp [Complex.mul_re, Complex.mul_im, add_comm]
  rw [discDiamondHomeomorph_apply, hn, hp, discDiamondHomeomorph_apply]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    ring
  · simp [Complex.mul_re, Complex.mul_im]

/-- The analogous reflection for the other pair of square sides. -/
theorem discDiamondHomeomorph_opposite_b (z : ℂ) :
    discDiamondHomeomorph (Complex.I * star z) =
      Complex.I * star (discDiamondHomeomorph z) := by
  have hn : ‖Complex.I * star z‖ = ‖z‖ := by simp
  have hp : |(Complex.I * star z).re| + |(Complex.I * star z).im| =
      |z.re| + |z.im| := by simp [Complex.mul_re, Complex.mul_im, add_comm]
  rw [discDiamondHomeomorph_apply, hn, hp, discDiamondHomeomorph_apply]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    ring
  · simp [Complex.mul_re, Complex.mul_im]

/-- The underlying coordinate formula of the concrete disc-to-square homeomorphism. -/
theorem closedDiscSquareHomeomorph_apply (z : Metric.closedBall (0 : ℂ) 1) :
    ((closedDiscSquareHomeomorph z).1.val, (closedDiscSquareHomeomorph z).2.val) =
      diamondSquareAffine (discDiamondHomeomorph z.val) := rfl

/-- Boundary coordinates of the usual circular polygon carrier. -/
def handleBoundaryPoint (r : ℝ) : Metric.closedBall (0 : ℂ) 1 :=
  ⟨Circle.exp (2 * Real.pi * r), mem_closedBall_zero_iff.mpr (Circle.norm_coe _).le⟩

theorem handleBoundaryPoint_norm (r : ℝ) : ‖(handleBoundaryPoint r).val‖ = 1 := by
  exact Circle.norm_coe _

theorem handleBoundaryPoint_re (r : ℝ) :
    (handleBoundaryPoint r).val.re = Real.cos (2 * Real.pi * r) := by
  exact Complex.exp_ofReal_mul_I_re (2 * Real.pi * r)

theorem handleBoundaryPoint_im (r : ℝ) :
    (handleBoundaryPoint r).val.im = Real.sin (2 * Real.pi * r) := by
  exact Complex.exp_ofReal_mul_I_im (2 * Real.pi * r)

theorem handleBoundaryPoint_opposite_a (t : ℝ) :
    (handleBoundaryPoint ((3 - t) / 4)).val =
      -Complex.I * star (handleBoundaryPoint (t / 4)).val := by
  have he : 2 * Real.pi * ((3 - t) / 4) = 3 * Real.pi / 2 - 2 * Real.pi * (t / 4) := by ring
  apply Complex.ext <;> simp only [handleBoundaryPoint_re, handleBoundaryPoint_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  · rw [he, Real.cos_sub]
    norm_num [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.cos_add, Real.sin_add]
  · rw [he, Real.sin_sub]
    norm_num [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.cos_add, Real.sin_add]

def closedDiscOppositeA (z : Metric.closedBall (0 : ℂ) 1) : Metric.closedBall (0 : ℂ) 1 :=
  ⟨-Complex.I * star z.val, mem_closedBall_zero_iff.mpr (by
    simpa using mem_closedBall_zero_iff.mp z.property)⟩

/-- A first-quadrant circular side and its paired side become exactly the square's horizontal pair. -/
theorem closedDiscSquareHomeomorph_opposite_a
    (z : Metric.closedBall (0 : ℂ) 1) (hn : ‖z.val‖ = 1)
    (hr : 0 ≤ z.val.re) (hi : 0 ≤ z.val.im) :
    (closedDiscSquareHomeomorph z).2 = 0 ∧
      (closedDiscSquareHomeomorph (closedDiscOppositeA z)).1 =
        (closedDiscSquareHomeomorph z).1 ∧
      (closedDiscSquareHomeomorph (closedDiscOppositeA z)).2 = 1 := by
  have hs : 0 ≤ ‖z.val‖ / (|z.val.re| + |z.val.im|) :=
    div_nonneg (norm_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hfr : 0 ≤ (discDiamondHomeomorph z.val).re := by
    rw [discDiamondHomeomorph_apply]
    simpa only [Complex.smul_re, smul_eq_mul] using mul_nonneg hs hr
  have hfi : 0 ≤ (discDiamondHomeomorph z.val).im := by
    rw [discDiamondHomeomorph_apply]
    simpa only [Complex.smul_im, smul_eq_mul] using mul_nonneg hs hi
  have hsum : (discDiamondHomeomorph z.val).re + (discDiamondHomeomorph z.val).im = 1 := by
    have hh := discDiamondHomeomorph_gauge z.val
    simpa only [complexDiamondSeminorm_apply, abs_of_nonneg hfr, abs_of_nonneg hfi, hn] using hh
  constructor
  · apply Subtype.ext
    change (1 - (discDiamondHomeomorph z.val).re - (discDiamondHomeomorph z.val).im) / 2 = 0
    linarith
  constructor
  · apply Subtype.ext
    change (1 - (discDiamondHomeomorph (-Complex.I * star z.val)).re +
      (discDiamondHomeomorph (-Complex.I * star z.val)).im) / 2 =
        (1 - (discDiamondHomeomorph z.val).re + (discDiamondHomeomorph z.val).im) / 2
    rw [discDiamondHomeomorph_opposite_a]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  · apply Subtype.ext
    change (1 - (discDiamondHomeomorph (-Complex.I * star z.val)).re -
      (discDiamondHomeomorph (-Complex.I * star z.val)).im) / 2 = 1
    rw [discDiamondHomeomorph_opposite_a]
    simp [Complex.mul_re, Complex.mul_im]
    linarith

def closedDiscOppositeB (z : Metric.closedBall (0 : ℂ) 1) : Metric.closedBall (0 : ℂ) 1 :=
  ⟨Complex.I * star z.val, mem_closedBall_zero_iff.mpr (by
    simpa using mem_closedBall_zero_iff.mp z.property)⟩

/-- A second-quadrant circular side and its paired side become the other square edge pair. -/
theorem closedDiscSquareHomeomorph_opposite_b
    (z : Metric.closedBall (0 : ℂ) 1) (hn : ‖z.val‖ = 1)
    (hr : z.val.re ≤ 0) (hi : 0 ≤ z.val.im) :
    (closedDiscSquareHomeomorph z).1 = 1 ∧
      (closedDiscSquareHomeomorph (closedDiscOppositeB z)).1 = 0 ∧
      (closedDiscSquareHomeomorph (closedDiscOppositeB z)).2 =
        (closedDiscSquareHomeomorph z).2 := by
  have hs : 0 ≤ ‖z.val‖ / (|z.val.re| + |z.val.im|) :=
    div_nonneg (norm_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hfr : (discDiamondHomeomorph z.val).re ≤ 0 := by
    rw [discDiamondHomeomorph_apply]
    simpa only [Complex.smul_re, smul_eq_mul] using mul_nonpos_of_nonneg_of_nonpos hs hr
  have hfi : 0 ≤ (discDiamondHomeomorph z.val).im := by
    rw [discDiamondHomeomorph_apply]
    simpa only [Complex.smul_im, smul_eq_mul] using mul_nonneg hs hi
  have hsum : -(discDiamondHomeomorph z.val).re + (discDiamondHomeomorph z.val).im = 1 := by
    have hh := discDiamondHomeomorph_gauge z.val
    simpa only [complexDiamondSeminorm_apply, abs_of_nonpos hfr, abs_of_nonneg hfi, hn] using hh
  constructor
  · apply Subtype.ext
    change (1 - (discDiamondHomeomorph z.val).re + (discDiamondHomeomorph z.val).im) / 2 = 1
    linarith
  constructor
  · apply Subtype.ext
    change (1 - (discDiamondHomeomorph (Complex.I * star z.val)).re +
      (discDiamondHomeomorph (Complex.I * star z.val)).im) / 2 = 0
    rw [discDiamondHomeomorph_opposite_b]
    simp [Complex.mul_re, Complex.mul_im]
    linarith
  · apply Subtype.ext
    change (1 - (discDiamondHomeomorph (Complex.I * star z.val)).re -
      (discDiamondHomeomorph (Complex.I * star z.val)).im) / 2 =
        (1 - (discDiamondHomeomorph z.val).re - (discDiamondHomeomorph z.val).im) / 2
    rw [discDiamondHomeomorph_opposite_b]
    simp [Complex.mul_re, Complex.mul_im]
    ring

/-- Every actual unit-circle point in the first quadrant lies on the first canonical side. -/
theorem handleBoundaryPoint_first_quadrant
    (z : Metric.closedBall (0 : ℂ) 1) (hn : ‖z.val‖ = 1)
    (hr : 0 ≤ z.val.re) (hi : 0 ≤ z.val.im) :
    ∃ t : unitInterval, handleBoundaryPoint (t.val / 4) = z := by
  let a := z.val.arg
  have ha0 : 0 ≤ a := Complex.arg_nonneg_iff.mpr hi
  have ha1 : a ≤ Real.pi / 2 := Complex.arg_le_pi_div_two_iff.mpr (Or.inl hr)
  have hpi : 0 < Real.pi / 2 := by positivity
  let t : unitInterval := ⟨a / (Real.pi / 2),
    div_nonneg ha0 hpi.le, (div_le_one hpi).mpr ha1⟩
  refine ⟨t, ?_⟩
  apply Subtype.ext
  change (Circle.exp (2 * Real.pi * (t.val / 4)) : ℂ) = z.val
  have he : 2 * Real.pi * (t.val / 4) = z.val.arg := by
    dsimp only [t, a]
    field_simp
    ring
  rw [he]
  let c : Circle := ⟨z.val, mem_sphere_zero_iff_norm.mpr hn⟩
  exact congrArg (fun u : Circle => u.val) (Circle.exp_arg c)

/-- The square's bottom side is exactly the first circular quadrant. -/
theorem closedDiscSquareHomeomorph_bottom_inverse
    (z : Metric.closedBall (0 : ℂ) 1) (hv : (closedDiscSquareHomeomorph z).2 = 0) :
    ‖z.val‖ = 1 ∧ 0 ≤ z.val.re ∧ 0 ≤ z.val.im := by
  have hxy : (discDiamondHomeomorph z.val).re + (discDiamondHomeomorph z.val).im = 1 := by
    have hh := congrArg Subtype.val hv
    change (1 - (discDiamondHomeomorph z.val).re - (discDiamondHomeomorph z.val).im) / 2 = 0 at hh
    linarith
  have hnorm : complexDiamondSeminorm (discDiamondHomeomorph z.val) ≤ 1 := by
    rw [discDiamondHomeomorph_gauge]
    exact mem_closedBall_zero_iff.mp z.property
  rw [complexDiamondSeminorm_apply] at hnorm
  have hxr := le_abs_self (discDiamondHomeomorph z.val).re
  have hxi := le_abs_self (discDiamondHomeomorph z.val).im
  have hnre := neg_le_abs (discDiamondHomeomorph z.val).re
  have hnim := neg_le_abs (discDiamondHomeomorph z.val).im
  have hfr : 0 ≤ (discDiamondHomeomorph z.val).re := by linarith
  have hfi : 0 ≤ (discDiamondHomeomorph z.val).im := by linarith
  have hn : ‖z.val‖ = 1 := by
    have hh := discDiamondHomeomorph_gauge z.val
    simpa only [complexDiamondSeminorm_apply, abs_of_nonneg hfr, abs_of_nonneg hfi, hxy] using hh.symm
  have hp : 0 < |z.val.re| + |z.val.im| :=
    (by rw [hn]; norm_num : 0 < ‖z.val‖).trans_le (Complex.norm_le_abs_re_add_abs_im z.val)
  have hs : 0 < ‖z.val‖ / (|z.val.re| + |z.val.im|) := div_pos (by rw [hn]; norm_num) hp
  rw [discDiamondHomeomorph_apply] at hfr hfi
  simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul] at hfr hfi
  exact ⟨hn, (mul_nonneg_iff_of_pos_left hs).mp hfr, (mul_nonneg_iff_of_pos_left hs).mp hfi⟩

theorem handleBoundaryPoint_second_quadrant
    (z : Metric.closedBall (0 : ℂ) 1) (hn : ‖z.val‖ = 1)
    (hr : z.val.re ≤ 0) (hi : 0 ≤ z.val.im) :
    ∃ t : unitInterval, handleBoundaryPoint ((1 + t.val) / 4) = z := by
  let a := z.val.arg
  have hz : z.val ≠ 0 := by intro h; simp [h] at hn
  have ha0 : Real.pi / 2 ≤ a := by
    by_contra hh
    have ht : z.val.arg < Real.pi / 2 := lt_of_not_ge hh
    rcases Complex.arg_lt_pi_div_two_iff.mp ht with he | he | he
    · linarith
    · linarith
    · exact hz he
  have ha1 : a ≤ Real.pi := Complex.arg_le_pi _
  have hpi : 0 < Real.pi / 2 := by positivity
  let t : unitInterval := ⟨(a - Real.pi / 2) / (Real.pi / 2),
    div_nonneg (sub_nonneg.mpr ha0) hpi.le, (div_le_one hpi).mpr (by linarith)⟩
  refine ⟨t, ?_⟩
  apply Subtype.ext
  change (Circle.exp (2 * Real.pi * ((1 + t.val) / 4)) : ℂ) = z.val
  have he : 2 * Real.pi * ((1 + t.val) / 4) = z.val.arg := by
    dsimp only [t, a]
    field_simp
    ring
  rw [he]
  let c : Circle := ⟨z.val, mem_sphere_zero_iff_norm.mpr hn⟩
  exact congrArg (fun u : Circle => u.val) (Circle.exp_arg c)

theorem handleBoundaryPoint_opposite_b (t : ℝ) :
    (handleBoundaryPoint ((4 - t) / 4)).val =
      Complex.I * star (handleBoundaryPoint ((1 + t) / 4)).val := by
  have he : 2 * Real.pi * ((4 - t) / 4) = 2 * Real.pi - Real.pi * t / 2 := by ring
  have hf : 2 * Real.pi * ((1 + t) / 4) = Real.pi / 2 + Real.pi * t / 2 := by ring
  apply Complex.ext <;> simp only [handleBoundaryPoint_re, handleBoundaryPoint_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  · rw [he, hf, Real.cos_sub, Real.sin_add]
    norm_num
  · rw [he, hf, Real.sin_sub, Real.cos_add]
    norm_num

theorem handleBoundaryPoint_first_side_signs (t : unitInterval) :
    0 ≤ (handleBoundaryPoint (t.val / 4)).val.re ∧
      0 ≤ (handleBoundaryPoint (t.val / 4)).val.im := by
  have h0 : 0 ≤ 2 * Real.pi * (t.val / 4) :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (div_nonneg t.property.1 (by norm_num))
  have h1 : 2 * Real.pi * (t.val / 4) ≤ Real.pi / 2 := by
    nlinarith [t.property.2, Real.pi_pos]
  rw [handleBoundaryPoint_re, handleBoundaryPoint_im]
  exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩,
    Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [Real.pi_pos]⟩⟩

theorem handleBoundaryPoint_second_side_signs (t : unitInterval) :
    (handleBoundaryPoint ((1 + t.val) / 4)).val.re ≤ 0 ∧
      0 ≤ (handleBoundaryPoint ((1 + t.val) / 4)).val.im := by
  have h0 : Real.pi / 2 ≤ 2 * Real.pi * ((1 + t.val) / 4) := by
    nlinarith [t.property.1, Real.pi_pos]
  have h1 : 2 * Real.pi * ((1 + t.val) / 4) ≤ Real.pi := by
    nlinarith [t.property.2, Real.pi_pos]
  rw [handleBoundaryPoint_re, handleBoundaryPoint_im]
  exact ⟨Real.cos_nonpos_of_pi_div_two_le_of_le h0 (by linarith [Real.pi_pos]),
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩⟩


abbrev SquareInterval : Type := Set.Icc (0 : ℝ) (0 + 1)
def squareIntervalZero : SquareInterval := ⟨0, ⟨le_rfl, by norm_num⟩⟩
def squareIntervalOne : SquareInterval := ⟨0 + 1, ⟨by norm_num, le_rfl⟩⟩

/-- The literal opposite-edge identifications of a closed square. -/
inductive SquareSideIdent : SquareInterval × SquareInterval → SquareInterval × SquareInterval → Prop
  | horizontal (v : SquareInterval) : SquareSideIdent (squareIntervalZero, v) (squareIntervalOne, v)
  | vertical (u : SquareInterval) : SquareSideIdent (u, squareIntervalZero) (u, squareIntervalOne)

abbrev UnitEndpointIdent : SquareInterval → SquareInterval → Prop := AddCircle.EndpointIdent (1 : ℝ) 0

def squareEndpointQuotientMap : Quot SquareSideIdent →
    Quot UnitEndpointIdent × Quot UnitEndpointIdent :=
  Quot.lift (fun z => (Quot.mk _ z.1, Quot.mk _ z.2)) (by
    intro z w h
    cases h with
    | horizontal v => exact Prod.ext (Quot.sound AddCircle.EndpointIdent.mk) rfl
    | vertical u => exact Prod.ext rfl (Quot.sound AddCircle.EndpointIdent.mk))

def squareEndpointQuotientInverse (q : Quot UnitEndpointIdent × Quot UnitEndpointIdent) :
    Quot SquareSideIdent :=
  Quot.lift (fun u : SquareInterval =>
    Quot.lift (fun v : SquareInterval => Quot.mk _ (u,v)) (by
      intro v w h
      cases h
      exact Quot.sound (_root_.LowDimensionalTopology.Geometry.Surfaces.SquareSideIdent.vertical u)) q.2) (by
    intro u w h
    cases h
    induction q.2 using Quot.inductionOn with
    | _ v => exact Quot.sound (_root_.LowDimensionalTopology.Geometry.Surfaces.SquareSideIdent.horizontal v)) q.1

/-- Both opposite edge identifications are exactly the product of the two endpoint quotients. -/
def squareEndpointQuotientEquiv : Quot SquareSideIdent ≃
    Quot UnitEndpointIdent × Quot UnitEndpointIdent where
  toFun := squareEndpointQuotientMap
  invFun := squareEndpointQuotientInverse
  left_inv q := by
    induction q using Quot.inductionOn with
    | _ z => rfl
  right_inv q := by
    rcases q with ⟨q,r⟩
    induction q using Quot.inductionOn with
    | _ u =>
      induction r using Quot.inductionOn with
      | _ v => rfl

/-- Opposite-edge gluing of the square yields the actual product of real circles. -/
def squareTorusQuotientHomeomorph : Quot SquareSideIdent ≃ₜ
    AddCircle (1 : ℝ) × AddCircle (1 : ℝ) := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let E := (AddCircle.homeoIccQuot (1 : ℝ) 0).symm
  let e : Quot SquareSideIdent ≃ AddCircle (1 : ℝ) × AddCircle (1 : ℝ) :=
    squareEndpointQuotientEquiv.trans (E.toEquiv.prodCongr E.toEquiv)
  have hq : Continuous squareEndpointQuotientMap := by
    apply continuous_quot_lift
    exact (continuous_quot_mk.comp continuous_fst).prodMk
      (continuous_quot_mk.comp continuous_snd)
  have hc : Continuous e := by
    change Continuous ((E.prodCongr E) ∘ squareEndpointQuotientMap)
    exact (E.prodCongr E).continuous.comp hq
  exact e.toHomeomorphOfContinuousClosed hc hc.isClosedMap

/-- The square's right side is exactly the second circular quadrant. -/
theorem closedDiscSquareHomeomorph_right_inverse
    (z : Metric.closedBall (0 : ℂ) 1) (hv : (closedDiscSquareHomeomorph z).1 = 1) :
    ‖z.val‖ = 1 ∧ z.val.re ≤ 0 ∧ 0 ≤ z.val.im := by
  have hxy : -(discDiamondHomeomorph z.val).re + (discDiamondHomeomorph z.val).im = 1 := by
    have hh := congrArg Subtype.val hv
    change (1 - (discDiamondHomeomorph z.val).re + (discDiamondHomeomorph z.val).im) / 2 = 1 at hh
    linarith
  have hnorm : complexDiamondSeminorm (discDiamondHomeomorph z.val) ≤ 1 := by
    rw [discDiamondHomeomorph_gauge]
    exact mem_closedBall_zero_iff.mp z.property
  rw [complexDiamondSeminorm_apply] at hnorm
  have hxr := le_abs_self (discDiamondHomeomorph z.val).re
  have hxi := le_abs_self (discDiamondHomeomorph z.val).im
  have hnre := neg_le_abs (discDiamondHomeomorph z.val).re
  have hnim := neg_le_abs (discDiamondHomeomorph z.val).im
  have hfr : (discDiamondHomeomorph z.val).re ≤ 0 := by linarith
  have hfi : 0 ≤ (discDiamondHomeomorph z.val).im := by linarith
  have hn : ‖z.val‖ = 1 := by
    have hh := discDiamondHomeomorph_gauge z.val
    simpa only [complexDiamondSeminorm_apply, abs_of_nonpos hfr, abs_of_nonneg hfi, hxy] using hh.symm
  have hp : 0 < |z.val.re| + |z.val.im| :=
    (by rw [hn]; norm_num : 0 < ‖z.val‖).trans_le (Complex.norm_le_abs_re_add_abs_im z.val)
  have hs : 0 < ‖z.val‖ / (|z.val.re| + |z.val.im|) := div_pos (by rw [hn]; norm_num) hp
  rw [discDiamondHomeomorph_apply] at hfr hfi
  simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul] at hfr hfi
  exact ⟨hn, le_of_not_gt (fun h => not_lt_of_ge hfr (mul_pos hs h)), (mul_nonneg_iff_of_pos_left hs).mp hfi⟩

/-- The same explicit disc-to-square homeomorphism with the exact endpoint-quotient carrier. -/
def closedDiscCanonicalSquareHomeomorph : Metric.closedBall (0 : ℂ) 1 ≃ₜ
    SquareInterval × SquareInterval :=
  closedDiscSquareHomeomorph.trans
    ((Homeomorph.setCongr (show Set.Icc (0 : ℝ) 1 = Set.Icc 0 (0 + 1) by rw [zero_add])).prodCongr
      (Homeomorph.setCongr (show Set.Icc (0 : ℝ) 1 = Set.Icc 0 (0 + 1) by rw [zero_add])))

/-- The actual oriented edge pairing of the circular 4g-gon model.
The g=0 sphere is represented separately; no empty polygon is called a sphere. -/
inductive CanonicalHandleIdent (g : ℕ) :
    Metric.closedBall (0 : ℂ) 1 → Metric.closedBall (0 : ℂ) 1 → Prop
  | a (t : unitInterval) (i : Fin g) : CanonicalHandleIdent g
      (handleBoundaryPoint ((4 * (i.val : ℝ) + t.val) / (4 * (g : ℝ))))
      (handleBoundaryPoint ((4 * (i.val : ℝ) + 3 - t.val) / (4 * (g : ℝ))))
  | b (t : unitInterval) (i : Fin g) : CanonicalHandleIdent g
      (handleBoundaryPoint ((4 * (i.val : ℝ) + 1 + t.val) / (4 * (g : ℝ))))
      (handleBoundaryPoint ((4 * (i.val : ℝ) + 4 - t.val) / (4 * (g : ℝ))))

/-- The first circular edge pairing is the literal horizontal-edge square gluing. -/
theorem handle_one_a_to_square (t : unitInterval) :
    SquareSideIdent
      (closedDiscCanonicalSquareHomeomorph (handleBoundaryPoint (t.val / 4)))
      (closedDiscCanonicalSquareHomeomorph (handleBoundaryPoint ((3 - t.val) / 4))) := by
  let z := handleBoundaryPoint (t.val / 4)
  let w := handleBoundaryPoint ((3 - t.val) / 4)
  have he : w = closedDiscOppositeA z := Subtype.ext (handleBoundaryPoint_opposite_a t.val)
  have h := closedDiscSquareHomeomorph_opposite_a z (handleBoundaryPoint_norm _)
    (handleBoundaryPoint_first_side_signs t).1 (handleBoundaryPoint_first_side_signs t).2
  rw [← he] at h
  have h0 : (closedDiscCanonicalSquareHomeomorph z).2 = squareIntervalZero :=
    Subtype.ext (congrArg (fun u : unitInterval => u.val) h.1)
  have hx : (closedDiscCanonicalSquareHomeomorph w).1 =
      (closedDiscCanonicalSquareHomeomorph z).1 :=
    Subtype.ext (congrArg (fun u : unitInterval => u.val) h.2.1)
  have h1 : (closedDiscCanonicalSquareHomeomorph w).2 = squareIntervalOne := by
    apply Subtype.ext
    have hv := congrArg (fun u : unitInterval => u.val) h.2.2
    change (closedDiscSquareHomeomorph w).2.val = (1 : ℝ) at hv
    change (closedDiscSquareHomeomorph w).2.val = 0 + 1
    rw [zero_add]
    exact hv
  have hz : closedDiscCanonicalSquareHomeomorph z =
      ((closedDiscCanonicalSquareHomeomorph z).1, squareIntervalZero) := Prod.ext rfl h0
  have hw : closedDiscCanonicalSquareHomeomorph w =
      ((closedDiscCanonicalSquareHomeomorph z).1, squareIntervalOne) := Prod.ext hx h1
  change SquareSideIdent (closedDiscCanonicalSquareHomeomorph z) (closedDiscCanonicalSquareHomeomorph w)
  rw [hz, hw]
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.SquareSideIdent.vertical _

/-- The second circular edge pairing is the reverse literal vertical-edge square gluing. -/
theorem handle_one_b_to_square (t : unitInterval) :
    SquareSideIdent
      (closedDiscCanonicalSquareHomeomorph (handleBoundaryPoint ((4 - t.val) / 4)))
      (closedDiscCanonicalSquareHomeomorph (handleBoundaryPoint ((1 + t.val) / 4))) := by
  let z := handleBoundaryPoint ((1 + t.val) / 4)
  let w := handleBoundaryPoint ((4 - t.val) / 4)
  have he : w = closedDiscOppositeB z := Subtype.ext (handleBoundaryPoint_opposite_b t.val)
  have h := closedDiscSquareHomeomorph_opposite_b z (handleBoundaryPoint_norm _)
    (handleBoundaryPoint_second_side_signs t).1 (handleBoundaryPoint_second_side_signs t).2
  rw [← he] at h
  have h1 : (closedDiscCanonicalSquareHomeomorph z).1 = squareIntervalOne := by
    apply Subtype.ext
    have hv := congrArg (fun u : unitInterval => u.val) h.1
    change (closedDiscSquareHomeomorph z).1.val = (1 : ℝ) at hv
    change (closedDiscSquareHomeomorph z).1.val = 0 + 1
    rw [zero_add]
    exact hv
  have h0 : (closedDiscCanonicalSquareHomeomorph w).1 = squareIntervalZero :=
    Subtype.ext (congrArg (fun u : unitInterval => u.val) h.2.1)
  have hy : (closedDiscCanonicalSquareHomeomorph w).2 =
      (closedDiscCanonicalSquareHomeomorph z).2 :=
    Subtype.ext (congrArg (fun u : unitInterval => u.val) h.2.2)
  have hz : closedDiscCanonicalSquareHomeomorph z =
      (squareIntervalOne, (closedDiscCanonicalSquareHomeomorph z).2) := Prod.ext h1 rfl
  have hw : closedDiscCanonicalSquareHomeomorph w =
      (squareIntervalZero, (closedDiscCanonicalSquareHomeomorph z).2) := Prod.ext h0 hy
  change SquareSideIdent (closedDiscCanonicalSquareHomeomorph w) (closedDiscCanonicalSquareHomeomorph z)
  rw [hw, hz]
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.SquareSideIdent.horizontal _

/-- Every true canonical one-handle generator maps into the square's generated edge relation. -/
theorem canonicalHandle_one_to_square {z w : Metric.closedBall (0 : ℂ) 1}
    (h : CanonicalHandleIdent 1 z w) :
    Relation.EqvGen SquareSideIdent
      (closedDiscCanonicalSquareHomeomorph z) (closedDiscCanonicalSquareHomeomorph w) := by
  cases h with
  | a t i =>
    fin_cases i
    simpa only [Fin.val_zero, Nat.cast_one, Nat.cast_zero, mul_zero, zero_add, mul_one] using
      Relation.EqvGen.rel _ _ (handle_one_a_to_square t)
  | b t i =>
    fin_cases i
    simpa only [Fin.val_zero, Nat.cast_one, Nat.cast_zero, mul_zero, zero_add, mul_one] using
      Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (handle_one_b_to_square t))

theorem canonicalHandle_one_a_of_quadrant
    (z : Metric.closedBall (0 : ℂ) 1) (hn : ‖z.val‖ = 1)
    (hr : 0 ≤ z.val.re) (hi : 0 ≤ z.val.im) :
    CanonicalHandleIdent 1 z (closedDiscOppositeA z) := by
  obtain ⟨t, ht⟩ := handleBoundaryPoint_first_quadrant z hn hr hi
  have h : CanonicalHandleIdent 1 (handleBoundaryPoint (t.val / 4))
      (handleBoundaryPoint ((3 - t.val) / 4)) := by
    simpa only [Fin.val_zero, Nat.cast_one, Nat.cast_zero, mul_zero, zero_add, mul_one] using
      _root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent.a (g := 1) t (0 : Fin 1)
  have he : handleBoundaryPoint ((3 - t.val) / 4) = closedDiscOppositeA z := by
    apply Subtype.ext
    rw [handleBoundaryPoint_opposite_a, ht]
    rfl
  rw [ht, he] at h
  exact h

theorem canonicalHandle_one_b_of_quadrant
    (z : Metric.closedBall (0 : ℂ) 1) (hn : ‖z.val‖ = 1)
    (hr : z.val.re ≤ 0) (hi : 0 ≤ z.val.im) :
    CanonicalHandleIdent 1 z (closedDiscOppositeB z) := by
  obtain ⟨t, ht⟩ := handleBoundaryPoint_second_quadrant z hn hr hi
  have h : CanonicalHandleIdent 1 (handleBoundaryPoint ((1 + t.val) / 4))
      (handleBoundaryPoint ((4 - t.val) / 4)) := by
    simpa only [Fin.val_zero, Nat.cast_one, Nat.cast_zero, mul_zero, zero_add, mul_one] using
      _root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent.b (g := 1) t (0 : Fin 1)
  have he : handleBoundaryPoint ((4 - t.val) / 4) = closedDiscOppositeB z := by
    apply Subtype.ext
    rw [handleBoundaryPoint_opposite_b, ht]
    rfl
  rw [ht, he] at h
  exact h

/-- Each opposite square edge pair lifts to exactly the first true circular side pairing. -/
theorem square_vertical_to_canonicalHandle_one (u : SquareInterval) :
    CanonicalHandleIdent 1
      (closedDiscCanonicalSquareHomeomorph.symm (u, squareIntervalZero))
      (closedDiscCanonicalSquareHomeomorph.symm (u, squareIntervalOne)) := by
  let z := closedDiscCanonicalSquareHomeomorph.symm (u, squareIntervalZero)
  have hEz : closedDiscCanonicalSquareHomeomorph z = (u, squareIntervalZero) :=
    closedDiscCanonicalSquareHomeomorph.apply_symm_apply _
  have hv : (closedDiscSquareHomeomorph z).2 = 0 := by
    apply Subtype.ext
    exact congrArg (fun w : SquareInterval × SquareInterval => w.2.val) hEz
  obtain ⟨hn, hr, hi⟩ := closedDiscSquareHomeomorph_bottom_inverse z hv
  have h := canonicalHandle_one_a_of_quadrant z hn hr hi
  have hcoord := closedDiscSquareHomeomorph_opposite_a z hn hr hi
  have he : closedDiscOppositeA z =
      closedDiscCanonicalSquareHomeomorph.symm (u, squareIntervalOne) := by
    apply closedDiscCanonicalSquareHomeomorph.injective
    rw [closedDiscCanonicalSquareHomeomorph.apply_symm_apply]
    apply Prod.ext
    · have hh : (closedDiscCanonicalSquareHomeomorph (closedDiscOppositeA z)).1 =
          (closedDiscCanonicalSquareHomeomorph z).1 :=
        Subtype.ext (congrArg (fun v : unitInterval => v.val) hcoord.2.1)
      have hu := congrArg (fun v : SquareInterval × SquareInterval => v.1) hEz
      change (closedDiscCanonicalSquareHomeomorph z).1 = u at hu
      exact hh.trans hu
    · apply Subtype.ext
      have hh := congrArg (fun v : unitInterval => v.val) hcoord.2.2
      change (closedDiscSquareHomeomorph (closedDiscOppositeA z)).2.val = (1 : ℝ) at hh
      change (closedDiscSquareHomeomorph (closedDiscOppositeA z)).2.val = 0 + 1
      rw [zero_add]
      exact hh
  rw [he] at h
  exact h

/-- The other square edge pair lifts to the reversed second circular side pairing. -/
theorem square_horizontal_to_canonicalHandle_one (u : SquareInterval) :
    CanonicalHandleIdent 1
      (closedDiscCanonicalSquareHomeomorph.symm (squareIntervalOne, u))
      (closedDiscCanonicalSquareHomeomorph.symm (squareIntervalZero, u)) := by
  let z := closedDiscCanonicalSquareHomeomorph.symm (squareIntervalOne, u)
  have hEz : closedDiscCanonicalSquareHomeomorph z = (squareIntervalOne, u) :=
    closedDiscCanonicalSquareHomeomorph.apply_symm_apply _
  have hv : (closedDiscSquareHomeomorph z).1 = 1 := by
    apply Subtype.ext
    have hh := congrArg (fun w : SquareInterval × SquareInterval => w.1.val) hEz
    change (closedDiscSquareHomeomorph z).1.val = (1 : ℝ)
    change (closedDiscSquareHomeomorph z).1.val = (0 + 1 : ℝ) at hh
    rw [zero_add] at hh
    exact hh
  obtain ⟨hn, hr, hi⟩ := closedDiscSquareHomeomorph_right_inverse z hv
  have h := canonicalHandle_one_b_of_quadrant z hn hr hi
  have hcoord := closedDiscSquareHomeomorph_opposite_b z hn hr hi
  have he : closedDiscOppositeB z =
      closedDiscCanonicalSquareHomeomorph.symm (squareIntervalZero, u) := by
    apply closedDiscCanonicalSquareHomeomorph.injective
    rw [closedDiscCanonicalSquareHomeomorph.apply_symm_apply]
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun v : unitInterval => v.val) hcoord.2.1)
    · have hh : (closedDiscCanonicalSquareHomeomorph (closedDiscOppositeB z)).2 =
          (closedDiscCanonicalSquareHomeomorph z).2 :=
        Subtype.ext (congrArg (fun v : unitInterval => v.val) hcoord.2.2)
      have hu := congrArg (fun v : SquareInterval × SquareInterval => v.2) hEz
      change (closedDiscCanonicalSquareHomeomorph z).2 = u at hu
      exact hh.trans hu
  rw [he] at h
  exact h

/-- Every square generator lifts into the actual canonical handle equivalence relation. -/
theorem square_to_canonicalHandle_one {z w : SquareInterval × SquareInterval}
    (h : SquareSideIdent z w) :
    Relation.EqvGen (CanonicalHandleIdent 1)
      (closedDiscCanonicalSquareHomeomorph.symm z) (closedDiscCanonicalSquareHomeomorph.symm w) := by
  cases h with
  | horizontal u =>
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (square_horizontal_to_canonicalHandle_one u))
  | vertical u =>
      exact Relation.EqvGen.rel _ _ (square_vertical_to_canonicalHandle_one u)

/-- The canonical circular one-handle quotient and the literal square edge quotient are truly homeomorphic. -/
def canonicalHandleOneSquareHomeomorph : Quot (CanonicalHandleIdent 1) ≃ₜ Quot SquareSideIdent where
  toFun := Quot.lift (fun z => Quot.mk _ (closedDiscCanonicalSquareHomeomorph z))
    (fun _ _ h => Quot.eqvGen_sound (canonicalHandle_one_to_square h))
  invFun := Quot.lift (fun z => Quot.mk _ (closedDiscCanonicalSquareHomeomorph.symm z))
    (fun _ _ h => Quot.eqvGen_sound (square_to_canonicalHandle_one h))
  left_inv q := by
    induction q using Quot.inductionOn with
    | _ z => exact congrArg (Quot.mk _) (closedDiscCanonicalSquareHomeomorph.symm_apply_apply z)
  right_inv q := by
    induction q using Quot.inductionOn with
    | _ z => exact congrArg (Quot.mk _) (closedDiscCanonicalSquareHomeomorph.apply_symm_apply z)
  continuous_toFun := continuous_quot_lift _
    (continuous_quot_mk.comp closedDiscCanonicalSquareHomeomorph.continuous)
  continuous_invFun := continuous_quot_lift _
    (continuous_quot_mk.comp closedDiscCanonicalSquareHomeomorph.symm.continuous)

/-- The canonical oriented circular four-edge one-handle surface is the actual two-torus. -/
def canonicalHandleOneTorusHomeomorph : Quot (CanonicalHandleIdent 1) ≃ₜ
    AddCircle (1 : ℝ) × AddCircle (1 : ℝ) :=
  canonicalHandleOneSquareHomeomorph.trans squareTorusQuotientHomeomorph

/-- Standard closed oriented handle models: the zero-handle sphere is separate from nonempty polygons. -/
def CanonicalHandleSurface : ℕ → Type
  | 0 => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  | g + 1 => Quot (CanonicalHandleIdent (g + 1))

instance canonicalHandleSurfaceTopology (g : ℕ) : TopologicalSpace (CanonicalHandleSurface g) := by
  cases g <;> dsimp only [CanonicalHandleSurface] <;> infer_instance

def canonicalHandleSurfaceZeroHomeomorph : CanonicalHandleSurface 0 ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := Homeomorph.refl _

def canonicalHandleSurfaceOneHomeomorph : CanonicalHandleSurface 1 ≃ₜ
    AddCircle (1 : ℝ) × AddCircle (1 : ℝ) := canonicalHandleOneTorusHomeomorph

/-- A topological genus witness uses the actual closed handle surface, not the analytic form dimension. -/
def HasTopologicalGenus (X : Type*) [TopologicalSpace X] (g : ℕ) : Prop :=
  Nonempty (X ≃ₜ CanonicalHandleSurface g)

theorem hasTopologicalGenus_zero_iff {X : Type*} [TopologicalSpace X] :
    HasTopologicalGenus X 0 ↔ Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨fun ⟨e⟩ => ⟨e.trans canonicalHandleSurfaceZeroHomeomorph⟩,
    fun ⟨e⟩ => ⟨e.trans canonicalHandleSurfaceZeroHomeomorph.symm⟩⟩

theorem hasTopologicalGenus_one_iff {X : Type*} [TopologicalSpace X] :
    HasTopologicalGenus X 1 ↔ Nonempty (X ≃ₜ AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
  ⟨fun ⟨e⟩ => ⟨e.trans canonicalHandleSurfaceOneHomeomorph⟩,
    fun ⟨e⟩ => ⟨e.trans canonicalHandleSurfaceOneHomeomorph.symm⟩⟩

/-- The sphere alternative of the genuine universal cover is precisely the actual zero-handle model. -/
theorem RiemannUniversalCover.sphere_model_iff_topologicalGenus_zero
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X} (C : RiemannUniversalCover R) :
    @RiemannConformallyEquivalent C.space (OnePoint ℂ) C.topology _ C.surface
      sphereRiemannSurface ↔ HasTopologicalGenus X 0 := by
  rw [C.sphere_model_iff_homeomorphic_sphere, hasTopologicalGenus_zero_iff]
  let E : OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])
  exact ⟨fun ⟨e⟩ => ⟨e.trans E⟩, fun ⟨e⟩ => ⟨e.trans E.symm⟩⟩

/-- For compact bases, the genuine plane-cover alternative is precisely the true one-handle model. -/
theorem RiemannUniversalCover.plane_model_iff_topologicalGenus_one
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {R : RiemannSurface X} (C : RiemannUniversalCover R) :
    @RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface
      complexPlaneRiemannSurface ↔ HasTopologicalGenus X 1 := by
  rw [C.plane_model_iff_homeomorphic_torus, hasTopologicalGenus_one_iff]

end LowDimensionalTopology.Geometry.Surfaces
