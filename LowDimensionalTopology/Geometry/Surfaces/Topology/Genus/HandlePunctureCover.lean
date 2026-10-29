module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleBoundary
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# An actual puncture cover of the canonical handle quotient

The center-complement and a genuine interior disc form an open cover of the
original quotient topology. The disc and the intersection are identified with
an ordinary complex ball and punctured ball. Polar coordinates then give the
intersection an explicit circle homotopy equivalence.
-/

@[expose] public section
noncomputable section

open Set Metric ContinuousMap

namespace LowDimensionalTopology.Geometry.Surfaces.HandlePuncture

open HandlePresentation

def smallDisc (g : ℕ) (r : ℝ) : Set (PolygonQuotient g) :=
  projection g '' {z : Disc | ‖z.val‖ < r}

def overlap (g : ℕ) (r : ℝ) : Set (PolygonQuotient g) := punctured g ∩ smallDisc g r

abbrev PuncturedBall (r : ℝ) := {z : ℂ // z ≠ 0 ∧ ‖z‖ < r}

theorem preimage_smallDisc (g : ℕ) {r : ℝ} (hr : r ≤ 1) :
    projection g ⁻¹' smallDisc g r = {z : Disc | ‖z.val‖ < r} := by
  ext z
  constructor
  · rintro ⟨w, hw, he⟩
    have hzw : z = w := HandleCW.quotient_interior_fiber_singleton
      (hw.trans_le hr) he.symm
    simpa only [hzw] using hw
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem isOpen_smallDisc (g : ℕ) {r : ℝ} (hr : r ≤ 1) :
    IsOpen (smallDisc g r) := by
  apply (isQuotientMap_quot_mk (r := CanonicalHandleIdent g)).isOpen_preimage.mp
  change IsOpen (projection g ⁻¹' smallDisc g r)
  rw [preimage_smallDisc g hr]
  exact isOpen_lt continuous_subtype_val.norm continuous_const

theorem center_mem_smallDisc (g : ℕ) {r : ℝ} (hr : 0 < r) :
    center g ∈ smallDisc g r :=
  ⟨zeroDisc, by
    change ‖(0 : ℂ)‖ < r
    simpa only [norm_zero] using hr, rfl⟩

theorem punctured_union_smallDisc (g : ℕ) {r : ℝ} (hr : 0 < r) :
    punctured g ∪ smallDisc g r = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x = center g
  · right
    simpa only [hx] using center_mem_smallDisc g hr
  · left
    exact hx

theorem open_cover (g : ℕ) {r : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    IsOpen (punctured g) ∧ IsOpen (smallDisc g r) ∧
      punctured g ∪ smallDisc g r = univ :=
  ⟨punctured_open g, isOpen_smallDisc g hr₁, punctured_union_smallDisc g hr₀⟩

theorem out_norm_lt_of_mem_smallDisc (g : ℕ) {r : ℝ} (hr : r ≤ 1)
    {x : PolygonQuotient g} (hx : x ∈ smallDisc g r) : ‖x.out.val‖ < r := by
  rcases hx with ⟨z, hz, rfl⟩
  have hout : (projection g z).out = z :=
    HandleCW.quotient_out_projection_interior (g := g) (z := z) (hz.trans_le hr)
  rw [hout]
  exact hz

theorem continuous_out_smallDisc (g : ℕ) {r : ℝ} (hr : r ≤ 1) :
    Continuous (fun x : smallDisc g r => x.val.out) := by
  change Continuous ((smallDisc g r).domRestrict (fun x : PolygonQuotient g => x.out))
  apply ContinuousOn.domRestrict
  apply (HandleCW.quotient_out_continuousOn_interior g).mono
  rintro x ⟨z, hz, rfl⟩
  exact ⟨z, hz.trans_le hr, rfl⟩

def ballToDisc {r : ℝ} (hr : r ≤ 1) (z : ball (0 : ℂ) r) : Disc :=
  ⟨z.val, mem_closedBall_zero_iff.mpr
    ((mem_ball_zero_iff.mp z.property).le.trans hr)⟩

def smallDiscHomeomorphBall (g : ℕ) {r : ℝ} (hr : r ≤ 1) :
    smallDisc g r ≃ₜ ball (0 : ℂ) r where
  toFun x := ⟨x.val.out.val,
    mem_ball_zero_iff.mpr (out_norm_lt_of_mem_smallDisc g hr x.property)⟩
  invFun z := ⟨projection g (ballToDisc hr z),
    ⟨ballToDisc hr z, mem_ball_zero_iff.mp z.property, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact Quot.out_eq x.val
  right_inv z := by
    apply Subtype.ext
    change (projection g (ballToDisc hr z)).out.val = z.val
    exact congrArg Subtype.val
      (HandleCW.quotient_out_projection_interior (g := g) (z := ballToDisc hr z)
        ((mem_ball_zero_iff.mp z.property).trans_le hr))
  continuous_toFun :=
    (continuous_subtype_val.comp (continuous_out_smallDisc g hr)).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_quot_mk.comp (continuous_subtype_val.subtype_mk _)

theorem contractible_smallDisc (g : ℕ) {r : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    ContractibleSpace (smallDisc g r) := by
  let : ContractibleSpace (ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).contractibleSpace ⟨0, mem_ball_self hr₀⟩
  exact (smallDiscHomeomorphBall g hr₁).contractibleSpace

theorem out_ne_zero_of_mem_punctured (g : ℕ) {x : PolygonQuotient g}
    (hx : x ∈ punctured g) : x.out.val ≠ 0 := by
  intro hz
  have hzero : x.out = zeroDisc := Subtype.ext hz
  apply hx
  calc
    x = projection g x.out := (Quot.out_eq x).symm
    _ = center g := congrArg (projection g) hzero

def overlapHomeomorphPuncturedBall (g : ℕ) {r : ℝ} (hr : r ≤ 1) :
    overlap g r ≃ₜ PuncturedBall r where
  toFun x := ⟨x.val.out.val,
    out_ne_zero_of_mem_punctured g x.property.1,
    out_norm_lt_of_mem_smallDisc g hr x.property.2⟩
  invFun z :=
    let w : Disc := ⟨z.val, mem_closedBall_zero_iff.mpr (z.property.2.le.trans hr)⟩
    ⟨projection g w,
      (by
        refine ⟨?_, ⟨w, z.property.2, rfl⟩⟩
        intro he
        exact z.property.1 (congrArg Subtype.val (projection_eq_center_iff.mp he)))⟩
  left_inv x := by
    apply Subtype.ext
    exact Quot.out_eq x.val
  right_inv z := by
    apply Subtype.ext
    let w : Disc := ⟨z.val, mem_closedBall_zero_iff.mpr (z.property.2.le.trans hr)⟩
    change (projection g w).out.val = z.val
    exact congrArg Subtype.val
      (HandleCW.quotient_out_projection_interior (g := g) (z := w)
        (z.property.2.trans_le hr))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      ((continuous_out_smallDisc g hr).comp
        (continuous_subtype_val.subtype_mk (fun x => x.property.2)))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_quot_mk.comp (continuous_subtype_val.subtype_mk _)

/-- Polar coordinates on the actual punctured ball, with its actual subspace topology. -/
def puncturedBallHomeomorphPolar (r : ℝ) :
    PuncturedBall r ≃ₜ (Circle × Ioo (0 : ℝ) r) where
  toFun z :=
    (⟨‖z.val‖⁻¹ • z.val, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr z.property.1)])⟩,
      ⟨‖z.val‖, norm_pos_iff.mpr z.property.1, z.property.2⟩)
  invFun w := ⟨w.2.val • (w.1 : ℂ),
    smul_ne_zero w.2.property.1.ne' (Circle.coe_ne_zero w.1), by
      simpa only [norm_smul, Real.norm_of_nonneg w.2.property.1.le,
        Circle.norm_coe, mul_one] using w.2.property.2⟩
  left_inv z := by
    apply Subtype.ext
    change ‖z.val‖ • (‖z.val‖⁻¹ • z.val) = z.val
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr z.property.1), one_smul]
  right_inv w := by
    apply Prod.ext
    · apply Circle.ext
      change ‖w.2.val • (w.1 : ℂ)‖⁻¹ • (w.2.val • (w.1 : ℂ)) = (w.1 : ℂ)
      rw [norm_smul, Real.norm_of_nonneg w.2.property.1.le, Circle.norm_coe,
        mul_one, smul_smul, inv_mul_cancel₀ w.2.property.1.ne', one_smul]
    · apply Subtype.ext
      change ‖w.2.val • (w.1 : ℂ)‖ = w.2.val
      rw [norm_smul, Real.norm_of_nonneg w.2.property.1.le, Circle.norm_coe, mul_one]
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_subtype_val.norm.inv₀
        (fun z => norm_ne_zero_iff.mpr z.property.1)).smul continuous_subtype_val)
    · exact continuous_subtype_val.norm.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)

theorem pathConnected_overlap (g : ℕ) {r ρ : ℝ} (hr : r ≤ 1)
    (hρ : ρ ∈ Ioo (0 : ℝ) r) : PathConnectedSpace (overlap g r) := by
  let : ContractibleSpace (Ioo (0 : ℝ) r) :=
    (convex_Ioo (0 : ℝ) r).contractibleSpace ⟨ρ, hρ⟩
  exact ((overlapHomeomorphPuncturedBall g hr).trans
    (puncturedBallHomeomorphPolar r)).symm.pathConnectedSpace

/-- The interval factor contracts at the prescribed radius, not at an unspecified point. -/
def radialIntervalHomotopyEquiv {r ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) r) :
    Ioo (0 : ℝ) r ≃ₕ Unit where
  toFun := ContinuousMap.const _ ()
  invFun := ContinuousMap.const _ ⟨ρ, hρ⟩
  left_inv := by
    refine ⟨{ toFun := fun p => ⟨p.1.val * p.2.val + (1 - p.1.val) * ρ, by
                exact (convex_Ioo (0 : ℝ) r) p.2.property hρ p.1.property.1
                  (sub_nonneg.mpr p.1.property.2) (by simp)⟩
              continuous_toFun := by
                apply Continuous.subtype_mk
                fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro x
      apply Subtype.ext
      simp
    · intro x
      apply Subtype.ext
      simp
  right_inv := by
    have he : (ContinuousMap.const (Ioo (0 : ℝ) r) ()).comp
        (ContinuousMap.const Unit (⟨ρ, hρ⟩ : Ioo (0 : ℝ) r)) =
        ContinuousMap.id Unit := ContinuousMap.ext (fun _ => Subsingleton.elim _ _)
    rw [he]

/-- The actual overlap has the homotopy type of the circle, with radius `ρ` chosen explicitly. -/
def overlapCircleHomotopyEquiv (g : ℕ) {r ρ : ℝ} (hr : r ≤ 1)
    (hρ : ρ ∈ Ioo (0 : ℝ) r) : overlap g r ≃ₕ Circle :=
  ((overlapHomeomorphPuncturedBall g hr).trans
    (puncturedBallHomeomorphPolar r)).toHomotopyEquiv |>.trans
      (((HomotopyEquiv.refl Circle).prodCongr (radialIntervalHomotopyEquiv hρ)).trans
        (Homeomorph.prodUnique Circle Unit).toHomotopyEquiv)

/-- The forward map is exactly radial normalization in the original complex disc. -/
theorem overlapCircleHomotopyEquiv_apply (g : ℕ) {r ρ : ℝ} (hr : r ≤ 1)
    (hρ : ρ ∈ Ioo (0 : ℝ) r) (x : overlap g r) :
    ((overlapCircleHomotopyEquiv g hr hρ x : Circle) : ℂ) =
      ‖x.val.out.val‖⁻¹ • x.val.out.val := rfl

/-- The inverse circle map is the literal radius-`ρ` circle in the actual quotient. -/
theorem overlapCircleHomotopyEquiv_symm_val (g : ℕ) {r ρ : ℝ} (hr : r ≤ 1)
    (hρ : ρ ∈ Ioo (0 : ℝ) r) (z : Circle) :
    ((overlapCircleHomotopyEquiv g hr hρ).symm z).val =
      projection g ⟨ρ • (z : ℂ), mem_closedBall_zero_iff.mpr (by
        rw [norm_smul, Real.norm_of_nonneg hρ.1.le, Circle.norm_coe, mul_one]
        exact hρ.2.le.trans hr)⟩ := rfl

end LowDimensionalTopology.Geometry.Surfaces.HandlePuncture
