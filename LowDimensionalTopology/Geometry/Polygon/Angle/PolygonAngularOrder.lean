/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Polygon.Tangential.PolygonTangentialCoordinates
/-! # Actual cyclic tangential vertices and support inequalities

The strict source angle-sum condition yields distinct actual closed native vertices
and genuine cyclic support geodesics, with all nonincident inequalities strict.
The entire support-region boundary and actual Jordan polygon construction remain
separate unfinished geometric obligations.
-/

@[expose] public section
open Set
open scoped Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- Extend a finite list of angular increments by zero. -/
def polygonAngularIncrement {n : ℕ} (a : Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then a ⟨k,hk⟩ else 0

def polygonAngularPrefix {n : ℕ} (a : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k,polygonAngularIncrement a j

theorem polygonAngularPrefix_zero {n : ℕ} (a : Fin n → ℝ) : polygonAngularPrefix a 0 = 0 := by
  simp only [polygonAngularPrefix,Finset.range_zero,Finset.sum_empty]

theorem polygonAngularPrefix_succ {n : ℕ} (a : Fin n → ℝ) (k : ℕ) :
    polygonAngularPrefix a (k+1) = polygonAngularPrefix a k + polygonAngularIncrement a k := by
  exact Finset.sum_range_succ _ k

theorem polygonAngularPrefix_total {n : ℕ} (a : Fin n → ℝ) :
    polygonAngularPrefix a n = ∑ i,a i := by
  simp only [polygonAngularPrefix,polygonAngularIncrement,Finset.sum_fin_eq_sum_range]

theorem polygonAngularPrefix_monotone {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i,0 ≤ a i) :
    Monotone (polygonAngularPrefix a) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [polygonAngularPrefix_succ]
  apply le_add_of_nonneg_right
  unfold polygonAngularIncrement
  split_ifs <;> first | exact ha _ | exact le_rfl

theorem polygonAngularPrefix_strictMonoOn {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i,0 < a i) :
    StrictMonoOn (polygonAngularPrefix a) (Iic n) := by
  intro j hj k hk hjk
  have hjn : j < n := lt_of_lt_of_le hjk hk
  have hj1 : polygonAngularPrefix a j < polygonAngularPrefix a (j+1) := by
    rw [polygonAngularPrefix_succ,polygonAngularIncrement,dite_eq_left hjn]
    exact lt_add_of_pos_right _ (ha _)
  exact hj1.trans_le (polygonAngularPrefix_monotone a (fun i => (ha i).le) (by omega))

theorem polygonAngularPrefix_mem_Ico {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i,0 < a i) (i : Fin n) :
    polygonAngularPrefix a i ∈ Ico (0 : ℝ) (∑ j,a j) := by
  constructor
  · rw [← polygonAngularPrefix_zero a]
    exact polygonAngularPrefix_monotone a (fun j => (ha j).le) (Nat.zero_le _)
  · rw [← polygonAngularPrefix_total a]
    exact polygonAngularPrefix_strictMonoOn a ha (Nat.le_of_lt i.isLt) (show n ∈ Iic n from Nat.le_refl n) i.isLt

/-- The cosine is bounded by its endpoint value outside an open symmetric angular gap. -/
theorem polygon_cos_le_of_outside_gap {α t : ℝ} (hα0 : 0 ≤ α)
    (ht : t ∈ Icc α (2*Real.pi-α)) : Real.cos t ≤ Real.cos α := by
  by_cases htπ : t ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hα0 htπ ht.1
  · have hπt : Real.pi < t := lt_of_not_ge htπ
    rw [← Real.cos_two_pi_sub t]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hα0 (by linarith only [hπt]) (by linarith only [ht.2])

/-- Consecutive outward normals use the actual finite cumulative half-angle balance. -/
def polygonNormalAngle {n : ℕ} (θ : Fin n → ℝ) (d : ℝ) (k : ℕ) : ℝ :=
  2*polygonAngularPrefix (fun i => polygonTangentialHalfAngle (θ i) d) k

def polygonCornerNormalAngle {n : ℕ} (θ : Fin n → ℝ) (d : ℝ) (i : Fin n) : ℝ :=
  polygonNormalAngle θ d i + polygonTangentialHalfAngle (θ i) d

theorem polygonNormalAngle_zero {n : ℕ} (θ : Fin n → ℝ) (d : ℝ) : polygonNormalAngle θ d 0 = 0 := by
  rw [polygonNormalAngle,polygonAngularPrefix_zero,mul_zero]

theorem polygonNormalAngle_succ {n : ℕ} (θ : Fin n → ℝ) (d : ℝ) (i : Fin n) :
    polygonNormalAngle θ d (i+1) = polygonNormalAngle θ d i + 2*polygonTangentialHalfAngle (θ i) d := by
  unfold polygonNormalAngle
  rw [polygonAngularPrefix_succ,polygonAngularIncrement,dite_eq_left i.isLt]
  ring

theorem polygonNormalAngle_monotone {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) : Monotone (polygonNormalAngle θ d) := by
  intro j k hjk
  exact mul_le_mul_of_nonneg_left (polygonAngularPrefix_monotone _
    (fun i => (polygonTangentialHalfAngle_bounds (hθ i) hd).1.le) hjk) (by norm_num)

theorem polygonNormalAngle_strictMonoOn {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    StrictMonoOn (polygonNormalAngle θ d) (Iic n) := by
  intro j hj k hk hjk
  exact mul_lt_mul_of_pos_left (polygonAngularPrefix_strictMonoOn _
    (fun i => (polygonTangentialHalfAngle_bounds (hθ i) hd).1) hj hk hjk) (by norm_num)

theorem polygonNormalAngle_total {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hb : polygonAngleBalance θ d = Real.pi) : polygonNormalAngle θ d n = 2*Real.pi := by
  rw [polygonNormalAngle,polygonAngularPrefix_total]
  change 2*polygonAngleBalance θ d = _
  rw [hb]

theorem polygonNormalAngle_nonneg {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (k : ℕ) : 0 ≤ polygonNormalAngle θ d k := by
  have he := polygonNormalAngle_monotone θ d hθ hd (Nat.zero_le k)
  rwa [polygonNormalAngle_zero] at he

theorem polygonNormalAngle_le_total {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : polygonAngleBalance θ d = Real.pi)
    {k : ℕ} (hk : k ≤ n) : polygonNormalAngle θ d k ≤ 2*Real.pi := by
  rw [← polygonNormalAngle_total θ d hb]
  exact polygonNormalAngle_monotone θ d hθ hd hk

/-- Every constructed corner is on the inner side of every cyclic tangent support direction. -/
theorem polygonNormalAngle_cosine_bound {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : polygonAngleBalance θ d = Real.pi)
    (i j : Fin n) :
    Real.cos (polygonCornerNormalAngle θ d i-polygonNormalAngle θ d j) ≤
      Real.cos (polygonTangentialHalfAngle (θ i) d) := by
  dsimp only [polygonCornerNormalAngle]
  have hstep := polygonNormalAngle_succ θ d i
  have hi1 := polygonNormalAngle_le_total θ d hθ hd hb (show (i : ℕ)+1 ≤ n from i.isLt)
  have hj0 := polygonNormalAngle_nonneg θ d hθ hd j
  have hi0 := polygonNormalAngle_nonneg θ d hθ hd i
  have hj1 := polygonNormalAngle_le_total θ d hθ hd hb (Nat.le_of_lt j.isLt)
  have hα := polygonTangentialHalfAngle_bounds (hθ i) hd
  by_cases hji : (j : ℕ) ≤ i
  · have hle := polygonNormalAngle_monotone θ d hθ hd hji
    apply polygon_cos_le_of_outside_gap hα.1.le
    constructor <;> linarith only [hstep,hi1,hj0,hle]
  · have hij : (i : ℕ)+1 ≤ j := by omega
    have hle := polygonNormalAngle_monotone θ d hθ hd hij
    rw [show polygonNormalAngle θ d i + polygonTangentialHalfAngle (θ i) d - polygonNormalAngle θ d j =
      -(polygonNormalAngle θ d j - (polygonNormalAngle θ d i + polygonTangentialHalfAngle (θ i) d)) by ring,
      Real.cos_neg]
    apply polygon_cos_le_of_outside_gap hα.1.le
    constructor <;> linarith only [hstep,hj1,hi0,hle]

def polygonAngleUnit (t : ℝ) : ℂ := circleMap 0 1 t

theorem polygonAngleUnit_norm (t : ℝ) : ‖polygonAngleUnit t‖ = 1 := by
  simp only [polygonAngleUnit,norm_circleMap_zero,abs_one]

theorem polygonAngleUnit_re (t : ℝ) : (polygonAngleUnit t).re = Real.cos t := by
  simp only [polygonAngleUnit,circleMap_zero,Complex.ofReal_one,one_mul,Complex.exp_ofReal_mul_I_re]

theorem polygonAngleUnit_im (t : ℝ) : (polygonAngleUnit t).im = Real.sin t := by
  simp only [polygonAngleUnit,circleMap_zero,Complex.ofReal_one,one_mul,Complex.exp_ofReal_mul_I_im]

theorem polygonAngleUnit_inner (t u : ℝ) : inner ℝ (polygonAngleUnit t) (polygonAngleUnit u) = Real.cos (u-t) := by
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,polygonAngleUnit_re,polygonAngleUnit_re,
    polygonAngleUnit_im,polygonAngleUnit_im,Real.cos_sub]
  ring

theorem polygonAngleUnit_two_pi : polygonAngleUnit (2*Real.pi) = polygonAngleUnit 0 := by
  apply Complex.ext <;> simp only [polygonAngleUnit_re,polygonAngleUnit_im,Real.cos_two_pi,Real.sin_two_pi,Real.cos_zero,Real.sin_zero]

/-- Actual closed native vertices in their prescribed cyclic angular order. -/
def polygonOrderedTangentialVertex {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (i : Fin n) : 𝕔𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinHomeomorph.symm (Complex.UnitClosedDisc.mk
    (polygonTangentialVertexCoordinate (θ i) d • polygonAngleUnit (polygonCornerNormalAngle θ d i)) (by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (polygonTangentialVertexCoordinate_pos (hθ i) hd),
        polygonAngleUnit_norm,mul_one]
      exact polygonTangentialVertexCoordinate_le_one (hθ i) hd))

theorem polygonOrderedTangentialVertex_coordinate {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (polygonOrderedTangentialVertex θ d hθ hd
      i) =
      polygonTangentialVertexCoordinate (θ i) d • polygonAngleUnit (polygonCornerNormalAngle θ d i) :=
  congrArg (fun p : 𝕔𝔻 => (p :
    ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinHomeomorph.apply_symm_apply _)

/-- All true constructed vertices satisfy every actual cyclic tangent half-plane. -/
theorem polygonOrderedTangentialVertex_support_bound {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : polygonAngleBalance θ d = Real.pi)
    (i j : Fin n) :
    inner ℝ (polygonAngleUnit (polygonNormalAngle θ d j))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (polygonOrderedTangentialVertex θ d hθ hd i)) ≤ Real.tanh d := by
  rw [polygonOrderedTangentialVertex_coordinate,real_inner_smul_right,polygonAngleUnit_inner]
  calc
    _ ≤ polygonTangentialVertexCoordinate (θ i) d * Real.cos (polygonTangentialHalfAngle (θ i) d) :=
      mul_le_mul_of_nonneg_left (polygonNormalAngle_cosine_bound θ d hθ hd hb i j)
        (polygonTangentialVertexCoordinate_pos (hθ i) hd).le
    _ = Real.tanh d := by
      unfold polygonTangentialVertexCoordinate
      field_simp [(polygonTangentialHalfAngle_cos_pos (hθ i) hd).ne']

def polygonOrderedTangentialSupport {n : ℕ} (θ : Fin n → ℝ) (d : ℝ) (hd : 0 < d) (k :
  ℕ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine (polygonAngleUnit (polygonNormalAngle θ d
    k)) (Real.tanh d)
    (polygonAngleUnit_norm _) ⟨polygonTangential_tanh_pos hd,Real.tanh_lt_one d⟩

theorem polygonOrderedTangentialVertex_incoming {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (i : Fin n) :
    polygonOrderedTangentialVertex θ d hθ hd i ∈ (polygonOrderedTangentialSupport θ d hd i).closedCarrier := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_closed_equation_iff _ _ _ _ _).mpr
  rw [polygonOrderedTangentialVertex_coordinate,real_inner_smul_right,polygonAngleUnit_inner]
  simp only [polygonCornerNormalAngle,add_sub_cancel_left]
  unfold polygonTangentialVertexCoordinate
  field_simp [(polygonTangentialHalfAngle_cos_pos (hθ i) hd).ne']

theorem polygonOrderedTangentialVertex_outgoing {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (i : Fin n) :
    polygonOrderedTangentialVertex θ d hθ hd i ∈
      (polygonOrderedTangentialSupport θ d hd ((i : ℕ)+1)).closedCarrier := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_closed_equation_iff _ _ _ _ _).mpr
  rw [polygonOrderedTangentialVertex_coordinate,real_inner_smul_right,polygonAngleUnit_inner,
    polygonCornerNormalAngle,polygonNormalAngle_succ]
  rw [show polygonNormalAngle θ d i + polygonTangentialHalfAngle (θ i) d -
      (polygonNormalAngle θ d i + 2*polygonTangentialHalfAngle (θ i) d) =
      -polygonTangentialHalfAngle (θ i) d by ring,Real.cos_neg]
  unfold polygonTangentialVertexCoordinate
  field_simp [(polygonTangentialHalfAngle_cos_pos (hθ i) hd).ne']

theorem polygonOrderedTangentialSupport_closes {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hd : 0 < d) (hb : polygonAngleBalance θ d = Real.pi) :
    polygonOrderedTangentialSupport θ d hd n = polygonOrderedTangentialSupport θ d hd 0 := by
  simp only [polygonOrderedTangentialSupport,polygonNormalAngle_total θ d hb,
    polygonNormalAngle_zero,polygonAngleUnit_two_pi]

theorem polygonCornerNormalAngle_mem_Ioo {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : polygonAngleBalance θ d = Real.pi)
    (i : Fin n) : polygonCornerNormalAngle θ d i ∈ Ioo (0 : ℝ) (2*Real.pi) := by
  have hi0 := polygonNormalAngle_nonneg θ d hθ hd i
  have hi1 := polygonNormalAngle_le_total θ d hθ hd hb (show (i : ℕ)+1 ≤ n from i.isLt)
  have hs := polygonNormalAngle_succ θ d i
  have hα := (polygonTangentialHalfAngle_bounds (hθ i) hd).1
  constructor <;> dsimp only [polygonCornerNormalAngle] <;> linarith only [hi0,hi1,hs,hα]

theorem polygonCornerNormalAngle_strictMono {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) : StrictMono (polygonCornerNormalAngle θ d) := by
  intro i j hij
  have hαi := (polygonTangentialHalfAngle_bounds (hθ i) hd).1
  have hαj := (polygonTangentialHalfAngle_bounds (hθ j) hd).1
  have hstep := polygonNormalAngle_succ θ d i
  have hij' : (i : ℕ)+1 ≤ j := hij
  have hle := polygonNormalAngle_monotone θ d hθ hd hij'
  dsimp only [polygonCornerNormalAngle]
  linarith only [hαi,hαj,hstep,hle]

/-- All actual ordered vertices are distinct; no vertex distinctness is assumed. -/
theorem polygonOrderedTangentialVertex_injective {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : polygonAngleBalance θ d = Real.pi) :
    Function.Injective (polygonOrderedTangentialVertex θ d hθ hd) := by
  intro i j he
  have hK := congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate he
  rw [polygonOrderedTangentialVertex_coordinate,polygonOrderedTangentialVertex_coordinate] at hK
  have hN := congrArg norm hK
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (polygonTangentialVertexCoordinate_pos (hθ i) hd),
    abs_of_pos (polygonTangentialVertexCoordinate_pos (hθ j) hd),polygonAngleUnit_norm,mul_one] at hN
  rw [hN] at hK
  have hu : polygonAngleUnit (polygonCornerNormalAngle θ d i) = polygonAngleUnit (polygonCornerNormalAngle θ d j) := by
    change (polygonTangentialVertexCoordinate (θ j) d : ℂ) * polygonAngleUnit (polygonCornerNormalAngle θ d i) =
      (polygonTangentialVertexCoordinate (θ j) d : ℂ) * polygonAngleUnit (polygonCornerNormalAngle θ d j) at hK
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (polygonTangentialVertexCoordinate_pos (hθ j) hd).ne') hK
  have hi := polygonCornerNormalAngle_mem_Ioo θ d hθ hd hb i
  have hj := polygonCornerNormalAngle_mem_Ioo θ d hθ hd hb j
  have hβ : polygonCornerNormalAngle θ d i = polygonCornerNormalAngle θ d j :=
    injOn_circleMap_of_abs_sub_le' (by norm_num : (1 : ℝ) ≠ 0)
      (by linarith only : 2*Real.pi-0 ≤ 2*Real.pi) ⟨hi.1.le,hi.2⟩ ⟨hj.1.le,hj.2⟩ hu
  exact (polygonCornerNormalAngle_strictMono θ d hθ hd).injective hβ

theorem polygonOrderedTangentialVertex_ideal_iff {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (i : Fin n) :
    ‖(polygonOrderedTangentialVertex θ d hθ hd i : ℂ)‖ = 1 ↔ θ i = 0 := by
  rw [← norm_closedKleinCoordinate_eq_one_iff,polygonOrderedTangentialVertex_coordinate,norm_smul,
    Real.norm_eq_abs,abs_of_pos (polygonTangentialVertexCoordinate_pos (hθ i) hd),polygonAngleUnit_norm,mul_one,
    polygonTangentialVertexCoordinate_eq_one_iff (hθ i) hd]

/-- The true next vertex lies on the same actual outgoing support, including the cyclic wrap. -/
theorem polygonOrderedTangentialVertex_next_mem_support {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : polygonAngleBalance θ d = Real.pi)
    (i : Fin n) :
    polygonOrderedTangentialVertex θ d hθ hd (finRotate n i) ∈
      (polygonOrderedTangentialSupport θ d hd ((i : ℕ)+1)).closedCarrier := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  by_cases hi : i = Fin.last k
  · subst i
    rw [finRotate_last]
    change polygonOrderedTangentialVertex θ d hθ hd 0 ∈ (polygonOrderedTangentialSupport θ d hd (k+1)).closedCarrier
    rw [polygonOrderedTangentialSupport_closes θ d hd hb]
    exact polygonOrderedTangentialVertex_incoming θ d hθ hd 0
  · have he := polygonOrderedTangentialVertex_incoming θ d hθ hd (finRotate (k+1) i)
    rw [coe_finRotate_of_ne_last hi] at he
    exact he

/-- Each genuine cyclic closed side lies on its constructed genuine native tangent line. -/
theorem polygonOrderedTangentialEdge_subset_support {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : polygonAngleBalance θ d = Real.pi)
    (i : Fin n) :
    discPolygonEdge (polygonOrderedTangentialVertex θ d hθ hd) i ⊆
      (polygonOrderedTangentialSupport θ d hd ((i : ℕ)+1)).closedCarrier :=
  (polygonOrderedTangentialSupport θ d hd ((i : ℕ)+1)).closedCarrier_hConvex _
    (polygonOrderedTangentialVertex_outgoing θ d hθ hd i) _
    (polygonOrderedTangentialVertex_next_mem_support θ d hθ hd hb i)

theorem polygon_finRotate_val_of_succ_lt {n : ℕ} (i : Fin n) (hi : (i : ℕ)+1 < n) :
    (finRotate n i).val = (i : ℕ)+1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  have hn : i ≠ Fin.last k := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_last] at hv
    omega
  exact coe_finRotate_of_ne_last hn

theorem polygon_finRotate_val_of_last {n : ℕ} (i : Fin n) (hi : (i : ℕ)+1 = n) :
    (finRotate n i).val = 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  have he : i = Fin.last k := Fin.ext (by dsimp; omega)
  subst i
  rw [finRotate_last]
  rfl

theorem polygon_cos_lt_of_strict_outside_gap {α t : ℝ} (hα0 : 0 ≤ α)
    (ht : t ∈ Ioo α (2*Real.pi-α)) : Real.cos t < Real.cos α := by
  by_cases htπ : t ≤ Real.pi
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi hα0 htπ ht.1
  · have hπt : Real.pi < t := lt_of_not_ge htπ
    rw [← Real.cos_two_pi_sub t]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hα0 (by linarith only [hπt]) (by linarith only [ht.2])

theorem polygonNormalAngle_mem_Ico {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : polygonAngleBalance θ d = Real.pi)
    (i : Fin n) : polygonNormalAngle θ d i ∈ Ico (0 : ℝ) (2*Real.pi) := by
  refine ⟨polygonNormalAngle_nonneg θ d hθ hd i,?_⟩
  rw [← polygonNormalAngle_total θ d hb]
  exact polygonNormalAngle_strictMonoOn θ d hθ hd (Nat.le_of_lt i.isLt) (show n ∈ Iic n from Nat.le_refl n) i.isLt

/-- A corner belongs strictly to every nonincident support half-plane. -/
theorem polygonNormalAngle_cosine_strict {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : polygonAngleBalance θ d = Real.pi)
    (i k : Fin n) (hki : k ≠ i) (hknext : k ≠ finRotate n i) :
    Real.cos (polygonCornerNormalAngle θ d i-polygonNormalAngle θ d k) <
      Real.cos (polygonTangentialHalfAngle (θ i) d) := by
  dsimp only [polygonCornerNormalAngle]
  have hstep := polygonNormalAngle_succ θ d i
  have hi1 := polygonNormalAngle_le_total θ d hθ hd hb (show (i : ℕ)+1 ≤ n from i.isLt)
  have hk0 := polygonNormalAngle_nonneg θ d hθ hd k
  have hi0 := polygonNormalAngle_nonneg θ d hθ hd i
  have hk1 := (polygonNormalAngle_mem_Ico θ d hθ hd hb k).2
  have hα := polygonTangentialHalfAngle_bounds (hθ i) hd
  by_cases hle : (k : ℕ) ≤ i
  · have hlt : (k : ℕ) < i := by
      have hne : (k : ℕ) ≠ i := fun he => hki (Fin.ext he)
      omega
    have hnormlt := polygonNormalAngle_strictMonoOn θ d hθ hd (Nat.le_of_lt k.isLt)
      (Nat.le_of_lt i.isLt) hlt
    have hu : polygonNormalAngle θ d i + polygonTangentialHalfAngle (θ i) d - polygonNormalAngle θ d k <
        2*Real.pi-polygonTangentialHalfAngle (θ i) d := by
      by_cases hkzero : (k : ℕ) = 0
      · have hisucc : (i : ℕ)+1 < n := by
          by_contra! hnot
          have hilast : (i : ℕ)+1 = n := by omega
          have hrot := polygon_finRotate_val_of_last i hilast
          exact hknext (Fin.ext (hkzero.trans hrot.symm))
        have hinormlt := polygonNormalAngle_strictMonoOn θ d hθ hd (show (i : ℕ)+1 ∈ Iic n from Nat.le_of_lt hisucc)
          (show n ∈ Iic n from Nat.le_refl n) hisucc
        rw [polygonNormalAngle_total θ d hb] at hinormlt
        linarith only [hinormlt,hstep,hk0]
      · have hknormpos := polygonNormalAngle_strictMonoOn θ d hθ hd (show 0 ∈ Iic n from Nat.zero_le n)
          (Nat.le_of_lt k.isLt) (show 0 < (k : ℕ) from Nat.pos_of_ne_zero hkzero)
        rw [polygonNormalAngle_zero] at hknormpos
        linarith only [hi1,hstep,hknormpos]
    exact polygon_cos_lt_of_strict_outside_gap hα.1.le ⟨by linarith only [hnormlt],hu⟩
  · have hilt : (i : ℕ) < k := by omega
    have hisucc : (i : ℕ)+1 < n := by omega
    have hrot := polygon_finRotate_val_of_succ_lt i hisucc
    have hkne : (k : ℕ) ≠ (i : ℕ)+1 := fun he => hknext (Fin.ext (he.trans hrot.symm))
    have hisucclt : (i : ℕ)+1 < k := by omega
    have hnormlt := polygonNormalAngle_strictMonoOn θ d hθ hd (show (i : ℕ)+1 ∈ Iic n from Nat.le_of_lt hisucc)
      (Nat.le_of_lt k.isLt) hisucclt
    rw [show polygonNormalAngle θ d i + polygonTangentialHalfAngle (θ i) d - polygonNormalAngle θ d k =
      -(polygonNormalAngle θ d k - (polygonNormalAngle θ d i + polygonTangentialHalfAngle (θ i) d)) by ring,
      Real.cos_neg]
    apply polygon_cos_lt_of_strict_outside_gap hα.1.le
    constructor <;> linarith only [hstep,hnormlt,hk1,hi0]

theorem polygonOrderedTangentialVertex_support_strict {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : polygonAngleBalance θ d = Real.pi)
    (i k : Fin n) (hki : k ≠ i) (hknext : k ≠ finRotate n i) :
    inner ℝ (polygonAngleUnit (polygonNormalAngle θ d k))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (polygonOrderedTangentialVertex θ d hθ hd i)) < Real.tanh d := by
  rw [polygonOrderedTangentialVertex_coordinate,real_inner_smul_right,polygonAngleUnit_inner]
  calc
    _ < polygonTangentialVertexCoordinate (θ i) d * Real.cos (polygonTangentialHalfAngle (θ i) d) :=
      mul_lt_mul_of_pos_left (polygonNormalAngle_cosine_strict θ d hθ hd hb i k hki hknext)
        (polygonTangentialVertexCoordinate_pos (hθ i) hd)
    _ = Real.tanh d := by
      unfold polygonTangentialVertexCoordinate
      field_simp [(polygonTangentialHalfAngle_cos_pos (hθ i) hd).ne']

/-- The original angle-sum hypothesis yields actual distinct cyclic tangent vertices and true supports. -/
theorem exists_orderedTangentialConfiguration {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hsum : ∑ i,θ i < ((n : ℝ)-2)*Real.pi) :
    ∃ (d : ℝ) (hd : 0 < d),polygonAngleBalance θ d = Real.pi ∧
      Function.Injective (polygonOrderedTangentialVertex θ d hθ hd) ∧
      (∀ i,‖(polygonOrderedTangentialVertex θ d hθ hd i : ℂ)‖ = 1 ↔ θ i = 0) ∧
      (∀ (i j : Fin n),inner ℝ (polygonAngleUnit (polygonNormalAngle θ d j))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (polygonOrderedTangentialVertex θ d hθ
          hd i)) ≤ Real.tanh d) ∧
      (∀ i,discPolygonEdge (polygonOrderedTangentialVertex θ d hθ hd) i ⊆
        (polygonOrderedTangentialSupport θ d hd ((i : ℕ)+1)).closedCarrier) := by
  obtain ⟨d,hd,hb⟩ := polygonAngleBalance_exists_positive θ hθ hsum
  exact ⟨d,hd,hb,polygonOrderedTangentialVertex_injective θ d hθ hd hb,
    polygonOrderedTangentialVertex_ideal_iff θ d hθ hd,
    polygonOrderedTangentialVertex_support_bound θ d hθ hd hb,
    polygonOrderedTangentialEdge_subset_support θ d hθ hd hb⟩

end
end LowDimensionalTopology.Geometry.Polygon
