/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.PolygonalQuotient
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
set_option maxHeartbeats 600000
namespace LowDimensionalTopology.Geometry.Surfaces.PolygonCellCollision
open LeanEval.Topology.ClassificationOfSurfaces

theorem side_clock_period {n : ℕ} (i j : Fin n) (t u : unitInterval)
    (heq : PolygonCell.side i t=PolygonCell.side j u) :
    ∃m : ℤ,(i.val : ℝ)+t.val=(j.val : ℝ)+u.val+(m : ℝ)*n := by
  have hn : (n : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt i.pos)
  have hpi : 2*Real.pi≠0 := by positivity
  have he : Circle.exp (PolygonCell.sideAngle i t)=Circle.exp (PolygonCell.sideAngle j u) := by
    apply Subtype.ext
    exact congrArg (fun z : PolygonCell n => (z : ℂ)) heq
  obtain ⟨m,hm⟩ := Circle.exp_eq_exp.mp he
  refine ⟨m,?_⟩
  have hh : (2*Real.pi)*(((i.val : ℝ)+t.val)/n)=
      (2*Real.pi)*(((j.val : ℝ)+u.val)/n+(m : ℝ)) := by
    dsimp [PolygonCell.sideAngle] at hm
    linear_combination hm
  have hd := mul_left_cancel₀ hpi hh
  field_simp [hn] at hd
  linarith only [hd]

theorem side_core_unique {n : ℕ} (i j : Fin n) (t u : unitInterval)
    (ht : 0< t.val ∧ t.val< 1) (heq : PolygonCell.side i t=PolygonCell.side j u) :
    i=j ∧ t=u := by
  obtain ⟨m,hm⟩ := side_clock_period i j t u heq
  have hn : 0< (n : ℝ) := by exact_mod_cast i.pos
  have hi : (i.val : ℝ)+1 ≤ n := by exact_mod_cast i.isLt
  have hj : (j.val : ℝ)+1 ≤ n := by exact_mod_cast j.isLt
  have hi0 : (0 : ℝ) ≤ i.val := by positivity
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  have hm0 : m=0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hneg|hpos
    · have hm' : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      have hh := mul_le_mul_of_nonneg_right hm' hn.le
      linarith only [hm,hi0,hj,ht.1,u.property.2,hh]
    · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      have hh := mul_le_mul_of_nonneg_right hm' hn.le
      linarith only [hm,hi,hj0,ht.2,u.property.1,hh]
  simp only [hm0,Int.cast_zero,zero_mul,add_zero] at hm
  have hij : i.val=j.val := by
    by_contra h
    rcases lt_or_gt_of_ne h with hlt|hgt
    · have hr : (i.val : ℝ)+1 ≤ j.val := by exact_mod_cast hlt
      linarith only [hm,hr,ht.2,u.property.1]
    · have hr : (j.val : ℝ)+1 ≤ i.val := by exact_mod_cast hgt
      linarith only [hm,hr,ht.1,u.property.2]
  refine ⟨Fin.ext hij,Subtype.ext ?_⟩
  rw [hij] at hm
  linarith only [hm]

theorem side_zero_injective {n : ℕ} : Function.Injective (fun i : Fin n => PolygonCell.side i 0) := by
  intro i j heq
  obtain ⟨m,hm⟩ := side_clock_period i j 0 0 heq
  change (i.val : ℝ)+0=(j.val : ℝ)+0+(m : ℝ)*n at hm
  have hn : 0< (n : ℝ) := by exact_mod_cast i.pos
  have hi : (i.val : ℝ)< n := by exact_mod_cast i.isLt
  have hj : (j.val : ℝ)< n := by exact_mod_cast j.isLt
  have hi0 : (0 : ℝ) ≤ i.val := by positivity
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  have hm0 : m=0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hneg|hpos
    · have hm' : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      have hh := mul_le_mul_of_nonneg_right hm' hn.le
      linarith only [hm,hi0,hj,hh]
    · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      have hh := mul_le_mul_of_nonneg_right hm' hn.le
      linarith only [hm,hi,hj0,hh]
  simp only [hm0,Int.cast_zero,zero_mul,add_zero] at hm
  exact Fin.ext (by exact_mod_cast hm)

theorem side_eq_iff {n : ℕ} (i j : Fin n) (t u : unitInterval) :
    PolygonCell.side i t=PolygonCell.side j u ↔
      (i=j ∧ t=u) ∨
      (t=1 ∧ u=0 ∧ j=finRotate n i) ∨
      (t=0 ∧ u=1 ∧ i=finRotate n j) := by
  constructor
  · intro h
    by_cases ht0 : t=0
    · subst t
      by_cases hu0 : u=0
      · subst u
        exact Or.inl ⟨side_zero_injective h,rfl⟩
      by_cases hu1 : u=1
      · subst u
        exact Or.inr (Or.inr ⟨rfl,rfl,side_zero_injective
          (h.trans (PolygonCell.side_one_eq_rotate_zero j))⟩)
      have hu : 0< u.val ∧ u.val< 1 := by
        refine ⟨lt_of_le_of_ne u.property.1 ?_,lt_of_le_of_ne u.property.2 ?_⟩
        · exact fun he => hu0 (Subtype.ext he.symm)
        · exact fun he => hu1 (Subtype.ext he)
      obtain ⟨_,htu⟩ := side_core_unique j i u 0 hu h.symm
      exact False.elim (hu0 htu)
    by_cases ht1 : t=1
    · subst t
      by_cases hu0 : u=0
      · subst u
        exact Or.inr (Or.inl ⟨rfl,rfl,side_zero_injective
          (h.symm.trans (PolygonCell.side_one_eq_rotate_zero i))⟩)
      by_cases hu1 : u=1
      · subst u
        apply Or.inl
        refine ⟨(finRotate n).injective (side_zero_injective ?_),rfl⟩
        exact (PolygonCell.side_one_eq_rotate_zero i).symm.trans
          (h.trans (PolygonCell.side_one_eq_rotate_zero j))
      have hu : 0< u.val ∧ u.val< 1 := by
        refine ⟨lt_of_le_of_ne u.property.1 ?_,lt_of_le_of_ne u.property.2 ?_⟩
        · exact fun he => hu0 (Subtype.ext he.symm)
        · exact fun he => hu1 (Subtype.ext he)
      obtain ⟨_,htu⟩ := side_core_unique j i u 1 hu h.symm
      exact False.elim (hu1 htu)
    have ht : 0< t.val ∧ t.val< 1 := by
      refine ⟨lt_of_le_of_ne t.property.1 ?_,lt_of_le_of_ne t.property.2 ?_⟩
      · exact fun he => ht0 (Subtype.ext he.symm)
      · exact fun he => ht1 (Subtype.ext he)
    exact Or.inl (side_core_unique i j t u ht h)
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
    · rfl
    · exact PolygonCell.side_one_eq_rotate_zero i
    · exact (PolygonCell.side_one_eq_rotate_zero j).symm
end LowDimensionalTopology.Geometry.Surfaces.PolygonCellCollision
