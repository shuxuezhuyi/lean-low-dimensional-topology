/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.SmallParabolicSignatures
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LowDimensionalTopology.Geometry.Fuchsian

theorem halfTurn_area_ratio_lower (p : ℕ) (hp : 2≤p) :
    (3:ℝ)/4≤(2*(p:ℝ)-1)/(2*(p:ℝ)) := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  apply (le_div_iff₀ (by positivity : 0<2*(p:ℝ))).mpr
  linarith

/-- The complete integer solutions of the first/last-term inequality. -/
theorem halfTurn_exceptional_integer_triples (l m p : ℕ)
    (hl : 2≤l) (hlm : l≤m) (hp : 2≤p)
    (hproper : (1:ℝ)/l+1/m<1)
    (harea : (2*(p:ℝ)-1)/(2*(p:ℝ))≤1/(l:ℝ)+1/(m:ℝ)) :
    (l,m,p)=(2,3,2) ∨ (l,m,p)=(2,3,3) ∨ (l,m,p)=(2,4,2) := by
  have hlow := le_trans (halfTurn_area_ratio_lower p hp) harea
  have hl2 : l=2 := by
    by_contra hn
    have hl3 : 3≤l := by omega
    have hm3 : 3≤m := le_trans hl3 hlm
    have hlR : (3:ℝ)≤l := by exact_mod_cast hl3
    have hmR : (3:ℝ)≤m := by exact_mod_cast hm3
    have hlB := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) hlR
    have hmB := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) hmR
    linarith
  have hm3 : 3≤m := by
    have hm2 : 2≤m := le_trans hl hlm
    by_contra hn
    have he : m=2 := by omega
    norm_num [hl2,he] at hproper
  have hm4 : m≤4 := by
    by_contra hn
    have hm5 : 5≤m := by omega
    have hmR : (5:ℝ)≤m := by exact_mod_cast hm5
    have hmB := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<5) hmR
    norm_num [hl2] at hlow
    simp only [one_div] at hmB
    linarith
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : 0<2*(p:ℝ) := by positivity
  rcases (show m=3 ∨ m=4 by omega) with hm|hm
  · have ha : (2*(p:ℝ)-1)/(2*(p:ℝ))≤(5:ℝ)/6 := by norm_num [hl2,hm] at harea ⊢;exact harea
    have hb := (div_le_iff₀ hp0).mp ha
    have hp3 : p≤3 := by
      have hbR : (p:ℝ)≤3 := by linarith
      exact_mod_cast hbR
    rcases (show p=2 ∨ p=3 by omega) with he|he
    · exact Or.inl (by simp [hl2,hm,he])
    · exact Or.inr (Or.inl (by simp [hl2,hm,he]))
  · have ha : (2*(p:ℝ)-1)/(2*(p:ℝ))≤(3:ℝ)/4 := by norm_num [hl2,hm] at harea ⊢;exact harea
    have hb := (div_le_iff₀ hp0).mp ha
    have hp2 : p=2 := by
      have hbR : (p:ℝ)≤2 := by linarith
      have hbN : p≤2 := by exact_mod_cast hbR
      omega
    exact Or.inr (Or.inr (by simp [hl2,hm,hp2]))

/-- Each of the three listed candidates really satisfies every arithmetic condition. -/
theorem halfTurn_exceptional_integer_triples_iff (l m p : ℕ) :
    (2≤l ∧ l≤m ∧ 2≤p ∧ (1:ℝ)/l+1/m<1 ∧
      (2*(p:ℝ)-1)/(2*(p:ℝ))≤1/(l:ℝ)+1/(m:ℝ)) ↔
    ((l,m,p)=(2,3,2) ∨ (l,m,p)=(2,3,3) ∨ (l,m,p)=(2,4,2)) := by
  constructor
  · rintro ⟨hl,hlm,hp,hproper,harea⟩
    exact halfTurn_exceptional_integer_triples l m p hl hlm hp hproper harea
  · intro h
    rcases h with h|h|h <;> simp only [Prod.mk.injEq] at h <;>
      rcases h with ⟨rfl,rfl,rfl⟩ <;> norm_num

/-- A proper actual triangle-order budget supplies the strict inequality used above. -/
theorem halfTurn_triangle_area_exceptional_triples (l m n p : ℕ)
    (hl : 2≤l) (hlm : l≤m) (hn : 2≤n) (hp : 2≤p)
    (hproper : (1:ℝ)/l+1/m+1/n<1)
    (harea : (2*(p:ℝ)-1)/(2*(p:ℝ))≤1/(l:ℝ)+1/(m:ℝ)) :
    (l,m,p)=(2,3,2) ∨ (l,m,p)=(2,3,3) ∨ (l,m,p)=(2,4,2) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  exact halfTurn_exceptional_integer_triples l m p hl hlm hp
    (by linarith [one_div_pos.mpr hnR]) harea

/-- The first and last terms of the trace inequality already force the complete list. -/
theorem halfTurn_first_last_area_exceptional_triples (l m n p : ℕ)
    (hl : 2≤l) (hlm : l≤m) (hn : 2≤n) (hp : 2≤p)
    (hproper : (1:ℝ)/l+1/m+1/n<1)
    (hbudget : 2*(p:ℝ)*(1-(1/(l:ℝ)+1/(m:ℝ)+1/(n:ℝ)))≤1-2*(p:ℝ)/(n:ℝ)) :
    (l,m,p)=(2,3,2) ∨ (l,m,p)=(2,3,3) ∨ (l,m,p)=(2,4,2) := by
  apply halfTurn_triangle_area_exceptional_triples l m n p hl hlm hn hp hproper
  have hpR : (0:ℝ)<p := by exact_mod_cast (by omega : 0<p)
  apply (div_le_iff₀ (by positivity : 0<2*(p:ℝ))).mpr
  have he : 2*(p:ℝ)/(n:ℝ)=2*(p:ℝ)*(1/(n:ℝ)) := by ring
  rw [he] at hbudget
  nlinarith [hbudget]

/-- All and only the listed triples have a proper finite triangle-order witness
satisfying the original first/last-term area inequality. -/
theorem halfTurn_first_last_area_exceptional_triples_iff (l m p : ℕ) :
    (2≤l ∧ l≤m ∧ 2≤p ∧ ∃ n : ℕ, 2≤n ∧ (1:ℝ)/l+1/m+1/n<1 ∧
      2*(p:ℝ)*(1-(1/(l:ℝ)+1/(m:ℝ)+1/(n:ℝ)))≤1-2*(p:ℝ)/(n:ℝ)) ↔
    ((l,m,p)=(2,3,2) ∨ (l,m,p)=(2,3,3) ∨ (l,m,p)=(2,4,2)) := by
  constructor
  · rintro ⟨hl,hlm,hp,n,hn,hproper,hbudget⟩
    exact halfTurn_first_last_area_exceptional_triples l m n p hl hlm hn hp hproper hbudget
  · intro h
    rcases h with h|h|h <;> simp only [Prod.mk.injEq] at h <;>
      rcases h with ⟨rfl,rfl,rfl⟩
    · refine ⟨by norm_num,by norm_num,by norm_num,7,?_⟩
      norm_num
    · refine ⟨by norm_num,by norm_num,by norm_num,7,?_⟩
      norm_num
    · refine ⟨by norm_num,by norm_num,by norm_num,5,?_⟩
      norm_num

end LowDimensionalTopology.Geometry.Fuchsian
