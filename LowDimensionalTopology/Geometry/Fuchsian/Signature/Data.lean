/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
namespace LowDimensionalTopology.Geometry.Fuchsian

/-- The actual numerical signature data. Geometric realization is a separate theorem. -/
structure FuchsianSignature where
  genus : ℕ
  ellipticOrders : List ℕ
  ellipticOrders_two_le : ∀m∈ellipticOrders,2≤m
  parabolicEnds : ℕ
  boundaryHyperbolicEnds : ℕ

/-- The Euler deficit used in area and realizability formulas. -/
def FuchsianSignature.deficit (s : FuchsianSignature) : ℝ :=
  2*(s.genus:ℝ)-2+s.parabolicEnds+s.boundaryHyperbolicEnds+
    (s.ellipticOrders.map (fun m:ℕ=>1-1/(m:ℝ))).sum

/-- Reciprocal elliptic orders decrease monotonically on positive natural orders. -/
theorem signature_reciprocal_le (k n : ℕ) (hk : 0<k) (hkn : k≤n) :
    1/(n:ℝ)≤1/(k:ℝ) := by
  exact one_div_le_one_div_of_le (by exact_mod_cast hk) (by exact_mod_cast hkn)

/-- Each genuine elliptic contribution lies in the actual interval [1/2,1). -/
theorem signature_elliptic_weight_bounds (m : ℕ) (hm : 2≤m) :
    1/2≤1-1/(m:ℝ) ∧ 1-1/(m:ℝ)<1 := by
  have hl:=signature_reciprocal_le 2 m (by decide) hm
  have hp : 0<1/(m:ℝ):=one_div_pos.mpr (by exact_mod_cast (show 0<m by omega))
  norm_num at hl
  simp only [one_div] at hl hp ⊢
  constructor <;> linarith

/-- The true elliptic contribution sum is bounded below by half the number of elliptic classes. -/
theorem signature_elliptic_sum_lower (l : List ℕ) (hl : ∀m∈l,2≤m) :
    (l.length:ℝ)/2≤(l.map (fun m:ℕ=>1-1/(m:ℝ))).sum := by
  induction l with
  | nil => norm_num
  | cons m l ih =>
    have hm:=signature_elliptic_weight_bounds m (hl m (by simp))
    have ht:=ih (fun n hn=>hl n (by simp only [List.mem_cons];exact Or.inr hn))
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    linarith

/-- The contribution sum is strictly less than the number of classes when the list is nonempty. -/
theorem signature_elliptic_sum_lt_length (l : List ℕ) (hl : ∀m∈l,2≤m) (hn : l≠[]) :
    (l.map (fun m:ℕ=>1-1/(m:ℝ))).sum<(l.length:ℝ) := by
  induction l with
  | nil => exact False.elim (hn rfl)
  | cons m l ih =>
    have hm:=signature_elliptic_weight_bounds m (hl m (by simp))
    by_cases ht : l=[]
    · subst l
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
        Nat.cast_add,Nat.cast_zero,Nat.cast_one,add_zero,zero_add] using hm.2
    · have htail:=ih (fun n hn=>hl n (by simp only [List.mem_cons];exact Or.inr hn)) ht
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith

/-- Reordering the elliptic classes leaves the exact geometric area factor unchanged. -/
theorem signature_elliptic_sum_perm {l k : List ℕ} (h : l.Perm k) :
    (l.map (fun m:ℕ=>1-1/(m:ℝ))).sum=(k.map (fun m:ℕ=>1-1/(m:ℝ))).sum :=
  (h.map _).sum_eq

/-- The positive triangular signature deficit has sharp minimum 1/42, attained only at (2,3,7). -/
theorem triangle_signature_deficit_sharp (p q r : ℕ) (hp : 2≤p) (hpq : p≤q) (hqr : q≤r)
    (hpos : 0<1-1/(p:ℝ)-1/(q:ℝ)-1/(r:ℝ)) :
    1/42≤1-1/(p:ℝ)-1/(q:ℝ)-1/(r:ℝ) ∧
      (1-1/(p:ℝ)-1/(q:ℝ)-1/(r:ℝ)=1/42 ↔ p=2 ∧ q=3 ∧ r=7) := by
  simp only [one_div] at hpos ⊢
  by_cases he : p=2 ∧ q=3 ∧ r=7
  · rcases he with ⟨rfl,rfl,rfl⟩
    norm_num
  · have hstrict : (42:ℝ)⁻¹<1-(p:ℝ)⁻¹-(q:ℝ)⁻¹-(r:ℝ)⁻¹ := by
      by_cases hp4 : 4≤p
      · have h1:=signature_reciprocal_le 4 p (by decide) hp4
        have h2:=signature_reciprocal_le 4 q (by decide) (by omega)
        have h3:=signature_reciprocal_le 4 r (by decide) (by omega)
        norm_num at h1 h2 h3
        linarith
      · have hpCases : p=2 ∨ p=3:=by omega
        rcases hpCases with rfl | rfl
        · by_cases hq5 : 5≤q
          · have h1:=signature_reciprocal_le 5 q (by decide) hq5
            have h2:=signature_reciprocal_le 5 r (by decide) (by omega)
            norm_num at h1 h2 ⊢
            linarith
          · have hqCases : q=2 ∨ q=3 ∨ q=4:=by omega
            rcases hqCases with rfl | rfl | rfl
            · have h3 : 0<1/(r:ℝ):=one_div_pos.mpr (by exact_mod_cast (show 0<r by omega))
              norm_num at hpos
              linarith
            · have hr7 : 7≤r := by
                by_contra hn
                have hsmall : r≤6:=by omega
                have h:=signature_reciprocal_le r 6 (by omega) hsmall
                norm_num at h hpos
                linarith
              have hr8 : 8≤r:=by omega
              have h3:=signature_reciprocal_le 8 r (by decide) hr8
              norm_num at h3 ⊢
              linarith
            · have hr5 : 5≤r := by
                by_contra hn
                have hsmall : r≤4:=by omega
                have h:=signature_reciprocal_le r 4 (by omega) hsmall
                norm_num at h hpos
                linarith
              have h3:=signature_reciprocal_le 5 r (by decide) hr5
              norm_num at h3 ⊢
              linarith
        · by_cases hq4 : 4≤q
          · have h2:=signature_reciprocal_le 4 q (by decide) hq4
            have h3:=signature_reciprocal_le 4 r (by decide) (by omega)
            norm_num at h2 h3 ⊢
            linarith
          · have hq3 : q=3:=by omega
            subst q
            have hr4 : 4≤r := by
              by_contra hn
              have hsmall : r≤3:=by omega
              have h:=signature_reciprocal_le r 3 (by omega) hsmall
              norm_num at h hpos
              linarith
            have h3:=signature_reciprocal_le 4 r (by decide) hr4
            norm_num at h3 ⊢
            linarith
    exact ⟨hstrict.le,iff_of_false (ne_of_gt hstrict) he⟩

/-- All order-two classes give exactly the corresponding half-integer contribution. -/
theorem signature_elliptic_sum_all_two (l : List ℕ) (hl : ∀m∈l,m=2) :
    (l.map (fun m:ℕ=>1-1/(m:ℝ))).sum=(l.length:ℝ)/2 := by
  induction l with
  | nil => norm_num
  | cons m l ih =>
    have hm:=hl m (by simp)
    have ht:=ih (fun n hn=>hl n (by simp only [List.mem_cons];exact Or.inr hn))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,hm,ht]
    norm_num
    ring

/-- One actual elliptic order at least three contributes a strict 1/6 excess above half-counting. -/
theorem signature_elliptic_sum_excess (l : List ℕ) (hl : ∀m∈l,2≤m)
    (hex : ∃m∈l,3≤m) :
    (l.length:ℝ)/2+1/6≤(l.map (fun m:ℕ=>1-1/(m:ℝ))).sum := by
  induction l with
  | nil => simp at hex
  | cons m l ih =>
    have htail : ∀n∈l,2≤n:=fun n hn=>hl n (by simp only [List.mem_cons];exact Or.inr hn)
    have hm:=signature_elliptic_weight_bounds m (hl m (by simp))
    by_cases hm3 : 3≤m
    · have hi:=signature_reciprocal_le 3 m (by decide) hm3
      have ht:=signature_elliptic_sum_lower l htail
      simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
      norm_num at hi
      simp only [one_div] at hi hm ht ⊢
      linarith
    · have hext : ∃n∈l,3≤n := by
        obtain ⟨n,hn,hn3⟩:=hex
        rcases List.mem_cons.mp hn with rfl | hn
        · exact False.elim (hm3 hn3)
        · exact ⟨n,hn,hn3⟩
      have ht:=ih htail hext
      simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
      linarith

/-- A sufficiently small positive numerical deficit necessarily has genus/ends complexity
zero and exactly three elliptic classes. This proves the reduction rather than assuming it. -/
theorem signature_small_deficit_structure (n : ℕ) (l : List ℕ) (hl : ∀m∈l,2≤m)
    (hpos : 0<(n:ℝ)-2+(l.map (fun m:ℕ=>1-1/(m:ℝ))).sum)
    (hsmall : (n:ℝ)-2+(l.map (fun m:ℕ=>1-1/(m:ℝ))).sum≤1/42) : n=0 ∧ l.length=3 := by
  classical
  by_cases hall : ∀m∈l,m=2
  · have hs:=signature_elliptic_sum_all_two l hall
    rw [hs] at hpos hsmall
    have hc : 4<2*n+l.length := by
      have hr : (4:ℝ)<2*(n:ℝ)+(l.length:ℝ):=by linarith
      exact_mod_cast hr
    have hcR : (5:ℝ)≤2*(n:ℝ)+(l.length:ℝ):=by exact_mod_cast (show 5≤2*n+l.length by omega)
    linarith
  · push Not at hall
    obtain ⟨m,hm,hm2⟩:=hall
    have hex : ∃m∈l,3≤m:=⟨m,hm,by have h:=hl m hm;omega⟩
    have he:=signature_elliptic_sum_excess l hl hex
    have hn : l≠[]:=by intro h;simp only [h,List.not_mem_nil] at hm
    have ht:=signature_elliptic_sum_lt_length l hl hn
    have hc : 2*n+l.length<4 := by
      have hr : 2*(n:ℝ)+(l.length:ℝ)<4:=by linarith
      exact_mod_cast hr
    have hd : 2<n+l.length := by
      have hr : (2:ℝ)<(n:ℝ)+(l.length:ℝ):=by linarith
      exact_mod_cast hr
    omega

/-- Any three genuine elliptic orders can be sorted by an actual list permutation. -/
theorem signature_sorted_three (p q r : ℕ) :
    ∃a b c : ℕ,[a,b,c].Perm [p,q,r] ∧ a≤b ∧ b≤c := by
  rcases le_total p q with hpq | hqp
  · rcases le_total q r with hqr | hrq
    · exact ⟨p,q,r,List.Perm.refl _,hpq,hqr⟩
    · rcases le_total p r with hpr | hrp
      · exact ⟨p,r,q,by apply List.perm_iff_count.mpr;intro x;simp only [List.count_cons,List.count_nil];omega,hpr,hrq⟩
      · exact ⟨r,p,q,by apply List.perm_iff_count.mpr;intro x;simp only [List.count_cons,List.count_nil];omega,hrp,hpq⟩
  · rcases le_total p r with hpr | hrp
    · exact ⟨q,p,r,by apply List.perm_iff_count.mpr;intro x;simp only [List.count_cons,List.count_nil];omega,hqp,hpr⟩
    · rcases le_total q r with hqr | hrq
      · exact ⟨q,r,p,by apply List.perm_iff_count.mpr;intro x;simp only [List.count_cons,List.count_nil];omega,hqr,hrp⟩
      · exact ⟨r,q,p,by apply List.perm_iff_count.mpr;intro x;simp only [List.count_cons,List.count_nil];omega,hrq,hqp⟩

/-- The triangular minimum and its unique signature are independent of all orderings. -/
theorem triangle_signature_deficit_sharp_perm (p q r : ℕ) (hp : 2≤p) (hq : 2≤q) (hr : 2≤r)
    (hpos : 0<1-1/(p:ℝ)-1/(q:ℝ)-1/(r:ℝ)) :
    1/42≤1-1/(p:ℝ)-1/(q:ℝ)-1/(r:ℝ) ∧
      (1-1/(p:ℝ)-1/(q:ℝ)-1/(r:ℝ)=1/42 ↔ [p,q,r].Perm [2,3,7]) := by
  simp only [one_div] at hpos ⊢
  obtain ⟨a,b,c,hperm,hab,hbc⟩:=signature_sorted_three p q r
  have ha : 2≤a := by
    have h:=hperm.mem_iff.mp (show a∈[a,b,c] by simp)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl <;> assumption
  have hdelta : 1-(a:ℝ)⁻¹-(b:ℝ)⁻¹-(c:ℝ)⁻¹=1-(p:ℝ)⁻¹-(q:ℝ)⁻¹-(r:ℝ)⁻¹ := by
    have hs:=signature_elliptic_sum_perm hperm
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,one_div] at hs
    linarith
  have hpos' : 0<1-(a:ℝ)⁻¹-(b:ℝ)⁻¹-(c:ℝ)⁻¹:=by rw [hdelta];exact hpos
  have hs:=triangle_signature_deficit_sharp a b c ha hab hbc (by simpa only [one_div] using hpos')
  simp only [one_div] at hs
  refine ⟨by rw [←hdelta];exact hs.1,?_⟩
  constructor
  · intro he
    have habc:=hs.2.mp (hdelta.trans he)
    rcases habc with ⟨rfl,rfl,rfl⟩
    exact hperm.symm
  · intro he
    have hsum:=signature_elliptic_sum_perm he
    norm_num at hsum
    linarith

/-- The full numerical signature deficit has sharp minimum 1/42, with no a priori bound
on genus, ends, the number of elliptic classes, or the ordering of their genuine orders. -/
theorem signature_numeric_deficit_sharp (n : ℕ) (l : List ℕ) (hl : ∀m∈l,2≤m)
    (hpos : 0<(n:ℝ)-2+(l.map (fun m:ℕ=>1-1/(m:ℝ))).sum) :
    1/42≤(n:ℝ)-2+(l.map (fun m:ℕ=>1-1/(m:ℝ))).sum ∧
      ((n:ℝ)-2+(l.map (fun m:ℕ=>1-1/(m:ℝ))).sum=1/42 ↔ n=0 ∧ l.Perm [2,3,7]) := by
  by_cases hsmall : (n:ℝ)-2+(l.map (fun m:ℕ=>1-1/(m:ℝ))).sum≤1/42
  · obtain ⟨hn,hlen⟩:=signature_small_deficit_structure n l hl hpos hsmall
    subst n
    simp only [Nat.cast_zero] at hpos hsmall ⊢
    obtain ⟨p,q,r,rfl⟩:=List.length_eq_three.mp hlen
    have hp : 2≤p:=hl p (by simp)
    have hq : 2≤q:=hl q (by simp)
    have hr : 2≤r:=hl r (by simp)
    have heq : (0:ℝ)-2+([p,q,r].map (fun m:ℕ=>1-1/(m:ℝ))).sum=
        1-1/(p:ℝ)-1/(q:ℝ)-1/(r:ℝ) := by
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      ring
    have hp' : 0<1-1/(p:ℝ)-1/(q:ℝ)-1/(r:ℝ) := by
      rw [←heq]
      exact hpos
    have hs:=triangle_signature_deficit_sharp_perm p q r hp hq hr hp'
    rw [heq]
    simpa using hs
  · have hstrict : 1/42<(n:ℝ)-2+(l.map (fun m:ℕ=>1-1/(m:ℝ))).sum:=lt_of_not_ge hsmall
    refine ⟨hstrict.le,iff_of_false (ne_of_gt hstrict) ?_⟩
    rintro ⟨rfl,hperm⟩
    have hs:=signature_elliptic_sum_perm hperm
    norm_num at hs hstrict
    linarith

/-- The genuine numerical signature minimum, with its unique genus/ends/order-list data. -/
theorem FuchsianSignature.deficit_sharp (s : FuchsianSignature) (hpos : 0<s.deficit) :
    1/42≤s.deficit ∧ (s.deficit=1/42 ↔ s.genus=0 ∧ s.parabolicEnds=0 ∧
      s.boundaryHyperbolicEnds=0 ∧ s.ellipticOrders.Perm [2,3,7]) := by
  let n:=2*s.genus+s.parabolicEnds+s.boundaryHyperbolicEnds
  have heq : (n:ℝ)-2+(s.ellipticOrders.map (fun m:ℕ=>1-1/(m:ℝ))).sum=s.deficit := by
    simp only [n, _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat]
    ring
  have hs:=signature_numeric_deficit_sharp n s.ellipticOrders s.ellipticOrders_two_le (by rw [heq];exact hpos)
  rw [heq] at hs
  refine ⟨hs.1,?_⟩
  constructor
  · intro h
    obtain ⟨hn,hperm⟩:=hs.2.mp h
    have hz : s.genus=0 ∧ s.parabolicEnds=0 ∧ s.boundaryHyperbolicEnds=0 := by dsimp only [n] at hn;omega
    exact ⟨hz.1,hz.2.1,hz.2.2,hperm⟩
  · rintro ⟨hg,hp,hb,hperm⟩
    exact hs.2.mpr ⟨by simp only [n,hg,hp,hb,Nat.mul_zero,Nat.zero_add],hperm⟩

/-- The source area-formula expression; identifying it with actual quotient area remains a
geometric theorem, not an assumption hidden in this numerical definition. -/
def FuchsianSignature.areaFormulaValue (s : FuchsianSignature) : ℝ:=2*Real.pi*s.deficit

/-- The area formula's numerical value is at least pi/21, with the exact unique signature. -/
theorem FuchsianSignature.areaFormulaValue_sharp (s : FuchsianSignature) (hpos : 0<s.deficit) :
    Real.pi/21≤s.areaFormulaValue ∧ (s.areaFormulaValue=Real.pi/21 ↔ s.genus=0 ∧ s.parabolicEnds=0 ∧
      s.boundaryHyperbolicEnds=0 ∧ s.ellipticOrders.Perm [2,3,7]) := by
  have hs:=s.deficit_sharp hpos
  have hp:=Real.pi_pos
  have hmul : 0<2*Real.pi:=by positivity
  constructor
  · dsimp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.areaFormulaValue]
    nlinarith [mul_le_mul_of_nonneg_left hs.1 hmul.le]
  · have heq : s.areaFormulaValue=Real.pi/21 ↔ s.deficit=1/42 := by
      dsimp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.areaFormulaValue]
      constructor <;> intro h <;> nlinarith
    exact heq.trans hs.2

/-- The unique numerical signature at the sharp lower bound; existence of its actual
Fuchsian realization is a distinct geometric assertion. -/
def hurwitzSignature : FuchsianSignature where
  genus:=0
  ellipticOrders:=[2,3,7]
  ellipticOrders_two_le:=by
    intro m hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    omega
  parabolicEnds:=0
  boundaryHyperbolicEnds:=0

theorem hurwitzSignature_deficit : hurwitzSignature.deficit=1/42 := by
  norm_num [hurwitzSignature,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit]

theorem hurwitzSignature_areaFormulaValue : hurwitzSignature.areaFormulaValue=Real.pi/21 := by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.areaFormulaValue,hurwitzSignature_deficit]
  ring

/-- The numerical lower bound is attained, rather than merely an unattained infimum. -/
theorem signature_deficit_isLeast :
    IsLeast {v : ℝ | ∃s : FuchsianSignature,0<s.deficit ∧ s.deficit=v} (1/42) := by
  refine ⟨⟨hurwitzSignature,by rw [hurwitzSignature_deficit];norm_num,hurwitzSignature_deficit⟩,?_⟩
  rintro v ⟨s,hpos,rfl⟩
  exact (s.deficit_sharp hpos).1

/-- The area expression has the exact attained minimum pi/21. This statement does not
assume that the expression has already been identified with an actual quotient measure. -/
theorem signature_areaFormulaValue_isLeast :
    IsLeast {v : ℝ | ∃s : FuchsianSignature,0<s.deficit ∧ s.areaFormulaValue=v} (Real.pi/21) := by
  refine ⟨⟨hurwitzSignature,by rw [hurwitzSignature_deficit];norm_num,hurwitzSignature_areaFormulaValue⟩,?_⟩
  rintro v ⟨s,hpos,rfl⟩
  exact (s.areaFormulaValue_sharp hpos).1

end LowDimensionalTopology.Geometry.Fuchsian
