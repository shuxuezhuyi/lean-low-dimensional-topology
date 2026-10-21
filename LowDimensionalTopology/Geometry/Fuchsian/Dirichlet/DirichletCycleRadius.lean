/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.TrigonometricInequalities
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.RightTriangleIdentities
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleAngleSum
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.HorocyclicCycleBounds
/-! # Genuine right-triangle radius estimates for Dirichlet cycle geometry

The right triangles have their actual native side lengths and angles. The
finite fan angle budget remains explicit until the actual Dirichlet-cycle
construction is available; no group-level source theorem is asserted here.
-/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Fuchsian
open Set LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Fuchsian
open scoped UpperHalfPlane BigOperators
noncomputable section

theorem rightTriangle_acute_other_angles (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (hγ :
  T.gamma=Real.pi/2) :
    T.alpha∈Ioo (0:ℝ) (Real.pi/2) ∧ T.beta∈Ioo (0:ℝ) (Real.pi/2) := by
  have hs:=T.angle_sum_lt_pi
  rw [hγ] at hs
  have hpα:=T.angles_mem_Ioo.1.1
  have hpβ:=T.angles_mem_Ioo.2.1.1
  exact ⟨⟨hpα,by linarith only [hs,hpβ]⟩,⟨hpβ,by linarith only [hs,hpα]⟩⟩

/-- The exact source hypotenuse relation for every genuine right triangle. -/
theorem rightTriangle_cosh_tan_product (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (hγ :
  T.gamma=Real.pi/2) :
    Real.cosh T.lengthC*Real.tan T.alpha*Real.tan T.beta=1 := by
  obtain ⟨hα,hβ⟩:=rightTriangle_acute_other_angles T hγ
  have hcα : Real.cos T.alpha≠0:=ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hα.1,Real.pi_pos],hα.2⟩)
  have hcβ : Real.cos T.beta≠0:=ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hβ.1,Real.pi_pos],hβ.2⟩)
  obtain ⟨heA,heB⟩:=T.right_cosine_identities hγ
  rw [Real.tan_eq_sin_div_cos,Real.tan_eq_sin_div_cos]
  field_simp
  calc
    Real.cosh T.lengthC*Real.sin T.alpha*Real.sin T.beta=
      (Real.cosh T.lengthA*Real.sin T.beta)*(Real.cosh T.lengthB*Real.sin T.alpha):=by
        rw [T.cosh_hypotenuse_eq_cosh_mul_cosh hγ]
        ring
    _=Real.cos T.alpha*Real.cos T.beta:=by rw [heA,heB]

/-- An acute-angle sum bound gives a cotangent-square lower bound for the hypotenuse cosine. -/
theorem rightTriangle_cosh_ge_cot_sq (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (hγ :
  T.gamma=Real.pi/2)
    (n : ℕ) (hn : 5≤n) (hangle : T.alpha+T.beta≤2*Real.pi/(n:ℝ)) :
    Real.cot (Real.pi/(n:ℝ))^2≤Real.cosh T.lengthC := by
  have hnR : (5:ℝ)≤n:=by exact_mod_cast hn
  have hn0 : (0:ℝ)<n:=by linarith only [hnR]
  have hsmall : 2*Real.pi/(n:ℝ)<Real.pi/2:=by
    apply (div_lt_iff₀ hn0).mpr
    nlinarith only [mul_pos (show 0<(n:ℝ)-4 by linarith only [hnR]) Real.pi_pos]
  obtain ⟨hα,hβ⟩:=rightTriangle_acute_other_angles T hγ
  have hsum : T.alpha+T.beta<Real.pi/2:=hangle.trans_lt hsmall
  have hp:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.tangent_product hα hβ hsum
  have hBpos : 0<Real.pi/(n:ℝ):=div_pos Real.pi_pos hn0
  have hBlt : Real.pi/(n:ℝ)<Real.pi/2:=by
    apply (div_lt_iff₀ hn0).mpr
    nlinarith only [mul_pos (show 0<(n:ℝ)-2 by linarith only [hnR]) Real.pi_pos]
  have hhalf : (T.alpha+T.beta)/2≤Real.pi/(n:ℝ):=by
    have he : T.alpha+T.beta≤2*(Real.pi/(n:ℝ)):=by simpa only [mul_div_assoc] using hangle
    linarith only [he]
  have ht:=Real.strictMonoOn_tan.monotoneOn
    (show (T.alpha+T.beta)/2∈Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hα.1,hβ.1,Real.pi_pos],by linarith only [hsum,Real.pi_pos]⟩)
    (show Real.pi/(n:ℝ)∈Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hBpos,Real.pi_pos],hBlt⟩) hhalf
  have ht0 : 0≤Real.tan ((T.alpha+T.beta)/2):=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith [hα.1,hβ.1]) (by linarith only [hsum,Real.pi_pos])
  have hprod : Real.tan T.alpha*Real.tan T.beta≤Real.tan (Real.pi/(n:ℝ))^2:=
    hp.trans ((sq_le_sq₀ ht0 (ht0.trans ht)).mpr ht)
  have hid:=rightTriangle_cosh_tan_product T hγ
  have hmul:=mul_le_mul_of_nonneg_left hprod (Real.cosh_pos T.lengthC).le
  have htan : 0<Real.tan (Real.pi/(n:ℝ)):=Real.tan_pos_of_pos_of_lt_pi_div_two hBpos hBlt
  rw [←Real.tan_inv_eq_cot,inv_pow]
  apply (inv_le_iff_one_le_mul₀ (sq_pos_of_pos htan)).mpr
  nlinarith only [hid,hmul]

theorem finite_angle_budget_exists {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι→ℝ)
    (b : ℝ) (h : ∑ i∈s,f i≤(s.card:ℝ)*b) : ∃ i∈s,f i≤b := by
  by_contra hn
  push Not at hn
  have hlt:=Finset.sum_lt_sum (fun i hi=>(hn i hi).le)
    (hs.imp (fun i hi=>⟨hi,hn i hi⟩))
  have hlt' : (s.card:ℝ)*b<∑ i∈s,f i:=by
    simpa only [Finset.sum_const,nsmul_eq_mul] using hlt
  linarith only [h,hlt']

/-- An actual finite fan of right triangles with one genuine hypotenuse radius has the source radius bound. -/
theorem rightTriangleFan_cosh_radius_ge_cot_sq {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (T : ι→_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (hγ : ∀ i∈s,(T i).gamma=Real.pi/2) (r : ℝ)
    (hr : ∀ i∈s,(T i).lengthC=r) (n : ℕ) (hn : 5≤n)
    (hangle : ∑ i∈s,((T i).alpha+(T i).beta)≤(s.card:ℝ)*(2*Real.pi/(n:ℝ))) :
    Real.cot (Real.pi/(n:ℝ))^2≤Real.cosh r := by
  obtain ⟨i,hi,hsmall⟩:=finite_angle_budget_exists s hs (fun i=>(T i).alpha+(T i).beta)
    (2*Real.pi/(n:ℝ)) hangle
  rw [←hr i hi]
  exact rightTriangle_cosh_ge_cot_sq (T i) (hγ i hi) n hn hsmall

theorem positive_fin_angles_pair_lt_total {n : ℕ} (hn : 3≤n) (α : Fin n→ℝ)
    (hα : ∀ i,0<α i) (i j : Fin n) (hij : i≠j) : α i+α j<∑ k,α k := by
  classical
  have hex : ∃ k : Fin n,k≠i ∧ k≠j:=by
    by_contra hh
    push Not at hh
    have hsub : (Finset.univ:Finset (Fin n))⊆{i,j}:=by
      intro k _
      by_cases hki : k=i
      · simp only [Finset.mem_insert,Finset.mem_singleton,hki,true_or]
      · simp only [Finset.mem_insert,Finset.mem_singleton]
        exact Or.inr (hh k hki)
    have hc:=(Finset.card_le_card hsub).trans (Finset.card_le_two (a:=i) (b:=j))
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨k,hki,hkj⟩:=hex
  have h:=Finset.sum_lt_sum_of_subset (Finset.subset_univ ({i,j}:Finset (Fin n)))
    (Finset.mem_univ k) (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or];exact ⟨hki,hkj⟩)
    (hα k) (fun l _ _=>(hα l).le)
  simpa only [Finset.sum_pair hij] using h

/-- All but at most one of the true cyclic half-arcs are acute. -/
theorem cyclic_half_arc_other_acute {n : ℕ} (hn : 3≤n) (α : Fin n→ℝ)
    (hα : ∀ i,0<α i) (hsum : ∑ i,α i=Real.pi) (k : Fin n) (hk : Real.pi/2≤α k)
    (i : Fin n) (hik : i≠k) : α i<Real.pi/2 := by
  have hp:=positive_fin_angles_pair_lt_total hn α hα i k hik
  rw [hsum] at hp
  linarith only [hp,hk]

/-- The genuine source two-case averaging argument, including a cyclic gap of at least a half-turn. -/
theorem cyclic_half_arc_small_pair {n : ℕ} (hn : 5≤n) (α θ : Fin n→ℝ)
    (hα : ∀ i,0<α i) (hsumα : ∑ i,α i=Real.pi)
    (hsumθ : ∑ i∈Finset.univ.filter (fun i=>α i<Real.pi/2),θ i≤Real.pi) :
    ∃ i : Fin n,α i<Real.pi/2 ∧ α i+θ i≤2*Real.pi/(n:ℝ) := by
  classical
  have hnR : (5:ℝ)≤n:=by exact_mod_cast hn
  have hn0 : (0:ℝ)<n:=by linarith only [hnR]
  by_cases hall : ∀ i,α i<Real.pi/2
  · have he : Finset.univ.filter (fun i=>α i<Real.pi/2)=(Finset.univ:Finset (Fin n)):=by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hall i]
    rw [he] at hsumθ
    have hbudget : ∑ i,(α i+θ i)≤((Finset.univ:Finset (Fin n)).card:ℝ)*(2*Real.pi/(n:ℝ)):=by
      rw [Finset.sum_add_distrib,hsumα,Finset.card_univ,Fintype.card_fin]
      rw [mul_div_cancel₀ _ hn0.ne']
      linarith only [hsumθ]
    obtain ⟨i,_,hi⟩:=finite_angle_budget_exists Finset.univ
      ⟨⟨0,by omega⟩,Finset.mem_univ _⟩ (fun i=>α i+θ i) (2*Real.pi/(n:ℝ)) hbudget
    exact ⟨i,hall i,hi⟩
  · push Not at hall
    obtain ⟨k,hk⟩:=hall
    let S:=(Finset.univ:Finset (Fin n)).erase k
    have hothers : ∀ i,i≠k → α i<Real.pi/2:=cyclic_half_arc_other_acute (by omega) α hα hsumα k hk
    have he : Finset.univ.filter (fun i=>α i<Real.pi/2)=S:=by
      ext i
      simp only [Finset.mem_filter,S,Finset.mem_erase,Finset.mem_univ,true_and,and_true]
      constructor
      · intro hi hik
        exact (not_lt.mpr hk) (hik ▸ hi)
      · exact hothers i
    rw [he] at hsumθ
    have hc : S.card=n-1:=by simp only [S,Finset.card_erase_of_mem (Finset.mem_univ k),Finset.card_univ,Fintype.card_fin]
    have hne : S.Nonempty:=Finset.card_pos.mp (by rw [hc];omega)
    have hαS : ∑ i∈S,α i=Real.pi-α k:=by
      have h:=Finset.sum_erase_add (Finset.univ:Finset (Fin n)) α (Finset.mem_univ k)
      rw [hsumα] at h
      linarith only [h]
    have hsmall : ∑ i∈S,(α i+θ i)≤3*Real.pi/2:=by
      rw [Finset.sum_add_distrib,hαS]
      linarith only [hsumθ,hk]
    have hcR : (S.card:ℝ)=(n:ℝ)-1:=by
      rw [hc,Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
    have hconstant : 3*Real.pi/2≤(S.card:ℝ)*(2*Real.pi/(n:ℝ)):=by
      rw [hcR,←mul_div_assoc]
      apply (le_div_iff₀ hn0).mpr
      nlinarith only [mul_nonneg (show 0≤(n:ℝ)-4 by linarith only [hnR]) Real.pi_pos.le]
    obtain ⟨i,hi,hpair⟩:=finite_angle_budget_exists S hne (fun i=>α i+θ i)
      (2*Real.pi/(n:ℝ)) (hsmall.trans hconstant)
    exact ⟨i,hothers i (Finset.mem_erase.mp hi).1,hpair⟩

/-- Complete finite-cycle numerical step, with actual right triangles at every usable arc. -/
theorem dirichlet_cycle_radius_bound_from_right_triangles {n : ℕ} (hn : 5≤n)
    (α θ : Fin n→ℝ) (hα : ∀ i,0<α i) (hsumα : ∑ i,α i=Real.pi)
    (hsumθ : ∑ i∈Finset.univ.filter (fun i=>α i<Real.pi/2),θ i≤Real.pi)
    (T : Fin n→_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (r : ℝ)
    (hT : ∀ i,α i<Real.pi/2 → (T i).gamma=Real.pi/2 ∧
      (T i).alpha=α i ∧ (T i).beta=θ i ∧ (T i).lengthC=r) :
    Real.cot (Real.pi/(n:ℝ))^2≤Real.cosh r := by
  obtain ⟨i,hi,hpair⟩:=cyclic_half_arc_small_pair hn α θ hα hsumα hsumθ
  obtain ⟨hγ,hA,hB,hR⟩:=hT i hi
  rw [←hR]
  apply rightTriangle_cosh_ge_cot_sq (T i) hγ n hn
  simpa only [hA,hB] using hpair

theorem cot_sq_pi_div_five : Real.cot (Real.pi/5)^2=1+2*Real.sqrt 5/5 := by
  have hsqrt : (Real.sqrt 5)^2=5:=Real.sq_sqrt (by norm_num)
  have hs : Real.sin (Real.pi/5)≠0:=ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos]))
  rw [Real.cot_eq_cos_div_sin,div_pow]
  apply (div_eq_iff (pow_ne_zero 2 hs)).mpr
  have htrig:=Real.sin_sq_add_cos_sq (Real.pi/5)
  rw [Real.cos_pi_div_five] at htrig ⊢
  linear_combination -(1+2*Real.sqrt 5/5)*htrig+((Real.sqrt 5+7)/40)*hsqrt

/-- A strict rational lower bound for the squared cotangent at angles at most pi/5. -/
theorem cot_sq_pi_div_nat_gt_189_div_100 (n : ℕ) (hn : 5≤n) :
    (189:ℝ)/100<Real.cot (Real.pi/(n:ℝ))^2 := by
  have hnR : (5:ℝ)≤n:=by exact_mod_cast hn
  have hn2 : (2:ℝ)<n:=by linarith only [hnR]
  have hAn:=pi_div_acute_of_two_lt (n:ℝ) hn2
  have hA5:=pi_div_acute_of_two_lt (5:ℝ) (by norm_num)
  have harg : Real.pi/(n:ℝ)≤Real.pi/5:=div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR
  have hcot:=cot_antitone_on_acute hAn hA5 harg
  have hc0 : 0≤Real.cot (Real.pi/5):=by
    rw [←Real.tan_inv_eq_cot]
    exact inv_nonneg.mpr (Real.tan_pos_of_pos_of_lt_pi_div_two hA5.1 hA5.2).le
  have hsquare : Real.cot (Real.pi/5)^2≤Real.cot (Real.pi/(n:ℝ))^2:=
    (sq_le_sq₀ hc0 (hc0.trans hcot)).mpr hcot
  have hmin : (189:ℝ)/100<Real.cot (Real.pi/5)^2:=by
    rw [cot_sq_pi_div_five]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5),Real.sqrt_nonneg (5:ℝ)]
  exact hmin.trans_le hsquare

theorem dirichlet_cycle_radius_numeric_lower_from_right_triangles {n : ℕ} (hn : 5≤n)
    (α θ : Fin n→ℝ) (hα : ∀ i,0<α i) (hsumα : ∑ i,α i=Real.pi)
    (hsumθ : ∑ i∈Finset.univ.filter (fun i=>α i<Real.pi/2),θ i≤Real.pi)
    (T : Fin n→_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (r : ℝ)
    (hT : ∀ i,α i<Real.pi/2 → (T i).gamma=Real.pi/2 ∧
      (T i).alpha=α i ∧ (T i).beta=θ i ∧ (T i).lengthC=r) :
    (189:ℝ)/100<Real.cosh r :=
  (cot_sq_pi_div_nat_gt_189_div_100 n hn).trans_le
    (dirichlet_cycle_radius_bound_from_right_triangles hn α θ hα hsumα hsumθ T r hT)

end
end LowDimensionalTopology.Geometry.Fuchsian
