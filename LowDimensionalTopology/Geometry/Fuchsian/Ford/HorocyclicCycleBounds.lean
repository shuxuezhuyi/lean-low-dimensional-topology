/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.TrigonometricInequalities
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementGeometry
/-! # Finite Jensen estimates for horocyclic vertex configurations

These analytic lemmas keep the angle partition and projection identities
explicit. Constructing them from actual Ford-domain cycles is a separate
geometric obligation; they do not assume or claim that group-level adapter.
-/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Fuchsian
open Set LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Fuchsian
open scoped UpperHalfPlane BigOperators
noncomputable section

theorem cot_antitone_on_acute {x y : ℝ} (hx : x∈Ioo (0:ℝ) (Real.pi/2))
    (hy : y∈Ioo (0:ℝ) (Real.pi/2)) (hxy : x≤y) : Real.cot y≤Real.cot x := by
  have ht:=Real.strictMonoOn_tan.monotoneOn
    (show x∈Ioo (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩)
    (show y∈Ioo (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith [hy.1,Real.pi_pos],hy.2⟩) hxy
  rw [←Real.tan_inv_eq_cot,←Real.tan_inv_eq_cot,inv_eq_one_div,inv_eq_one_div]
  exact one_div_le_one_div_of_le (Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 hx.2) ht

/-- The mean of a nonempty finite collection of genuine acute angles is acute. -/
theorem acute_angle_mean {n : ℕ} (hn : 0<n) (θ : Fin n→ℝ)
    (hθ : ∀ i,θ i∈Ioo (0:ℝ) (Real.pi/2)) :
    (∑ i,θ i)/(n:ℝ)∈Ioo (0:ℝ) (Real.pi/2) := by
  have hnR : (0:ℝ)<n:=by exact_mod_cast hn
  have hne : (Finset.univ:Finset (Fin n)).Nonempty:=⟨⟨0,hn⟩,Finset.mem_univ _⟩
  constructor
  · exact div_pos (Finset.sum_pos (fun i _=>(hθ i).1) hne) hnR
  · apply (div_lt_iff₀ hnR).mpr
    have h:=Finset.sum_lt_sum (s:=(Finset.univ:Finset (Fin n)))
      (fun i _=>(hθ i).2.le) ⟨⟨0,hn⟩,Finset.mem_univ _,(hθ ⟨0,hn⟩).2⟩
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using h

/-- The exact finite Jensen step, with its geometric premises visible. -/
theorem horocyclic_height_bound_from_angle_partition {n q : ℕ} (hn : 0<n) (hq : 0<q)
    (hqn : 2<q*n) (θ : Fin n→ℝ) (z : ℍ)
    (hθ : ∀ i,θ i∈Ioo (0:ℝ) (Real.pi/2))
    (hsum : ∑ i,θ i≤Real.pi/(q:ℝ))
    (hprojection : ∑ i,z.im*Real.cot (θ i)=1/2) :
    z.im≤Real.tan (Real.pi/((q:ℝ)*(n:ℝ)))/(2*(n:ℝ)) := by
  have hnR : (0:ℝ)<n:=by exact_mod_cast hn
  have hqR : (0:ℝ)<q:=by exact_mod_cast hq
  have hqnR : (2:ℝ)<(q:ℝ)*(n:ℝ):=by exact_mod_cast hqn
  let B:=Real.pi/((q:ℝ)*(n:ℝ))
  have hB : B∈Ioo (0:ℝ) (Real.pi/2):=by
    refine ⟨div_pos Real.pi_pos (mul_pos hqR hnR),?_⟩
    apply (div_lt_iff₀ (mul_pos hqR hnR)).mpr
    nlinarith only [mul_pos (sub_pos.mpr hqnR) Real.pi_pos]
  have hmean:=acute_angle_mean hn θ hθ
  have hmeanB : (∑ i,θ i)/(n:ℝ)≤B:=by
    have h:=div_le_div_of_nonneg_right hsum hnR.le
    simpa only [div_div] using h
  have hcot:=cot_antitone_on_acute hmean hB hmeanB
  have hne : (Finset.univ:Finset (Fin n)).Nonempty:=⟨⟨0,hn⟩,Finset.mem_univ _⟩
  have hj:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.mean_cotangent Finset.univ hne θ (fun i _=>hθ i)
  simp only [Finset.card_univ,Fintype.card_fin] at hj
  have hbound : Real.cot B≤(∑ i,Real.cot (θ i))/(n:ℝ):=hcot.trans hj
  rw [←Real.tan_inv_eq_cot,inv_eq_one_div] at hbound
  have hcross:=(div_le_div_iff₀ (Real.tan_pos_of_pos_of_lt_pi_div_two hB.1 hB.2) hnR).mp hbound
  rw [one_mul] at hcross
  have heq : z.im*(∑ i,Real.cot (θ i))=1/2:=by
    simpa only [Finset.mul_sum] using hprojection
  have hy : z.im*(n:ℝ)≤Real.tan B/2:=by
    calc
      z.im*(n:ℝ)≤z.im*((∑ i,Real.cot (θ i))*Real.tan B):=
        mul_le_mul_of_nonneg_left hcross z.im_pos.le
      _=(z.im*(∑ i,Real.cot (θ i)))*Real.tan B:=by ring
      _=Real.tan B/2:=by rw [heq];ring
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hnR)).mpr
  change z.im*(2*(n:ℝ))≤Real.tan B
  nlinarith only [hy]

/-- A true upper height bound is exactly a lower bound for the normalized parabolic half displacement. -/
theorem unitTranslation_half_displacement_lower_of_height (z : ℍ) (b : ℝ)
    (hheight : z.im≤b) :
    1/(2*b)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) z := by
  change _≤Real.sinh (dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z)/2)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_half_displacement]
  norm_num only [abs_one]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hheight])

def cycleHeightBound (q n : ℕ) : ℝ := Real.tan (Real.pi/((q:ℝ)*(n:ℝ)))/(2*(n:ℝ))

theorem pi_div_acute_of_two_lt (x : ℝ) (hx : 2<x) :
    Real.pi/x∈Ioo (0:ℝ) (Real.pi/2) := by
  have hx0 : 0<x:=by linarith only [hx]
  refine ⟨div_pos Real.pi_pos hx0,?_⟩
  apply (div_lt_iff₀ hx0).mpr
  nlinarith only [mul_pos (sub_pos.mpr hx) Real.pi_pos]

/-- The exact Jensen bound decreases when the number of vertices increases. -/
theorem cycleHeightBound_antitone_count (q k n : ℕ) (hq : 0<q) (hk : 0<k)
    (hkn : k≤n) (hqk : 2<q*k) : cycleHeightBound q n≤cycleHeightBound q k := by
  have hqR : (0:ℝ)<q:=by exact_mod_cast hq
  have hkR : (0:ℝ)<k:=by exact_mod_cast hk
  have hknR : (k:ℝ)≤n:=by exact_mod_cast hkn
  have hnR : (0:ℝ)<n:=hkR.trans_le hknR
  have hqkR : (2:ℝ)<(q:ℝ)*(k:ℝ):=by exact_mod_cast hqk
  have hproduct : (q:ℝ)*(k:ℝ)≤(q:ℝ)*(n:ℝ):=mul_le_mul_of_nonneg_left hknR hqR.le
  have hAk:=pi_div_acute_of_two_lt _ hqkR
  have hAn:=pi_div_acute_of_two_lt _ (hqkR.trans_le hproduct)
  have harg : Real.pi/((q:ℝ)*(n:ℝ))≤Real.pi/((q:ℝ)*(k:ℝ)):=
    div_le_div_of_nonneg_left Real.pi_pos.le (mul_pos hqR hkR) hproduct
  have ht:=Real.strictMonoOn_tan.monotoneOn
    (show Real.pi/((q:ℝ)*(n:ℝ))∈Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hAn.1,Real.pi_pos],hAn.2⟩)
    (show Real.pi/((q:ℝ)*(k:ℝ))∈Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hAk.1,Real.pi_pos],hAk.2⟩) harg
  unfold cycleHeightBound
  calc
    _≤Real.tan (Real.pi/((q:ℝ)*(n:ℝ)))/(2*(k:ℝ)):=
      div_le_div_of_nonneg_left (Real.tan_nonneg_of_nonneg_of_le_pi_div_two hAn.1.le hAn.2.le)
        (by positivity) (by linarith only [hknR])
    _≤_:=div_le_div_of_nonneg_right ht (by positivity)

theorem cycleHeightBound_accidental_le (n : ℕ) (hn : 3≤n) :
    cycleHeightBound 1 n≤1/(2*Real.sqrt 3) := by
  have h:=cycleHeightBound_antitone_count 1 3 n (by decide) (by decide) hn (by decide)
  have he : cycleHeightBound 1 3=1/(2*Real.sqrt 3):=by
    norm_num only [cycleHeightBound,Nat.cast_one,one_mul,Nat.cast_ofNat,Real.tan_pi_div_three]
    have hsqrt : Real.sqrt 3≠0:=ne_of_gt (by positivity)
    field_simp
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  exact h.trans_eq he

theorem cycleHeightBound_elliptic_le (q n : ℕ) (hq : 3≤q) (hn : 0<n) :
    cycleHeightBound q n≤Real.tan (Real.pi/(q:ℝ))/2 := by
  have h:=cycleHeightBound_antitone_count q 1 n (by omega) (by decide) (by omega) (by simpa only [mul_one] using (show 2<q by omega))
  simpa only [cycleHeightBound,Nat.cast_one,mul_one] using h

/-- The analytic accidental-cycle estimate keeps its actual geometric partition premises explicit. -/
theorem horocyclic_accidental_height_bound_from_angle_partition {n : ℕ} (hn : 3≤n)
    (θ : Fin n→ℝ) (z : ℍ) (hθ : ∀ i,θ i∈Ioo (0:ℝ) (Real.pi/2))
    (hsum : ∑ i,θ i≤Real.pi) (hprojection : ∑ i,z.im*Real.cot (θ i)=1/2) :
    z.im≤1/(2*Real.sqrt 3) := by
  have h:=horocyclic_height_bound_from_angle_partition (q:=1) (by omega) (by decide)
    (by simpa only [one_mul] using (show 2<n by omega)) θ z hθ (by simpa only [Nat.cast_one,div_one] using hsum) hprojection
  exact h.trans (cycleHeightBound_accidental_le n hn)

/-- The analytic elliptic-cycle estimate still requires the explicit actual angle partition. -/
theorem horocyclic_elliptic_height_bound_from_angle_partition {n q : ℕ} (hn : 0<n) (hq : 3≤q)
    (θ : Fin n→ℝ) (z : ℍ) (hθ : ∀ i,θ i∈Ioo (0:ℝ) (Real.pi/2))
    (hsum : ∑ i,θ i≤Real.pi/(q:ℝ)) (hprojection : ∑ i,z.im*Real.cot (θ i)=1/2) :
    z.im≤Real.tan (Real.pi/(q:ℝ))/2 := by
  have hqn : 2<q*n:=by nlinarith
  exact (horocyclic_height_bound_from_angle_partition hn (by omega) hqn θ z hθ hsum hprojection).trans
    (cycleHeightBound_elliptic_le q n hq hn)

theorem horocyclic_accidental_displacement_bound_from_angle_partition {n : ℕ} (hn : 3≤n)
    (θ : Fin n→ℝ) (z : ℍ) (hθ : ∀ i,θ i∈Ioo (0:ℝ) (Real.pi/2))
    (hsum : ∑ i,θ i≤Real.pi) (hprojection : ∑ i,z.im*Real.cot (θ i)=1/2) :
    Real.sqrt 3≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) z := by
  have h:=unitTranslation_half_displacement_lower_of_height z (1/(2*Real.sqrt 3))
    (horocyclic_accidental_height_bound_from_angle_partition hn θ z hθ hsum hprojection)
  have hsqrt : Real.sqrt 3≠0:=ne_of_gt (by positivity)
  have he : 1/(2*(1/(2*Real.sqrt 3)))=Real.sqrt 3:=by field_simp
  rwa [he] at h

theorem horocyclic_elliptic_displacement_bound_from_angle_partition {n q : ℕ} (hn : 0<n) (hq : 3≤q)
    (θ : Fin n→ℝ) (z : ℍ) (hθ : ∀ i,θ i∈Ioo (0:ℝ) (Real.pi/2))
    (hsum : ∑ i,θ i≤Real.pi/(q:ℝ)) (hprojection : ∑ i,z.im*Real.cot (θ i)=1/2) :
    Real.cot (Real.pi/(q:ℝ))≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) z := by
  have h:=unitTranslation_half_displacement_lower_of_height z (Real.tan (Real.pi/(q:ℝ))/2)
    (horocyclic_elliptic_height_bound_from_angle_partition hn hq θ z hθ hsum hprojection)
  have he : 1/(2*(Real.tan (Real.pi/(q:ℝ))/2))=Real.cot (Real.pi/(q:ℝ)):=by
    rw [←Real.tan_inv_eq_cot,inv_eq_one_div]
    congr 1
    ring
  rwa [he] at h

end
end LowDimensionalTopology.Geometry.Fuchsian
