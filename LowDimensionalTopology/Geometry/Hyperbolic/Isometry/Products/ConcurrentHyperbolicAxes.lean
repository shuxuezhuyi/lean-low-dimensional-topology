/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.CommutatorGeometry
public import Mathlib.Data.Finset.Sort
public import Mathlib.Analysis.Complex.Angle
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped BigOperators UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The cyclic-gap pigeonhole bound on the real projective angular circle.
The actual angle application places the points in [0,L); the inequality is valid for every finite real set. -/
theorem real_projective_angle_pigeonhole (S : Finset ℝ) (hS : 2≤S.card) (L : ℝ) :
    ∃x∈S,∃y∈S,x≠y ∧ min |x-y| (L-|x-y|)≤L/(S.card:ℝ) := by
  classical
  let n:=S.card-1
  have hn : 0<n := by dsimp only [n];omega
  have hcard : S.card=n+1 := by dsimp only [n];omega
  rw [hcard]
  let γ:=S.orderEmbOfFin hcard
  let d:=L/((n+1:ℕ):ℝ)
  let g:ℕ→ℝ:=fun k=>if hk:k<n+1 then γ ⟨k,hk⟩ else 0
  have hg (k : ℕ) (hk : k<n+1) : g k=γ ⟨k,hk⟩ := dite_eq_left hk
  by_contra hfail
  have hgap (i j : Fin (n+1)) (hne : i≠j) :
      d<min |γ i-γ j| (L-|γ i-γ j|) := by
    apply lt_of_not_ge
    intro he
    apply hfail
    exact ⟨γ i,S.orderEmbOfFin_mem hcard i,γ j,S.orderEmbOfFin_mem hcard j,
      γ.injective.ne hne,he⟩
  have hadj (k : ℕ) (hk : k∈Finset.range n) : d≤g (k+1)-g k := by
    have hkn : k<n := Finset.mem_range.mp hk
    let i:Fin (n+1):=⟨k,by omega⟩
    let j:Fin (n+1):=⟨k+1,by omega⟩
    have hij : i<j := by change k<k+1;omega
    have hγij : γ i<γ j:=γ.strictMono hij
    have h:=lt_of_lt_of_le (hgap i j (ne_of_lt hij)) (min_le_left _ _)
    rw [abs_of_neg (sub_neg.mpr hγij)] at h
    rw [hg (k+1) (by omega),hg k (by omega)]
    change d≤γ j-γ i
    linarith
  have htel (m : ℕ) : (∑ k ∈ Finset.range m,(g (k+1)-g k))=g m-g 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ,ih];ring
  have hsum : (n:ℝ)*d≤g n-g 0 := calc
    _ = ∑ _k ∈ Finset.range n,d := by simp
    _ ≤ ∑ k ∈ Finset.range n,(g (k+1)-g k) := Finset.sum_le_sum hadj
    _ = _ := htel n
  rw [hg n (by omega),hg 0 (by omega)] at hsum
  change (n:ℝ)*d≤γ (Fin.last n)-γ 0 at hsum
  have hfirst : (0:Fin (n+1))<Fin.last n := by exact hn
  have hγfirst:=γ.strictMono hfirst
  have hwrap:=lt_of_lt_of_le (hgap 0 (Fin.last n) (ne_of_lt hfirst)) (min_le_right _ _)
  rw [abs_of_neg (sub_neg.mpr hγfirst)] at hwrap
  have hden : ((n:ℝ)+1)≠0 := by positivity
  have hd : ((n:ℝ)+1)*d=L := by
    dsimp only [d]
    push_cast
    field_simp
  nlinarith


/-- A canonical actual projective direction, using the genuine unit normal with nonnegative imaginary part. -/
def HalfPlaneLine.normalArg (L : HalfPlaneLine) (p : ℍ) : ℝ := Complex.arg (L.incenterNormalAt p)

/-- Actual upper-half-plane side-normal arguments lie in the source projective angular interval. -/
theorem HalfPlaneLine.normalArg_mem_Ico (L : HalfPlaneLine) (p : ℍ) :
    L.normalArg p∈Ico 0 Real.pi := by
  cases L with
  | vertical a =>
    simp [HalfPlaneLine.normalArg,HalfPlaneLine.incenterNormalAt_vertical,Real.pi_pos]
  | circle c r hr =>
    have him : 0<((HalfPlaneLine.circle c r hr).incenterNormalAt p).im := by
      rw [HalfPlaneLine.incenterNormalAt_circle]
      simpa only [Complex.smul_im,Complex.sub_im,Complex.ofReal_im,sub_zero,UpperHalfPlane.coe_im,
        smul_eq_mul] using mul_pos (inv_pos.mpr hr) p.im_pos
    exact ⟨Complex.arg_nonneg_iff.mpr him.le,Complex.arg_lt_pi_iff.mpr (Or.inr him.ne')⟩

/-- Actual tangent-line angles equal the actual unit side-normal angles. -/
theorem HalfPlaneLine.acuteAngle_eq_normalAngle (L M : HalfPlaneLine) (p : ℍ)
    (hpL : p∈L.carrier) (hpM : p∈M.carrier) :
    L.acuteAngle M p=acuteTangentAngle (L.incenterNormalAt p) (M.incenterNormalAt p) := by
  rw [HalfPlaneLine.acuteAngle,L.tangentAt_eq_incenterNormalAt p hpL,M.tangentAt_eq_incenterNormalAt p hpM,
    acuteTangentAngle_smul_left _ _ _ (norm_ne_zero_iff.mpr (L.tangentAt_ne_zero p)),
    acuteTangentAngle_smul_right _ _ _ (norm_ne_zero_iff.mpr (M.tangentAt_ne_zero p))]
  simp only [acuteTangentAngle,Complex.angle_mul_left Complex.I_ne_zero]

/-- The projective circular angular distance is exactly the angle between the two actual geodesics. -/
theorem HalfPlaneLine.acuteAngle_eq_normalArg (L M : HalfPlaneLine) (p : ℍ)
    (hpL : p∈L.carrier) (hpM : p∈M.carrier) :
    L.acuteAngle M p=min |L.normalArg p-M.normalArg p| (Real.pi-|L.normalArg p-M.normalArg p|) := by
  have hNL:=L.incenterNormalAt_norm p hpL
  have hNM:=M.incenterNormalAt_norm p hpM
  have hL:=L.normalArg_mem_Ico p
  have hM:=M.normalArg_mem_Ico p
  have harg : InnerProductGeometry.angle (L.incenterNormalAt p) (M.incenterNormalAt p)=
      |L.normalArg p-M.normalArg p| := by
    apply Real.arccos_eq_of_eq_cos (abs_nonneg _)
      (abs_le.mpr ⟨by linarith [hL.1,hM.2],by linarith [hM.1,hL.2]⟩)
    rw [Real.cos_abs,Real.cos_sub]
    dsimp only [HalfPlaneLine.normalArg]
    rw [Complex.cos_arg (by rw [←norm_ne_zero_iff,hNL];norm_num),
      Complex.cos_arg (by rw [←norm_ne_zero_iff,hNM];norm_num),Complex.sin_arg,Complex.sin_arg,
      hNL,hNM,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    simp
  rw [L.acuteAngle_eq_normalAngle M p hpL hpM]
  simp only [acuteTangentAngle,harg]

/-- Distinct actual geodesics through the same actual point have distinct projective direction arguments. -/
theorem HalfPlaneLine.eq_of_normalArg_eq (L M : HalfPlaneLine) (p : ℍ)
    (hpL : p∈L.carrier) (hpM : p∈M.carrier) (he : L.normalArg p=M.normalArg p) : L=M := by
  by_contra hne
  have hpos:=L.acuteAngle_pos M p hpL hpM hne
  rw [L.acuteAngle_eq_normalArg M p hpL hpM,he] at hpos
  simp [Real.pi_pos.le] at hpos


/-- Among n distinct actual concurrent axes, two meet at projective angle at most pi/n. -/
theorem HalfPlaneLine.concurrent_exists_small_acuteAngle {n : ℕ} (hn : 2≤n)
    (L : Fin n→HalfPlaneLine) (hL : Function.Injective L) (p : ℍ) (hp : ∀i,p∈(L i).carrier) :
    ∃i j:Fin n,i≠j ∧ (L i).acuteAngle (L j) p≤Real.pi/(n:ℝ) := by
  classical
  let f:Fin n→ℝ:=fun i=>(L i).normalArg p
  have hf : Function.Injective f := by
    intro i j he
    apply hL
    exact (L i).eq_of_normalArg_eq (L j) p (hp i) (hp j) he
  let S:=Finset.univ.image f
  have hcard : S.card=n := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  obtain ⟨x,hx,y,hy,hxy,hgap⟩:=real_projective_angle_pigeonhole S (by rwa [hcard]) Real.pi
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hy
  refine ⟨i,j,(fun he=>hxy (congrArg f he)),?_⟩
  rw [(L i).acuteAngle_eq_normalArg (L j) p (hp i) (hp j)]
  simpa only [hcard] using hgap

/-- Actual conjugate hyperbolic maps have the same actual metric translation length,
even when the conjugating map is given only in the original geometric group. -/
theorem hSL_translationLength_eq_of_isConj
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hConj : IsConj (realSLMobius A) (realSLMobius B)) :
    hTranslationLength (hSLIsometry A)=hTranslationLength (hSLIsometry B) := by
  obtain ⟨q,hq⟩:=isConj_iff.mp hConj
  have he : Mobius.mobiusSquaredTrace (realSLMobius A)=Mobius.mobiusSquaredTrace (realSLMobius B) := by
    rw [←hq,Mobius.mobiusSquaredTrace_conjugation]
  rw [realSLMobius_squaredTrace,realSLMobius_squaredTrace] at he
  have hr : (Matrix.trace A.val)^2=(Matrix.trace B.val)^2 := Complex.ofReal_injective he
  have habs : |Matrix.trace A.val|=|Matrix.trace B.val| :=
    (sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _)).mp (by simpa only [sq_abs] using hr)
  have hcosh : Real.cosh (hTranslationLength (hSLIsometry A)/2)=
      Real.cosh (hTranslationLength (hSLIsometry B)/2) := by
    rw [←hHyperbolic_translation_abs_trace A hA htA,←hHyperbolic_translation_abs_trace B hB htB,habs]
  have ha : 0≤hTranslationLength (hSLIsometry A)/2 := by linarith [hHyperbolic_translationLength_pos A hA htA]
  have hb : 0≤hTranslationLength (hSLIsometry B)/2 := by linarith [hHyperbolic_translationLength_pos B hB htB]
  have hh:=Real.cosh_strictMonoOn.injOn ha hb hcosh
  linarith

/-- The sharp concurrent-family bound from the actual pairwise commutator condition. -/
theorem hHyperbolic_concurrent_equal_length_bound {n : ℕ} (hn : 2≤n)
    (A : Fin n→Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀i,realSLMobius (A i)≠1) (htA : ∀i,4 < (Matrix.trace (A i).val)^2)
    (p : ℍ) (hp : ∀i,p∈(hHyperbolicAxis (A i) (hA i) (htA i)).carrier)
    (hAxes : Function.Injective (fun i=>hHyperbolicAxis (A i) (hA i) (htA i)))
    (T : ℝ) (hT : ∀i,hTranslationLength (hSLIsometry (A i))=T)
    (hcomm : ∀i j,i≠j→¬Mobius.MobiusElliptic (realSLMobius (A i*A j*(A i)⁻¹*(A j)⁻¹))) :
    1≤Real.sinh (T/2)^2*Real.sin (Real.pi/(n:ℝ)) := by
  let L:=fun i=>hHyperbolicAxis (A i) (hA i) (htA i)
  obtain ⟨i,j,hij,hsmall⟩:=HalfPlaneLine.concurrent_exists_small_acuteAngle hn L hAxes p hp
  let R:=(L i).rayAt p (hp i)
  let S:=(L j).rayAt p (hp j)
  have hR : R.supportLine=L i:=(L i).rayAt_support p (hp i)
  have hS : S.supportLine=L j:=(L j).rayAt_support p (hp j)
  have hRS : R.supportLine≠S.supportLine := by rw [hR,hS];exact hAxes.ne hij
  have hθ:=hInteriorAngleMeasure_pos R S hRS
  have hθπ:=hInteriorAngleMeasure_lt_pi R S hRS
  have hb:=hHyperbolic_commutator_intersection_bound (A i) (A j) (hA i) (hA j) (htA i) (htA j)
    R S hR hS hθ hθπ (hcomm i j hij)
  rw [hT i,hT j] at hb
  have hsin : Real.sin ((L i).acuteAngle (L j) p)=Real.sin (hInteriorAngleMeasure R S) := by
    rw [←hR,←hS,←R.acuteAngle_eq_support S,min_def]
    split_ifs <;> simp only [Real.sin_pi_sub]
  rw [←hsin] at hb
  have hnR : (2:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have htarget : Real.pi/(n:ℝ)≤Real.pi/2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num : (0:ℝ)<2) hnR
  have hs:=Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [(L i).acuteAngle_mem_Icc (L j) p |>.1] : -(Real.pi/2)≤(L i).acuteAngle (L j) p)
    htarget hsmall
  calc
    1≤Real.sinh (T/2)^2*Real.sin ((L i).acuteAngle (L j) p) := by nlinarith [hb]
    _≤Real.sinh (T/2)^2*Real.sin (Real.pi/(n:ℝ)) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)

/--
For an actual elliptic-free geometric group and actual conjugate hyperbolic maps.
The concurrent axes are pairwise distinct and n is at least two.
-/
theorem hFuchsian_concurrent_conjugate_hyperbolics_bound {n : ℕ} (hn : 2≤n)
    (G : Subgroup Mobius.complexMobiusGroup) (hG : ∀g∈G,¬Mobius.MobiusElliptic g)
    (A : Fin n→Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀i,realSLMobius (A i)≠1) (htA : ∀i,4 < (Matrix.trace (A i).val)^2)
    (hmem : ∀i,realSLMobius (A i)∈G)
    (hConj : ∀i j,IsConj (realSLMobius (A i)) (realSLMobius (A j)))
    (p : ℍ) (hp : ∀i,p∈(hHyperbolicAxis (A i) (hA i) (htA i)).carrier)
    (hAxes : Function.Injective (fun i=>hHyperbolicAxis (A i) (hA i) (htA i))) (i₀ : Fin n) :
    1≤Real.sinh (hTranslationLength (hSLIsometry (A i₀))/2)^2*Real.sin (Real.pi/(n:ℝ)) := by
  apply hHyperbolic_concurrent_equal_length_bound hn A hA htA p hp hAxes
  · intro i
    exact hSL_translationLength_eq_of_isConj (A i) (A i₀) (hA i) (hA i₀) (htA i) (htA i₀) (hConj i i₀)
  · intro i j _hij
    apply hG
    simpa only [map_mul,map_inv] using
      G.mul_mem (G.mul_mem (G.mul_mem (hmem i) (hmem j)) (G.inv_mem (hmem i))) (G.inv_mem (hmem j))

/-- A singleton axis cannot satisfy the stated concurrent-family conclusion. -/
theorem hConcurrent_single_axis_bound_fails (T : ℝ) :
    ¬1≤Real.sinh (T/2)^2*Real.sin (Real.pi/(1:ℝ)) := by
  norm_num

/-- Repeating a short actual dilation does not create a valid two-axis configuration. -/
theorem hConcurrent_duplicate_dilation_bound_value :
    Real.sinh (hTranslationLength (hSLIsometry (verticalDilationSL 4 (by norm_num)))/2)^2*
      Real.sin (Real.pi/2)=9/16 := by
  rw [dilation_translationLength,abs_of_pos (Real.log_pos (by norm_num : 1<(4:ℝ)))]
  have hlog : Real.log (4:ℝ)/2=Real.log 2 := by
    have h:=Real.log_pow (2:ℝ) 2
    norm_num at h
    linarith
  rw [hlog,Real.sinh_log (by norm_num : 0<(2:ℝ)),Real.sin_pi_div_two]
  norm_num

end LowDimensionalTopology.Geometry.Hyperbolic
