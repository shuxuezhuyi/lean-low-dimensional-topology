/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.HyperbolicProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.EllipticProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleCosineRule
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The exact real two-by-two trace identity, for arbitrary original determinant-one lifts. -/
theorem hSL_trace_product_add_inverse (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (A*B).val+Matrix.trace (A*B⁻¹).val=Matrix.trace A.val*Matrix.trace B.val := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  ring

/-- A genuine half-turn has inverse equal to its negative real lift. -/
theorem IsHalfTurnAt.inverse_eq_neg {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {p : ℍ}
    (h : IsHalfTurnAt A p) : A⁻¹= -A := by
  have ht:=(realSLMobius_order_two_iff_trace_zero A h.ne_one).mp h.1
  rw [Matrix.trace_fin_two] at ht
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.SpecialLinearGroup.coe_neg]
  all_goals linarith

/-- A half-turn's actual center is the unique elliptic center used by the native normal form. -/
theorem IsHalfTurnAt.center_eq {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {p : ℍ}
    (h : IsHalfTurnAt A p) :
    hEllipticCenter A ((realSLMobius_elliptic_iff A h.ne_one).mp h.elliptic)=p := by
  exact ((hSL_elliptic_fixed_iff A ((realSLMobius_elliptic_iff A h.ne_one).mp h.elliptic) p).mp h.2).symm

/-- The signed center coefficient of a true half-turn has magnitude one. -/
theorem IsHalfTurnAt.center_coefficient_abs {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {p : ℍ}
    (h : IsHalfTurnAt A p) : |A 1 0*p.im|=1 := by
  have hc:=hSL_elliptic_center_coefficients A h.elliptic
  rw [h.center_eq] at hc
  have ht:=(realSLMobius_order_two_iff_trace_zero A h.ne_one).mp h.1
  have he:=hc.2.2.2.1
  rw [ht] at he
  nlinarith [sq_abs (A 1 0*p.im),abs_nonneg (A 1 0*p.im)]

/-- The product trace of two actual half-turns is the signed cosine of their center distance. -/
theorem hHalfTurn_product_trace (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p q : ℍ)
    (hA : IsHalfTurnAt A p) (hB : IsHalfTurnAt B q) :
    Matrix.trace (A*B).val/2= -Real.cosh (dist p q)*(A 1 0*p.im)*(B 1 0*q.im) := by
  have he:=hSL_elliptic_product_trace A B hA.elliptic hB.elliptic
  rw [hA.center_eq,hB.center_eq,
    (realSLMobius_order_two_iff_trace_zero A hA.ne_one).mp hA.1,
    (realSLMobius_order_two_iff_trace_zero B hB.ne_one).mp hB.1] at he
  dsimp only at he
  nlinarith

/-- Three genuine half-turn centers give the exact absolute trace of the two resulting translations. -/
theorem hHalfTurn_four_product_abs_trace (P W U : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (p w u : ℍ) (hP : IsHalfTurnAt P p) (hW : IsHalfTurnAt W w) (hU : IsHalfTurnAt U u) :
    |Matrix.trace ((W*P)*(U*P)).val|/2=
      |2*Real.cosh (dist p w)*Real.cosh (dist p u)-Real.cosh (dist w u)| := by
  have ht:=hSL_trace_product_add_inverse (W*P) (U*P)
  have hi : (W*P)*(U*P)⁻¹=W*U⁻¹ := by group
  have hneg : (W* -U).val= -(W*U).val := by
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_neg,Matrix.mul_neg]
  rw [hi,hU.inverse_eq_neg,hneg,Matrix.trace_neg] at ht
  change Matrix.trace ((W*P)*(U*P)).val-Matrix.trace (W*U).val=
    Matrix.trace (W*P).val*Matrix.trace (U*P).val at ht
  have hWP:=hHalfTurn_product_trace W P w p hW hP
  have hUP:=hHalfTurn_product_trace U P u p hU hP
  have hWU:=hHalfTurn_product_trace W U w u hW hU
  rw [dist_comm w p] at hWP
  rw [dist_comm u p] at hUP
  have hsq : (P 1 0*p.im)^2=1 := by
    have he:=congrArg (fun x:ℝ=>x^2) hP.center_coefficient_abs
    simpa only [sq_abs,one_pow] using he
  have he : Matrix.trace ((W*P)*(U*P)).val/2=
      (W 1 0*w.im)*(U 1 0*u.im)*
      (2*Real.cosh (dist p w)*Real.cosh (dist p u)-Real.cosh (dist w u)) := by
    have hWP' : Matrix.trace (W*P).val=
        -2*Real.cosh (dist p w)*(W 1 0*w.im)*(P 1 0*p.im) := by linarith
    have hUP' : Matrix.trace (U*P).val=
        -2*Real.cosh (dist p u)*(U 1 0*u.im)*(P 1 0*p.im) := by linarith
    have hWU' : Matrix.trace (W*U).val=
        -2*Real.cosh (dist w u)*(W 1 0*w.im)*(U 1 0*u.im) := by linarith
    rw [hWP',hUP',hWU'] at ht
    have hprod : (-2*Real.cosh (dist p w)*(W 1 0*w.im)*(P 1 0*p.im))*
        (-2*Real.cosh (dist p u)*(U 1 0*u.im)*(P 1 0*p.im))=
        4*Real.cosh (dist p w)*Real.cosh (dist p u)*(W 1 0*w.im)*(U 1 0*u.im) := by
      calc
        _ = (4*Real.cosh (dist p w)*Real.cosh (dist p u)*(W 1 0*w.im)*(U 1 0*u.im))*
          (P 1 0*p.im)^2 := by ring
        _ = _ := by rw [hsq,mul_one]
    rw [hprod] at ht
    linear_combination ht/2
  have heabs:=congrArg abs he
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_mul,abs_mul,
    hW.center_coefficient_abs,hU.center_coefficient_abs,one_mul,one_mul] at heabs
  exact heabs

/-- The trace magnitude depends only on the actual geometric transformation. -/
theorem hSL_abs_trace_congr {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (he : realSLMobius A=realSLMobius B) : |Matrix.trace A.val|=|Matrix.trace B.val| := by
  rcases (realSLMobius_eq_iff_sign A B).mp he with he | he
  · rw [he]
  · rw [he,Matrix.SpecialLinearGroup.coe_neg,Matrix.trace_neg,abs_neg]

/-- An actual half-turn factorization at a common point gives the genuine forward-ray cosine formula. -/
theorem hHyperbolic_product_trace_of_halfTurn_factors
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p w u : ℍ)
    (hA : HasHalfTurnFactorization A p w) (hB : HasHalfTurnFactorization B p u)
    (hpw : p≠w) (hpu : p≠u) :
    |Matrix.trace (A*B).val|/2=
      |Real.cosh (dist p w)*Real.cosh (dist p u)+
      Real.sinh (dist p w)*Real.sinh (dist p u)*
        Real.cos (hInteriorAngleMeasure (hRayThrough p w hpw) (hRayThrough p u hpu))| := by
  obtain ⟨P,W,hP,hW,heA⟩:=hA
  obtain ⟨P',U,hP',hU,heB⟩:=hB
  have heP:=hP.unique hP'
  rw [←heP] at heB
  have he : realSLMobius (A*B)=realSLMobius ((W*P)*(U*P)) := by
    rw [map_mul,heA,heB,map_mul,map_mul,map_mul]
  rw [hSL_abs_trace_congr he,hHalfTurn_four_product_abs_trace P W U p w u hP hW hU]
  have hcos:=hInteriorAngleMeasure_cosine_rule (hRayThrough p w hpw) (hRayThrough p u hpu)
    (hRayThrough_mem p w hpw) hpw.symm (hRayThrough_mem p u hpu) hpu.symm
  rw [hcos]
  congr 1
  ring

/-- For two positive translation halves and a genuine nonstraight angle, the source product expression exceeds one. -/
theorem hHyperbolic_product_expression_gt_one (a b θ : ℝ) (ha : 0<a) (hb : 0<b)
    (hθ : 0<θ) (hθπ : θ<Real.pi) :
    1<Real.cosh a*Real.cosh b+Real.sinh a*Real.sinh b*Real.cos θ := by
  have hcos : -1<Real.cos θ := by
    have h:=Real.strictAntiOn_cos (show θ∈Icc 0 Real.pi from ⟨hθ.le,hθπ.le⟩)
      (show Real.pi∈Icc 0 Real.pi from ⟨Real.pi_pos.le,le_rfl⟩) hθπ
    simpa only [Real.cos_pi] using h
  have hs:=mul_pos (Real.sinh_pos_iff.mpr ha) (Real.sinh_pos_iff.mpr hb)
  have hc:=Real.one_le_cosh (a-b)
  rw [Real.cosh_sub] at hc
  nlinarith [mul_pos hs (by linarith : 0<1+Real.cos θ)]

/-- An original real transformation whose trace magnitude exceeds two is genuinely hyperbolic. -/
theorem hSL_hyperbolic_of_two_lt_abs_trace (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : 2 < |Matrix.trace A.val|) : Mobius.MobiusHyperbolic (realSLMobius A) := by
  have hs : 4<(Matrix.trace A.val)^2 := by nlinarith [sq_abs (Matrix.trace A.val)]
  have hn : realSLMobius A≠1 := by intro hi;have he:=hSL_trace_sq_of_projection_one A hi;linarith
  exact (realSLMobius_hyperbolic_iff A hn).mpr hs


/-- Genuine attracting endpoints are unique, with uniqueness proved from the actual orbit limits. -/
theorem hHyperbolic_attractive_fixedPoint_unique
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ht : 4<(Matrix.trace A.val)^2)
    {a b : Mobius.ExtendedComplex} (ha : Mobius.MobiusAttractiveFixedPoint (realSLMobius A) a)
    (hb : Mobius.MobiusAttractiveFixedPoint (realSLMobius A) b) : a=b := by
  obtain ⟨r,hr⟩:=ha
  obtain ⟨s,hs⟩:=hb
  have hn (q : Mobius.ExtendedComplex) (hq : (realSLMobius A).val q=q) :
      (((UpperHalfPlane.I:ℍ):ℂ):Mobius.ExtendedComplex)≠q := by
    intro he
    rw [←he] at hq
    have hh:=realSLMobius_hyperbolic_fixed_im A ht (UpperHalfPlane.I:ℂ) hq
    simp at hh
  exact tendsto_nhds_unique (hr.2.2.2.1 _ (hn r hr.2.2.1))
    (hs.2.2.2.1 _ (hn s hs.2.2.1))

/-- Exact trace pairing for the genuine attractive rays at a common actual axis point. -/
theorem hHyperbolic_attractive_rays_trace
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (p : ℍ) (hpA : p∈(hHyperbolicAxis A hA htA).carrier)
    (hpB : p∈(hHyperbolicAxis B hB htB).carrier)
    (R S : HRayAt p)
    (hR : Mobius.MobiusAttractiveFixedPoint (realSLMobius A) R.idealEndpoint)
    (hS : Mobius.MobiusAttractiveFixedPoint (realSLMobius B) S.idealEndpoint) :
    R.supportLine=hHyperbolicAxis A hA htA ∧ S.supportLine=hHyperbolicAxis B hB htB ∧
    |Matrix.trace (A*B).val|/2=
      |Real.cosh (hTranslationLength (hSLIsometry A)/2)*Real.cosh (hTranslationLength (hSLIsometry B)/2)+
      Real.sinh (hTranslationLength (hSLIsometry A)/2)*Real.sinh (hTranslationLength (hSLIsometry B)/2)*
        Real.cos (hInteriorAngleMeasure R S)| := by
  obtain ⟨w,⟨hw,hAw,hTA⟩,_⟩:=realSL_hyperbolic_halfturn_factor A hA htA p hpA
  obtain ⟨u,⟨hu,hBu,hTB⟩,_⟩:=realSL_hyperbolic_halfturn_factor B hB htB p hpB
  have hpw : p≠w := by
    intro he
    rw [←he,dist_self,mul_zero] at hTA
    have hh:=hHyperbolic_translationLength_pos A hA htA
    linarith
  have hpu : p≠u := by
    intro he
    rw [←he,dist_self,mul_zero] at hTB
    have hh:=hHyperbolic_translationLength_pos B hB htB
    linarith
  let R':=hRayThrough p w hpw
  let S':=hRayThrough p u hpu
  have hReq : R=R' := HRayAt.idealEndpoint_injective p
    (hHyperbolic_attractive_fixedPoint_unique A htA hR
      (realSL_hyperbolic_halfturn_ray_attractive A hA htA p w hpw hpA hAw))
  have hSeq : S=S' := HRayAt.idealEndpoint_injective p
    (hHyperbolic_attractive_fixedPoint_unique B htB hS
      (realSL_hyperbolic_halfturn_ray_attractive B hB htB p u hpu hpB hBu))
  rw [hReq,hSeq]
  have hRL : R'.supportLine=hHyperbolicAxis A hA htA :=
    R'.supportLine.eq_of_two_points _ hpw R'.start_mem_support
      (R'.subset_support (hRayThrough_mem p w hpw)) hpA hw
  have hSM : S'.supportLine=hHyperbolicAxis B hB htB :=
    S'.supportLine.eq_of_two_points _ hpu S'.start_mem_support
      (S'.subset_support (hRayThrough_mem p u hpu)) hpB hu
  have hhalfA : hTranslationLength (hSLIsometry A)/2=dist p w := by linarith
  have hhalfB : hTranslationLength (hSLIsometry B)/2=dist p u := by linarith
  have htrace:=hHyperbolic_product_trace_of_halfTurn_factors A B p w u hAw hBu hpw hpu
  rw [←hhalfA,←hhalfB] at htrace
  exact ⟨hRL,hSM,htrace⟩

/--
The actual attractive-ray angle and actual translation lengths determine
an intersecting-axis product, which is genuinely hyperbolic.
-/
theorem hHyperbolic_intersecting_product_trace
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (p : ℍ) (hpA : p∈(hHyperbolicAxis A hA htA).carrier)
    (hpB : p∈(hHyperbolicAxis B hB htB).carrier)
    (R S : HRayAt p)
    (hR : Mobius.MobiusAttractiveFixedPoint (realSLMobius A) R.idealEndpoint)
    (hS : Mobius.MobiusAttractiveFixedPoint (realSLMobius B) S.idealEndpoint)
    (hθ : 0<hInteriorAngleMeasure R S) (hθπ : hInteriorAngleMeasure R S<Real.pi) :
    Mobius.MobiusHyperbolic (realSLMobius (A*B)) ∧
    |Matrix.trace (A*B).val|/2=
      Real.cosh (hTranslationLength (hSLIsometry A)/2)*Real.cosh (hTranslationLength (hSLIsometry B)/2)+
      Real.sinh (hTranslationLength (hSLIsometry A)/2)*Real.sinh (hTranslationLength (hSLIsometry B)/2)*
        Real.cos (hInteriorAngleMeasure R S) := by
  obtain ⟨_,_,htrace⟩:=hHyperbolic_attractive_rays_trace A B hA hB htA htB p hpA hpB R S hR hS
  have hgt:=hHyperbolic_product_expression_gt_one
    (hTranslationLength (hSLIsometry A)/2) (hTranslationLength (hSLIsometry B)/2)
    (hInteriorAngleMeasure R S)
    (by linarith [hHyperbolic_translationLength_pos A hA htA])
    (by linarith [hHyperbolic_translationLength_pos B hB htB]) hθ hθπ
  rw [abs_of_pos (lt_trans zero_lt_one hgt)] at htrace
  exact ⟨hSL_hyperbolic_of_two_lt_abs_trace (A*B) (by linarith [htrace]),htrace⟩

end LowDimensionalTopology.Geometry.Hyperbolic
