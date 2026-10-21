/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.AngleDomains
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! # Actual forward Euclidean tangents of genuine hyperbolic rays -/

@[expose] public section
open Set Filter
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- A Euclidean tangent is forward when an actual differentiable curve realizes it
and all sufficiently short positive parameters lie on the genuine punctured ray. -/
def IsForwardRayTangent (R : Set ℍ) (z : ℍ) (v : ℂ) : Prop :=
  v ≠ 0 ∧ ∃ c : ℝ → ℂ, HasDerivAt c v 0 ∧ c 0 = (z : ℂ) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (0 : ℝ) ε,
      ∃ w : ℍ, w ∈ R \ {z} ∧ (w : ℂ) = c t

/-- This coordinate is globally injective along the actual H geodesic, and its
canonical Euclidean tangent derivative is positive. -/
def HalfPlaneLine.longitudinal : HalfPlaneLine → ℂ →L[ℝ] ℝ
  | .vertical _ => Complex.imCLM
  | .circle _ _ _ => -Complex.reCLM

theorem HalfPlaneLine.longitudinal_injective_on_carrier (L : HalfPlaneLine) {x y : ℍ}
    (hx : x ∈ L.carrier) (hy : y ∈ L.carrier)
    (hxy : L.longitudinal (x : ℂ) = L.longitudinal (y : ℂ)) : x = y := by
  cases L with
  | vertical a =>
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hx.trans hy.symm
    · exact hxy
  | circle c r hr =>
    have hre : x.re = y.re := by
      change -(x : ℂ).re = -(y : ℂ).re at hxy
      simp only [UpperHalfPlane.coe_re] at hxy
      linarith
    exact eq_of_circle_mem_of_re_eq hx hy hre

theorem HalfPlaneLine.longitudinal_tangent_pos (L : HalfPlaneLine) (z : ℍ) :
    0 < L.longitudinal (L.tangentAt z) := by
  cases L with
  | vertical a => norm_num [HalfPlaneLine.longitudinal,HalfPlaneLine.tangentAt]
  | circle c r hr =>
    simpa only [HalfPlaneLine.longitudinal,neg_apply,Complex.reCLM_apply,
      HalfPlaneLine.tangentAt,Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,
      Complex.sub_im,Complex.ofReal_im,sub_zero,one_mul,zero_sub,neg_neg,
      UpperHalfPlane.coe_im] using z.im_pos

/-- An injective continuous scalar coordinate on a complete genuine support line
recovers the ray's actual forward order from any genuine point of the punctured ray. -/
theorem HRayAt.mem_iff_scalar_order {z : ℍ} (R : HRayAt z) (φ : ℍ → ℝ) (hc : Continuous φ)
    (hi : Set.InjOn φ R.supportLine.carrier) {x : ℍ} (hx : x ∈ R.supportLine.carrier) :
    x ∈ R.val ↔ if φ z < φ R.directionPoint then φ z ≤ φ x else φ x ≤ φ z := by
  classical
  obtain ⟨a,b,γ,s,_,_,hγ,hrange,hs,_,_,_,_⟩ := R.supportLine.exists_rays_at z R.start_mem_support
  have hor := R.isRay.eq_one_of_rays_at R.supportLine R.start_mem_support
    R.ideal_mem_support γ hγ.1 hrange s hs
  have hγline (t : ℝ) : γ t ∈ R.supportLine.carrier := hrange ▸ mem_range_self t
  have hqi : Function.Injective (φ ∘ γ) := fun u v huv => hγ.1.injective (hi (hγline u) (hγline v) huv)
  obtain ⟨u,hu⟩ : R.directionPoint ∈ range γ := hrange.symm ▸ (R.subset_support R.directionPoint_mem.1)
  obtain ⟨r,hr⟩ : x ∈ range γ := hrange.symm ▸ hx
  have hus : u ≠ s := by
    intro he
    exact R.directionPoint_mem.2 (hu.symm.trans ((congrArg γ he).trans hs))
  have hγmem (T : Set ℝ) (t : ℝ) : γ t ∈ γ '' T ↔ t ∈ T := by
    constructor
    · rintro ⟨v,hv,he⟩
      exact hγ.1.injective he ▸ hv
    · intro ht
      exact mem_image_of_mem γ ht
  rcases (hc.comp hγ.1.continuous).strictMono_of_inj hqi with hmono | hanti
  · rcases hor with hor | hor
    · have hsu : s < u := by
        have huR := R.directionPoint_mem.1
        rw [hor,← hu] at huR
        exact lt_of_le_of_ne ((hγmem (Ici s) u).mp huR) (Ne.symm hus)
      have hdir : φ z < φ R.directionPoint := by
        have he := hmono hsu
        change φ (γ s) < φ (γ u) at he
        rwa [hs,hu] at he
      rw [ite_eq_left hdir,hor,forwardHLineRay,← hr,hγmem]
      change s ≤ r ↔ φ z ≤ φ (γ r)
      rw [← hs]
      exact hmono.le_iff_le.symm
    · have hus' : u < s := by
        have huR := R.directionPoint_mem.1
        rw [hor,← hu] at huR
        exact lt_of_le_of_ne ((hγmem (Iic s) u).mp huR) hus
      have hdir : ¬ φ z < φ R.directionPoint := by
        have he := hmono hus'
        change φ (γ u) < φ (γ s) at he
        rw [hu,hs] at he
        exact not_lt.mpr he.le
      rw [ite_eq_right hdir,hor,backwardHLineRay,← hr,hγmem]
      change r ≤ s ↔ φ (γ r) ≤ φ z
      rw [← hs]
      exact hmono.le_iff_le.symm
  · rcases hor with hor | hor
    · have hsu : s < u := by
        have huR := R.directionPoint_mem.1
        rw [hor,← hu] at huR
        exact lt_of_le_of_ne ((hγmem (Ici s) u).mp huR) (Ne.symm hus)
      have hdir : ¬ φ z < φ R.directionPoint := by
        have he := hanti hsu
        change φ (γ u) < φ (γ s) at he
        rw [hu,hs] at he
        exact not_lt.mpr he.le
      rw [ite_eq_right hdir,hor,forwardHLineRay,← hr,hγmem]
      change s ≤ r ↔ φ (γ r) ≤ φ z
      rw [← hs]
      constructor
      · intro h
        exact hanti.antitone h
      · intro he
        by_contra! hrs
        have hlt := hanti hrs
        exact (not_lt.mpr he) hlt
    · have hus' : u < s := by
        have huR := R.directionPoint_mem.1
        rw [hor,← hu] at huR
        exact lt_of_le_of_ne ((hγmem (Iic s) u).mp huR) hus
      have hdir : φ z < φ R.directionPoint := by
        have he := hanti hus'
        change φ (γ s) < φ (γ u) at he
        rwa [hs,hu] at he
      rw [ite_eq_left hdir,hor,backwardHLineRay,← hr,hγmem]
      change r ≤ s ↔ φ z ≤ φ (γ r)
      rw [← hs]
      constructor
      · intro h
        exact hanti.antitone h
      · intro he
        by_contra! hsr
        have hlt := hanti hsr
        exact (not_lt.mpr he) hlt

def HRayAt.longitudinal {z : ℍ} (R : HRayAt z) (x : ℍ) : ℝ := R.supportLine.longitudinal (x : ℂ)

theorem HRayAt.longitudinal_continuous {z : ℍ} (R : HRayAt z) : Continuous R.longitudinal :=
  R.supportLine.longitudinal.continuous.comp UpperHalfPlane.continuous_coe

theorem HRayAt.longitudinal_tip_ne {z : ℍ} (R : HRayAt z) : R.longitudinal R.directionPoint ≠ R.longitudinal z := by
  intro he
  exact R.directionPoint_mem.2 (R.supportLine.longitudinal_injective_on_carrier
    (R.subset_support R.directionPoint_mem.1) R.start_mem_support he)

theorem HRayAt.mem_iff_longitudinal {z : ℍ} (R : HRayAt z) {x : ℍ}
    (hx : x ∈ R.supportLine.carrier) :
    x ∈ R.val ↔ if R.longitudinal z < R.longitudinal R.directionPoint
      then R.longitudinal z ≤ R.longitudinal x else R.longitudinal x ≤ R.longitudinal z :=
  R.mem_iff_scalar_order R.longitudinal R.longitudinal_continuous
    (fun _ hx _ hy he => R.supportLine.longitudinal_injective_on_carrier hx hy he) hx

def HRayAt.tangentSign {z : ℍ} (R : HRayAt z) : ℝ := by
  classical
  exact if R.longitudinal z < R.longitudinal R.directionPoint then 1 else -1

theorem HRayAt.tangentSign_ne_zero {z : ℍ} (R : HRayAt z) : R.tangentSign ≠ 0 := by
  classical
  unfold HRayAt.tangentSign
  split_ifs <;> norm_num

theorem HRayAt.tangentSign_sq {z : ℍ} (R : HRayAt z) : R.tangentSign ^ 2 = 1 := by
  classical
  unfold HRayAt.tangentSign
  split_ifs <;> norm_num

/-- The oriented actual Euclidean tangent of the supporting circle or vertical line. -/
def HRayAt.tangentVector {z : ℍ} (R : HRayAt z) : ℂ := R.tangentSign • R.supportLine.tangentAt z

theorem HRayAt.tangentVector_ne_zero {z : ℍ} (R : HRayAt z) : R.tangentVector ≠ 0 :=
  smul_ne_zero R.tangentSign_ne_zero (R.supportLine.tangentAt_ne_zero z)

/-- An actual analytic circle/line curve, with orientation determined by the genuine ray. -/
def HRayAt.euclideanTangentCurve {z : ℍ} (R : HRayAt z) (t : ℝ) : ℂ :=
  R.supportLine.tangentCurve z (R.tangentSign * t)

theorem HRayAt.euclideanTangentCurve_zero {z : ℍ} (R : HRayAt z) :
    R.euclideanTangentCurve 0 = (z : ℂ) := by
  change R.supportLine.tangentCurve z (R.tangentSign * 0) = (z : ℂ)
  rw [mul_zero,HalfPlaneLine.tangentCurve_zero]

theorem HRayAt.euclideanTangentCurve_hasDerivAt {z : ℍ} (R : HRayAt z) :
    HasDerivAt R.euclideanTangentCurve R.tangentVector 0 := by
  have he : R.tangentSign * (0 : ℝ) = 0 := mul_zero _
  have hcurve := R.supportLine.tangentCurve_hasDerivAt z
  rw [← he] at hcurve
  have hlin : HasDerivAt (fun t : ℝ => R.tangentSign * t) R.tangentSign 0 := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul R.tangentSign
  exact hcurve.scomp 0 hlin

theorem derivative_pos_eventually_increases {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0) (hd : 0 < d) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), g 0 < g t := by
  have hs := hg.tendsto_slope_zero_right.eventually (Ioi_mem_nhds hd)
  filter_upwards [hs,self_mem_nhdsWithin] with t ht htpos
  change 0 < t at htpos
  change 0 < t⁻¹ * (g (0 + t) - g 0) at ht
  rw [zero_add] at ht
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (inv_pos.mpr htpos)).mp ht)

theorem HRayAt.euclideanTangentCurve_support {z : ℍ} (R : HRayAt z) (t : ℝ) (w : ℍ)
    (hw : (w : ℂ) = R.euclideanTangentCurve t) : w ∈ R.supportLine.carrier := by
  have hz := R.start_mem_support
  cases hL : R.supportLine with
  | vertical a =>
    rw [hL] at hz
    change w.re = a
    change z.re = a at hz
    have he := congrArg Complex.re hw
    rw [HRayAt.euclideanTangentCurve,hL,HalfPlaneLine.tangentCurve] at he
    simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,
      UpperHalfPlane.coe_re] at he
    exact he.trans hz
  | circle c r hr =>
    rw [hL] at hz
    change ‖(w : ℂ) - (c : ℂ)‖ = r
    rw [hw,HRayAt.euclideanTangentCurve,hL]
    exact tangentCurve_circle_norm c r hr z hz (R.tangentSign * t)

/-- This verifies the orientation against the actual ray point set, not merely
against an arbitrarily chosen tangent line. -/
theorem HRayAt.tangentVector_isForward {z : ℍ} (R : HRayAt z) :
    IsForwardRayTangent R.val z R.tangentVector := by
  let c := R.euclideanTangentCurve
  let f := R.supportLine.longitudinal
  have hc := R.euclideanTangentCurve_hasDerivAt
  have hc0 := R.euclideanTangentCurve_zero
  have hf : HasDerivAt (fun t : ℝ => f (c t))
      (R.tangentSign * f (R.supportLine.tangentAt z)) 0 := by
    have he := f.hasFDerivAt.comp_hasDerivAt 0 hc
    convert! he using 1
    simp only [HRayAt.tangentVector,map_smul,smul_eq_mul]
  have hf0 : f (c 0) = R.longitudinal z := congrArg f hc0
  have him : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (c t).im := by
    have hi : ContinuousAt (fun t : ℝ => (c t).im) 0 :=
      Complex.continuous_im.continuousAt.comp hc.continuousAt
    have h0 : 0 < (c 0).im := by
      change 0 < (R.euclideanTangentCurve 0).im
      rw [hc0]
      exact z.im_pos
    exact (hi.eventually (Ioi_mem_nhds h0)).filter_mono nhdsWithin_le_nhds
  have hside : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      if R.longitudinal z < R.longitudinal R.directionPoint
      then R.longitudinal z < f (c t) else f (c t) < R.longitudinal z := by
    classical
    by_cases hdir : R.longitudinal z < R.longitudinal R.directionPoint
    · have hs : R.tangentSign = 1 := by simp only [HRayAt.tangentSign,ite_eq_left hdir]
      have hd : 0 < R.tangentSign * f (R.supportLine.tangentAt z) := by
        rw [hs,one_mul]
        exact R.supportLine.longitudinal_tangent_pos z
      have he := derivative_pos_eventually_increases hf hd
      simpa only [ite_eq_left hdir,hf0] using he
    · have hs : R.tangentSign = -1 := by simp only [HRayAt.tangentSign,ite_eq_right hdir]
      have hd : 0 < -(R.tangentSign * f (R.supportLine.tangentAt z)) := by
        rw [hs,neg_one_mul,neg_neg]
        exact R.supportLine.longitudinal_tangent_pos z
      have he := derivative_pos_eventually_increases hf.neg hd
      filter_upwards [he] with t ht
      rw [ite_eq_right hdir]
      change -f (c 0) < -f (c t) at ht
      rw [hf0] at ht
      linarith
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∃ w : ℍ, w ∈ R.val \ {z} ∧ (w : ℂ) = c t := by
    filter_upwards [him,hside] with t htIm htSide
    let w : ℍ := ⟨c t,htIm⟩
    have hwS : w ∈ R.supportLine.carrier := R.euclideanTangentCurve_support t w rfl
    have hwR : w ∈ R.val := by
      apply (R.mem_iff_longitudinal hwS).mpr
      classical
      by_cases hdir : R.longitudinal z < R.longitudinal R.directionPoint
      · rw [ite_eq_left hdir] at htSide ⊢
        exact htSide.le
      · rw [ite_eq_right hdir] at htSide ⊢
        exact htSide.le
    have hwne : w ≠ z := by
      intro hwz
      have hφ : f (c t) = R.longitudinal z := congrArg (fun u : ℍ => R.longitudinal u) hwz
      classical
      by_cases hdir : R.longitudinal z < R.longitudinal R.directionPoint
      · rw [ite_eq_left hdir,hφ] at htSide
        exact lt_irrefl _ htSide
      · rw [ite_eq_right hdir,hφ] at htSide
        exact lt_irrefl _ htSide
    exact ⟨w,⟨hwR,hwne⟩,rfl⟩
  obtain ⟨ε,hε,hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  exact ⟨R.tangentVector_ne_zero,c,hc,hc0,ε,hε,fun t ht => hsub ht⟩

/-- Through a genuine interior point, an actual tangent line determines the full H h-line. -/
theorem HalfPlaneLine.eq_of_tangent_smul (L M : HalfPlaneLine) (z : ℍ)
    (hzL : z ∈ L.carrier) (hzM : z ∈ M.carrier) (r : ℝ)
    (he : M.tangentAt z = r • L.tangentAt z) : L = M := by
  cases L with
  | vertical a =>
    cases M with
    | vertical b =>
      have hab : a = b := hzL.symm.trans hzM
      exact congrArg HalfPlaneLine.vertical hab
    | circle c ρ hρ =>
      have hre := congrArg Complex.re he
      norm_num [HalfPlaneLine.tangentAt,Complex.real_smul,Complex.mul_re] at hre
      linarith [z.im_pos]
  | circle c ρ hρ =>
    cases M with
    | vertical a =>
      have hre := congrArg Complex.re he
      have him := congrArg Complex.im he
      norm_num [HalfPlaneLine.tangentAt,Complex.real_smul,Complex.mul_re,Complex.mul_im] at hre him
      have hr : r = 0 := hre.resolve_right (ne_of_gt z.im_pos)
      subst r
      norm_num at him
    | circle d σ hσ =>
      have hre := congrArg Complex.re he
      have him := congrArg Complex.im he
      norm_num [HalfPlaneLine.tangentAt,Complex.real_smul,Complex.mul_re,Complex.mul_im] at hre him
      have hm : (r - 1) * z.im = 0 := by nlinarith
      have hr : r = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (ne_of_gt z.im_pos))
      subst r
      have hcd : c = d := by linarith
      subst d
      change ‖(z : ℂ) - (c : ℂ)‖ = ρ at hzL
      change ‖(z : ℂ) - (c : ℂ)‖ = σ at hzM
      have hρσ : ρ = σ := hzL.symm.trans hzM
      cases hρσ
      rfl

theorem HRayAt.tangentSign_smul_vector {z : ℍ} (R : HRayAt z) :
    R.tangentSign • R.tangentVector = R.supportLine.tangentAt z := by
  rw [HRayAt.tangentVector,smul_smul,← pow_two,R.tangentSign_sq,one_smul]

theorem HRayAt.support_eq_of_tangent_smul {z : ℍ} (R S : HRayAt z) (r : ℝ)
    (he : S.tangentVector = r • R.tangentVector) : R.supportLine = S.supportLine := by
  have ht : S.supportLine.tangentAt z =
      (S.tangentSign * r * R.tangentSign) • R.supportLine.tangentAt z := by
    calc
      S.supportLine.tangentAt z = S.tangentSign • S.tangentVector := S.tangentSign_smul_vector.symm
      _ = S.tangentSign • (r • R.tangentVector) := congrArg (fun v : ℂ => S.tangentSign • v) he
      _ = (S.tangentSign * r * R.tangentSign) • R.supportLine.tangentAt z := by
        rw [HRayAt.tangentVector,smul_smul,smul_smul]
  exact R.supportLine.eq_of_tangent_smul S.supportLine z R.start_mem_support S.start_mem_support _ ht

/-- Actual forward tangent vectors of a proper genuine ray angle are linearly independent. -/
theorem HRayAt.tangents_linearIndependent {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : LinearIndependent ℝ ![R.tangentVector,S.tangentVector] := by
  apply linearIndependent_fin2.mpr
  refine ⟨S.tangentVector_ne_zero,?_⟩
  intro r he
  exact hne (S.support_eq_of_tangent_smul R r he.symm).symm

end
end LowDimensionalTopology.Geometry.Hyperbolic
