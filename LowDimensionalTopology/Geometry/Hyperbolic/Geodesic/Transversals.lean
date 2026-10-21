/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.TransversalAngles

/-!
# Actual four-transversal classification
-/
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem acute_parameter_cos_bounds (θ : ℝ) (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    0<Real.cos θ ∧ Real.cos θ<1 := by
  constructor
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθ⟩
  · have hh:=Real.strictAntiOn_cos ⟨by positivity,Real.pi_pos.le⟩
      ⟨h0.le,by linarith [Real.pi_pos]⟩ h0
    simpa only [Real.cos_zero] using hh

theorem equal_circle_angle_coefficients (s t a u C : ℝ) (hs : 0<s) (ht : 0<t)
    (hst : s≠t) (hu : 0<u) (hC : 0<C)
    (h1 : |s^2+u^2-a^2|/(2*s*u)=C) (h2 : |t^2+u^2-a^2|/(2*t*u)=C) :
    (u^2-a^2=s*t ∧ u=(s+t)/(2*C)) ∨
      (u^2-a^2= -(s*t) ∧ u=|s-t|/(2*C)) := by
  have h1' :=(div_eq_iff (by positivity : 2*s*u≠0)).mp h1
  have h2' :=(div_eq_iff (by positivity : 2*t*u≠0)).mp h2
  have he : |s^2+u^2-a^2| *t=|t^2+u^2-a^2| *s := by rw [h1',h2']; ring
  have he2:=congrArg (fun x : ℝ=>x^2) he
  rw [mul_pow,mul_pow,sq_abs,sq_abs] at he2
  have hf : (t^2-s^2)*((u^2-a^2)^2-(s*t)^2)=0 := by nlinarith only [he2]
  have hne : t^2-s^2≠0 := by intro h;apply hst;nlinarith
  have hd :=(mul_eq_zero.mp hf).resolve_left hne
  have hd' : (u^2-a^2)^2=(s*t)^2:=sub_eq_zero.mp hd
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hd' with hd' | hd'
  · left
    refine ⟨hd',?_⟩
    have hh : |s^2+u^2-a^2|=s*(s+t) := by
      rw [show s^2+u^2-a^2=s*(s+t) by nlinarith only [hd'],abs_of_pos (by positivity)]
    rw [hh] at h1'
    apply (eq_div_iff (by positivity : 2*C≠0)).mpr
    apply mul_left_cancel₀ hs.ne'
    nlinarith only [h1']
  · right
    refine ⟨hd',?_⟩
    have hh : |s^2+u^2-a^2|=s*|s-t| := by
      rw [show s^2+u^2-a^2=s*(s-t) by nlinarith only [hd'],abs_mul,abs_of_pos hs]
    rw [hh] at h1'
    apply (eq_div_iff (by positivity : 2*C≠0)).mpr
    apply mul_left_cancel₀ hs.ne'
    nlinarith only [h1']

/-- Genuine circle intersection and actual acute tangent angle from its exact coefficients. -/
theorem circle_intersection_of_acute_coefficient (s a u θ : ℝ) (hs : 0<s) (hu : 0<u)
    (h0 : 0<θ) (hθ : θ<Real.pi/2)
    (hC : |s^2+u^2-a^2|/(2*s*u)=Real.cos θ) :
    ∃p : ℍ,p∈(HalfPlaneLine.circle 0 s hs).carrier ∧
      p∈(HalfPlaneLine.circle a u hu).carrier ∧
      (HalfPlaneLine.circle 0 s hs).acuteAngle (.circle a u hu) p=θ := by
  have hc:=acute_parameter_cos_bounds θ h0 hθ
  have habs : |s^2+u^2-a^2|<2*s*u :=
    (div_lt_one (by positivity : 0<2*s*u)).mp (hC.trans_lt hc.2)
  have hsq : (s^2+u^2-a^2)^2<(2*s*u)^2 := by
    nlinarith [sq_abs (s^2+u^2-a^2),abs_nonneg (s^2+u^2-a^2)]
  have ha : a≠0 := by
    intro he
    rw [he] at hsq
    nlinarith [sq_nonneg (s^2-u^2)]
  let x:=(s^2+a^2-u^2)/(2*a)
  have hx : x*(2*a)=s^2+a^2-u^2 := by
    dsimp [x]
    exact div_mul_cancel₀ _ (by exact mul_ne_zero (by norm_num) ha)
  have hxx : x^2*(2*a)^2=(s^2+a^2-u^2)^2 := by
    rw [←mul_pow,hx]
  have hy : 0<s^2-x^2 := by
    have he : (s^2-x^2)*(2*a)^2>0 := by nlinarith only [hsq,hxx]
    exact pos_of_mul_pos_left he (sq_nonneg _)
  let y:=Real.sqrt (s^2-x^2)
  have hy0 : 0<y:=Real.sqrt_pos.mpr hy
  have hy2 : y^2=s^2-x^2:=Real.sq_sqrt hy.le
  let p : ℍ:=⟨(x : ℂ)+(y : ℂ)*Complex.I,by simpa using hy0⟩
  have hpRe : p.re=x:=by simp [p]
  have hpIm : p.im=y:=by simp [p]
  have hp : p∈(HalfPlaneLine.circle 0 s hs).carrier := by
    apply norm_sub_real_eq_of_sq hs
    rw [hpRe,hpIm]
    nlinarith only [hy2]
  have hq : p∈(HalfPlaneLine.circle a u hu).carrier := by
    apply norm_sub_real_eq_of_sq hu
    rw [hpRe,hpIm]
    nlinarith only [hx,hy2]
  refine ⟨p,hp,hq,?_⟩
  have hcos : Real.cos ((HalfPlaneLine.circle 0 s hs).acuteAngle (.circle a u hu) p)=Real.cos θ := by
    rw [circle_circle_acuteAngle_cos 0 s a u hs hu p hp hq,zero_sub,neg_sq]
    exact hC
  have hA:=(HalfPlaneLine.circle 0 s hs).acuteAngle_mem_Icc (.circle a u hu) p
  exact Real.injOn_cos ⟨hA.1,by linarith [hA.2,Real.pi_pos]⟩
    ⟨h0.le,by linarith [Real.pi_pos]⟩ hcos


theorem concentric_transversal_iff_coefficients (s t : ℝ) (hs : 0<s) (ht : 0<t)
    (hst : s≠t) (θ : ℝ) (h0 : 0<θ) (hθ : θ<Real.pi/2) (N : HalfPlaneLine) :
    (HalfPlaneLine.circle 0 s hs).IsThetaTransversal (.circle 0 t ht) θ N ↔
      ∃(a u : ℝ) (hu : 0<u),N=HalfPlaneLine.circle a u hu ∧
        |s^2+u^2-a^2|/(2*s*u)=Real.cos θ ∧ |t^2+u^2-a^2|/(2*t*u)=Real.cos θ := by
  constructor
  · rintro ⟨_,_,p,q,hpL,hpN,hqM,hqN,hp,hq⟩
    cases N with
    | vertical a =>
      have hpRe : p.re=a:=hpN
      have hqRe : q.re=a:=hqN
      have hsC : |a|/s=Real.cos θ := by
        rw [←hp,(HalfPlaneLine.circle 0 s hs).acuteAngle_comm,
          vertical_circle_acuteAngle_cos a 0 s hs p hpL,hpRe,sub_zero]
      have htC : |a|/t=Real.cos θ := by
        rw [←hq,(HalfPlaneLine.circle 0 t ht).acuteAngle_comm,
          vertical_circle_acuteAngle_cos a 0 t ht q hqM,hqRe,sub_zero]
      have he1:=(div_eq_iff hs.ne').mp hsC
      have he2:=(div_eq_iff ht.ne').mp htC
      exfalso
      apply hst
      exact mul_left_cancel₀ (acute_parameter_cos_bounds θ h0 hθ).1.ne' (he1.symm.trans he2)
    | circle a u hu =>
      refine ⟨a,u,hu,rfl,?_,?_⟩
      · rw [←hp,circle_circle_acuteAngle_cos 0 s a u hs hu p hpL hpN,zero_sub,neg_sq]
      · rw [←hq,circle_circle_acuteAngle_cos 0 t a u ht hu q hqM hqN,zero_sub,neg_sq]
  · rintro ⟨a,u,hu,rfl,h1,h2⟩
    obtain ⟨p,hpL,hpN,hp⟩:=circle_intersection_of_acute_coefficient s a u θ hs hu h0 hθ h1
    obtain ⟨q,hqM,hqN,hq⟩:=circle_intersection_of_acute_coefficient t a u θ ht hu h0 hθ h2
    exact ⟨h0,hθ.le,p,q,hpL,hpN,hqM,hqN,hp,hq⟩

theorem circle_angle_coefficients_of_alternate (s t a u C : ℝ) (hs : 0<s) (ht : 0<t)
    (hC : 0<C) (hD : u^2-a^2=s*t) (hu : u=(s+t)/(2*C)) :
    |s^2+u^2-a^2|/(2*s*u)=C ∧ |t^2+u^2-a^2|/(2*t*u)=C := by
  have hu0 : 0<u:=by rw [hu];positivity
  have he : u*(2*C)=s+t:=(eq_div_iff (by positivity : 2*C≠0)).mp hu
  constructor
  · apply (div_eq_iff (by positivity : 2*s*u≠0)).mpr
    rw [show s^2+u^2-a^2=s*(s+t) by nlinarith only [hD],abs_of_pos (by positivity)]
    nlinarith only [congrArg (fun x : ℝ=>s*x) he]
  · apply (div_eq_iff (by positivity : 2*t*u≠0)).mpr
    rw [show t^2+u^2-a^2=t*(s+t) by nlinarith only [hD],abs_of_pos (by positivity)]
    nlinarith only [congrArg (fun x : ℝ=>t*x) he]

theorem circle_angle_coefficients_of_complementary (s t a u C : ℝ) (hs : 0<s) (ht : 0<t)
    (hst : s≠t) (hC : 0<C) (hD : u^2-a^2= -(s*t)) (hu : u=|s-t|/(2*C)) :
    |s^2+u^2-a^2|/(2*s*u)=C ∧ |t^2+u^2-a^2|/(2*t*u)=C := by
  have hu0 : 0<u:=by rw [hu];exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hst)) (by positivity)
  have he : u*(2*C)=|s-t|:=(eq_div_iff (by positivity : 2*C≠0)).mp hu
  constructor
  · apply (div_eq_iff (by positivity : 2*s*u≠0)).mpr
    rw [show s^2+u^2-a^2=s*(s-t) by nlinarith only [hD],abs_mul,abs_of_pos hs]
    nlinarith only [congrArg (fun x : ℝ=>s*x) he]
  · apply (div_eq_iff (by positivity : 2*t*u≠0)).mpr
    rw [show t^2+u^2-a^2=t*(t-s) by nlinarith only [hD],abs_mul,abs_of_pos ht,abs_sub_comm t s]
    nlinarith only [congrArg (fun x : ℝ=>t*x) he]

def alternateTransversalRadius (s t θ : ℝ) : ℝ := (s+t)/(2*Real.cos θ)
def complementaryTransversalRadius (s t θ : ℝ) : ℝ := |s-t|/(2*Real.cos θ)
def alternateTransversalCenter (s t θ : ℝ) : ℝ :=
  Real.sqrt ((alternateTransversalRadius s t θ)^2-s*t)
def complementaryTransversalCenter (s t θ : ℝ) : ℝ :=
  Real.sqrt ((complementaryTransversalRadius s t θ)^2+s*t)

theorem alternateTransversalRadius_pos (s t θ : ℝ) (hs : 0<s) (ht : 0<t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) : 0<alternateTransversalRadius s t θ :=
  div_pos (add_pos hs ht) (mul_pos (by norm_num) (acute_parameter_cos_bounds θ h0 hθ).1)

theorem complementaryTransversalRadius_pos (s t θ : ℝ) (hst : s≠t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) : 0<complementaryTransversalRadius s t θ :=
  div_pos (abs_pos.mpr (sub_ne_zero.mpr hst))
    (mul_pos (by norm_num) (acute_parameter_cos_bounds θ h0 hθ).1)

theorem alternateTransversalCenter_sq_pos (s t θ : ℝ) (hs : 0<s) (ht : 0<t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    0<(alternateTransversalRadius s t θ)^2-s*t := by
  have hc:=acute_parameter_cos_bounds θ h0 hθ
  have hu:=alternateTransversalRadius_pos s t θ hs ht h0 hθ
  have he : alternateTransversalRadius s t θ*(2*Real.cos θ)=s+t :=
    div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hc.1.ne')
  have he2:=congrArg (fun x : ℝ=>x^2) he
  have hc2 : (Real.cos θ)^2<1:=by nlinarith only [hc.1,hc.2]
  have hh:=mul_lt_mul_of_pos_left hc2 (by positivity : 0<4*(alternateTransversalRadius s t θ)^2)
  nlinarith only [he2,hh,sq_nonneg (s-t)]

theorem alternateTransversalCenter_pos (s t θ : ℝ) (hs : 0<s) (ht : 0<t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) : 0<alternateTransversalCenter s t θ :=
  Real.sqrt_pos.mpr (alternateTransversalCenter_sq_pos s t θ hs ht h0 hθ)

theorem complementaryTransversalCenter_pos (s t θ : ℝ) (hs : 0<s) (ht : 0<t) :
    0<complementaryTransversalCenter s t θ := by
  apply Real.sqrt_pos.mpr
  nlinarith only [mul_pos hs ht,sq_nonneg (complementaryTransversalRadius s t θ)]


def alternateTransversal (s t θ : ℝ) (hs : 0<s) (ht : 0<t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) (negative : Bool) : HalfPlaneLine :=
  .circle (if negative then -(alternateTransversalCenter s t θ) else alternateTransversalCenter s t θ)
    (alternateTransversalRadius s t θ) (alternateTransversalRadius_pos s t θ hs ht h0 hθ)

def complementaryTransversal (s t θ : ℝ) (hst : s≠t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) (negative : Bool) : HalfPlaneLine :=
  .circle (if negative then -(complementaryTransversalCenter s t θ) else complementaryTransversalCenter s t θ)
    (complementaryTransversalRadius s t θ) (complementaryTransversalRadius_pos s t θ hst h0 hθ)

theorem alternateTransversalCenter_sq (s t θ : ℝ) (hs : 0<s) (ht : 0<t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    (alternateTransversalCenter s t θ)^2=(alternateTransversalRadius s t θ)^2-s*t :=
  Real.sq_sqrt (alternateTransversalCenter_sq_pos s t θ hs ht h0 hθ).le

theorem complementaryTransversalCenter_sq (s t θ : ℝ) (hs : 0<s) (ht : 0<t) :
    (complementaryTransversalCenter s t θ)^2=(complementaryTransversalRadius s t θ)^2+s*t := by
  apply Real.sq_sqrt
  nlinarith only [mul_pos hs ht,sq_nonneg (complementaryTransversalRadius s t θ)]

theorem alternateTransversal_isThetaTransversal (s t θ : ℝ) (hs : 0<s) (ht : 0<t)
    (hst : s≠t) (h0 : 0<θ) (hθ : θ<Real.pi/2) (negative : Bool) :
    (HalfPlaneLine.circle 0 s hs).IsThetaTransversal (.circle 0 t ht) θ
      (alternateTransversal s t θ hs ht h0 hθ negative) := by
  apply (concentric_transversal_iff_coefficients s t hs ht hst θ h0 hθ _).mpr
  refine ⟨_,_,alternateTransversalRadius_pos s t θ hs ht h0 hθ,rfl,?_⟩
  apply circle_angle_coefficients_of_alternate s t _ _ _ hs ht
    (acute_parameter_cos_bounds θ h0 hθ).1 _ rfl
  have he:=alternateTransversalCenter_sq s t θ hs ht h0 hθ
  dsimp only [alternateTransversalRadius] at he
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,neg_sq] <;> linarith only [he]

theorem complementaryTransversal_isThetaTransversal (s t θ : ℝ) (hs : 0<s) (ht : 0<t)
    (hst : s≠t) (h0 : 0<θ) (hθ : θ<Real.pi/2) (negative : Bool) :
    (HalfPlaneLine.circle 0 s hs).IsThetaTransversal (.circle 0 t ht) θ
      (complementaryTransversal s t θ hst h0 hθ negative) := by
  apply (concentric_transversal_iff_coefficients s t hs ht hst θ h0 hθ _).mpr
  refine ⟨_,_,complementaryTransversalRadius_pos s t θ hst h0 hθ,rfl,?_⟩
  apply circle_angle_coefficients_of_complementary s t _ _ _ hs ht hst
    (acute_parameter_cos_bounds θ h0 hθ).1 _ rfl
  have he:=complementaryTransversalCenter_sq s t θ hs ht
  dsimp only [complementaryTransversalRadius] at he
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,neg_sq] <;> linarith only [he]

theorem transversalRadii_ne (s t θ : ℝ) (hs : 0<s) (ht : 0<t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    alternateTransversalRadius s t θ≠complementaryTransversalRadius s t θ := by
  have hab : |s-t|<s+t:=abs_lt.mpr ⟨by linarith,by linarith⟩
  exact (ne_of_lt (div_lt_div_of_pos_right hab
    (mul_pos (by norm_num) (acute_parameter_cos_bounds θ h0 hθ).1))).symm

theorem alternateTransversal_ne (s t θ : ℝ) (hs : 0<s) (ht : 0<t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    alternateTransversal s t θ hs ht h0 hθ false≠alternateTransversal s t θ hs ht h0 hθ true := by
  intro he
  have hh:=(HalfPlaneLine.circle.inj he).1
  have hp:=alternateTransversalCenter_pos s t θ hs ht h0 hθ
  change alternateTransversalCenter s t θ= -(alternateTransversalCenter s t θ) at hh
  linarith

theorem complementaryTransversal_ne (s t θ : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    complementaryTransversal s t θ hst h0 hθ false≠complementaryTransversal s t θ hst h0 hθ true := by
  intro he
  have hh:=(HalfPlaneLine.circle.inj he).1
  have hp:=complementaryTransversalCenter_pos s t θ hs ht
  change complementaryTransversalCenter s t θ= -(complementaryTransversalCenter s t θ) at hh
  linarith

theorem alternateTransversal_ne_complementary (s t θ : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) (a b : Bool) :
    alternateTransversal s t θ hs ht h0 hθ a≠complementaryTransversal s t θ hst h0 hθ b := by
  intro he
  exact transversalRadii_ne s t θ hs ht h0 hθ (HalfPlaneLine.circle.inj he).2

theorem concentric_transversal_classification (s t θ : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) (N : HalfPlaneLine) :
    (HalfPlaneLine.circle 0 s hs).IsThetaTransversal (.circle 0 t ht) θ N ↔
      N∈({alternateTransversal s t θ hs ht h0 hθ false,
        alternateTransversal s t θ hs ht h0 hθ true,
        complementaryTransversal s t θ hst h0 hθ false,
        complementaryTransversal s t θ hst h0 hθ true} : Set HalfPlaneLine) := by
  constructor
  · intro hN
    obtain ⟨a,u,hu,rfl,h1,h2⟩:=(concentric_transversal_iff_coefficients s t hs ht hst θ h0 hθ N).mp hN
    have hc:=(acute_parameter_cos_bounds θ h0 hθ).1
    rcases equal_circle_angle_coefficients s t a u (Real.cos θ) hs ht hst hu hc h1 h2 with
      ⟨hD,hu'⟩ | ⟨hD,hu'⟩
    · have hu'' : u=alternateTransversalRadius s t θ:=hu'
      have he:=(alternateTransversalCenter_sq s t θ hs ht h0 hθ)
      have ha : a^2=(alternateTransversalCenter s t θ)^2 := by rw [←hu''] at he;linarith only [hD,he]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha with ha | ha
      · subst u
        rw [ha]
        exact mem_insert _ _
      · subst u
        rw [ha]
        exact mem_insert_of_mem _ (mem_insert _ _)
    · have hu'' : u=complementaryTransversalRadius s t θ:=hu'
      have he:=complementaryTransversalCenter_sq s t θ hs ht
      have ha : a^2=(complementaryTransversalCenter s t θ)^2 := by rw [←hu''] at he;linarith only [hD,he]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha with ha | ha
      · subst u
        rw [ha]
        exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_insert _ _))
      · subst u
        rw [ha]
        exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _)))
  · simp only [mem_insert_iff,mem_singleton_iff]
    rintro (rfl|rfl|rfl|rfl)
    · exact alternateTransversal_isThetaTransversal s t θ hs ht hst h0 hθ false
    · exact alternateTransversal_isThetaTransversal s t θ hs ht hst h0 hθ true
    · exact complementaryTransversal_isThetaTransversal s t θ hs ht hst h0 hθ false
    · exact complementaryTransversal_isThetaTransversal s t θ hs ht hst h0 hθ true

theorem concentric_transversals_ncard (s t θ : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    {N : HalfPlaneLine | (HalfPlaneLine.circle 0 s hs).IsThetaTransversal (.circle 0 t ht) θ N}.ncard=4 := by
  have he : {N : HalfPlaneLine | (HalfPlaneLine.circle 0 s hs).IsThetaTransversal (.circle 0 t ht) θ N}=
      {alternateTransversal s t θ hs ht h0 hθ false,alternateTransversal s t θ hs ht h0 hθ true,
       complementaryTransversal s t θ hst h0 hθ false,complementaryTransversal s t θ hst h0 hθ true} := by
    ext N
    exact concentric_transversal_classification s t θ hs ht hst h0 hθ N
  rw [he]
  have h1:=alternateTransversal_ne s t θ hs ht h0 hθ
  have h2:=complementaryTransversal_ne s t θ hs ht hst h0 hθ
  have h3:=alternateTransversal_ne_complementary s t θ hs ht hst h0 hθ false false
  have h4:=alternateTransversal_ne_complementary s t θ hs ht hst h0 hθ false true
  have h5:=alternateTransversal_ne_complementary s t θ hs ht hst h0 hθ true false
  have h6:=alternateTransversal_ne_complementary s t θ hs ht hst h0 hθ true true
  rw [Set.ncard_insert_of_notMem (by simp [h1,h3,h4]),
    Set.ncard_insert_of_notMem (by simp [h5,h6]),Set.ncard_pair h2]


/-- The actual image geodesic under the genuine real fractional-linear action. -/
def HalfPlaneLine.realGLMap (L : HalfPlaneLine) (g : GL (Fin 2) ℝ) : HalfPlaneLine :=
  (realGL_image_hLine g L).choose

theorem HalfPlaneLine.realGLMap_carrier (L : HalfPlaneLine) (g : GL (Fin 2) ℝ) :
    (L.realGLMap g).carrier=(g • · : ℍ→ℍ) '' L.carrier := (realGL_image_hLine g L).choose_spec.symm

theorem HalfPlaneLine.realGLMap_injective (g : GL (Fin 2) ℝ) :
    Function.Injective (fun L : HalfPlaneLine=>L.realGLMap g) := by
  intro L M he
  apply HalfPlaneLine.carrier_injective
  apply (realGL_isometry g).injective.image_injective
  rw [←L.realGLMap_carrier,←M.realGLMap_carrier]
  exact congrArg HalfPlaneLine.carrier he

theorem HalfPlaneLine.realGLMap_inv (L : HalfPlaneLine) (g : GL (Fin 2) ℝ) :
    (L.realGLMap g).realGLMap g⁻¹=L := by
  apply HalfPlaneLine.carrier_injective
  rw [HalfPlaneLine.realGLMap_carrier,L.realGLMap_carrier,image_image]
  simp only [inv_smul_smul,Set.image_id']

theorem HalfPlaneLine.realGLMap_surjective (g : GL (Fin 2) ℝ) :
    Function.Surjective (fun L : HalfPlaneLine=>L.realGLMap g) := by
  intro L
  refine ⟨L.realGLMap g⁻¹,?_⟩
  simpa only [inv_inv] using L.realGLMap_inv g⁻¹

theorem HalfPlaneLine.transversalSet_realGL_image (L M : HalfPlaneLine) (g : GL (Fin 2) ℝ) (θ : ℝ) :
    (fun N : HalfPlaneLine=>N.realGLMap g) '' {N | L.IsThetaTransversal M θ N}=
      {N | (L.realGLMap g).IsThetaTransversal (M.realGLMap g) θ N} := by
  ext N
  constructor
  · rintro ⟨P,hP,rfl⟩
    exact (L.isThetaTransversal_realGL_image_iff M P (L.realGLMap g) (M.realGLMap g)
      (P.realGLMap g) g (L.realGLMap_carrier g).symm (M.realGLMap_carrier g).symm
      (P.realGLMap_carrier g).symm θ).mpr hP
  · intro hN
    obtain ⟨P,rfl⟩:=HalfPlaneLine.realGLMap_surjective g N
    refine ⟨P,?_,rfl⟩
    exact (L.isThetaTransversal_realGL_image_iff M P (L.realGLMap g) (M.realGLMap g)
      (P.realGLMap g) g (L.realGLMap_carrier g).symm (M.realGLMap_carrier g).symm
      (P.realGLMap_carrier g).symm θ).mp hN

/-- The actual set of nonperpendicular transversals has exactly four elements. -/
theorem HalfPlaneLine.theta_transversals_ncard (L M : HalfPlaneLine) (hd : L.HDisjoint M)
    (θ : ℝ) (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    {N : HalfPlaneLine | L.IsThetaTransversal M θ N}.ncard=4 := by
  obtain ⟨g,s,t,hs,ht,_,hst,hL,hM⟩:=L.exists_concentric_normalizer M hd
  have hL' : L.realGLMap g=.circle 0 s hs := by
    apply HalfPlaneLine.carrier_injective
    rw [L.realGLMap_carrier]
    exact hL
  have hM' : M.realGLMap g=.circle 0 t ht := by
    apply HalfPlaneLine.carrier_injective
    rw [M.realGLMap_carrier]
    exact hM
  have he:=L.transversalSet_realGL_image M g θ
  rw [hL',hM'] at he
  have hn:=concentric_transversals_ncard s t θ hs ht hst h0 hθ
  rw [←he,Set.ncard_image_of_injective _ (HalfPlaneLine.realGLMap_injective g)] at hn
  exact hn

/-- The genuine native disc transversal set is the actual Cayley image of the H line set. -/
theorem DiscLine.transversalSet_eq_cayley_image (L M : DiscLine) (θ : ℝ) :
    {N : DiscLine | L.IsThetaTransversal M θ N}=
      HalfPlaneLine.toDiscLine '' {N : HalfPlaneLine | L.toHalfPlane.IsThetaTransversal M.toHalfPlane θ N} := by
  ext N
  constructor
  · intro hN
    exact ⟨N.toHalfPlane,(L.isThetaTransversal_iff_halfPlane M N θ).mp hN,N.toHalfPlane_spec⟩
  · rintro ⟨P,hP,rfl⟩
    change L.toHalfPlane.IsThetaTransversal M.toHalfPlane θ P at hP
    apply (L.isThetaTransversal_iff_halfPlane M P.toDiscLine θ).mpr
    simpa only [HalfPlaneLine.toDiscLine_toHalfPlane] using hP

theorem DiscLine.theta_transversals_ncard (L M : DiscLine) (hd : L.HDisjoint M)
    (θ : ℝ) (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    {N : DiscLine | L.IsThetaTransversal M θ N}.ncard=4 := by
  rw [L.transversalSet_eq_cayley_image,Set.ncard_image_of_injective _ HalfPlaneLine.toDiscLine_injective]
  exact L.toHalfPlane.theta_transversals_ncard M.toHalfPlane ((L.hDisjoint_iff_halfPlane M).mp hd) θ h0 hθ


/-- The source alternate configuration: the actual transversal passes through the
intersection of the genuine common perpendicular and genuine equal-distance bisector. -/
def HalfPlaneLine.IsAlternateTransversal (L M : HalfPlaneLine) (θ : ℝ) (N : HalfPlaneLine) : Prop :=
  L.IsThetaTransversal M θ N ∧ ∃(C B : HalfPlaneLine) (p : ℍ),
    L.Orthogonal C ∧ M.Orthogonal C ∧ L.bisectorSet M=B.carrier ∧
      p∈C.carrier ∧ p∈B.carrier ∧ p∈N.carrier

/-- The source complementary configuration: the actual transversal is perpendicular
 to the genuine equal-distance bisector. -/
def HalfPlaneLine.IsComplementaryTransversal (L M : HalfPlaneLine) (θ : ℝ) (N : HalfPlaneLine) : Prop :=
  L.IsThetaTransversal M θ N ∧ ∃B : HalfPlaneLine,L.bisectorSet M=B.carrier ∧ N.Orthogonal B

def DiscLine.IsAlternateTransversal (L M : DiscLine) (θ : ℝ) (N : DiscLine) : Prop :=
  L.IsThetaTransversal M θ N ∧ ∃(C B : DiscLine) (p : 𝔻),
    L.Orthogonal C ∧ M.Orthogonal C ∧ L.bisectorSet M=B.carrier ∧
      p∈C.carrier ∧ p∈B.carrier ∧ p∈N.carrier

def DiscLine.IsComplementaryTransversal (L M : DiscLine) (θ : ℝ) (N : DiscLine) : Prop :=
  L.IsThetaTransversal M θ N ∧ ∃B : DiscLine,L.bisectorSet M=B.carrier ∧ N.Orthogonal B

def concentricTransversalCentre (s t : ℝ) (hs : 0<s) (ht : 0<t) : ℍ :=
  ⟨((Real.sqrt (s*t) : ℝ) : ℂ)*Complex.I,by simpa using Real.sqrt_pos.mpr (mul_pos hs ht)⟩

theorem concentricTransversalCentre_re (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    (concentricTransversalCentre s t hs ht).re=0 := by simp [concentricTransversalCentre]

theorem concentricTransversalCentre_im (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    (concentricTransversalCentre s t hs ht).im=Real.sqrt (s*t) := by simp [concentricTransversalCentre]

theorem concentric_commonOrthogonal_eq (s t : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (N : HalfPlaneLine) (h1 : (HalfPlaneLine.circle 0 s hs).Orthogonal N)
    (h2 : (HalfPlaneLine.circle 0 t ht).Orthogonal N) : N=HalfPlaneLine.vertical 0 := by
  rw [HalfPlaneLine.orthogonal_iff_coefficients] at h1 h2
  cases N with
  | vertical a =>
    change (0 : ℝ)=a at h1
    rw [h1]
  | circle a u hu =>
    change (0-a)^2=s^2+u^2 at h1
    change (0-a)^2=t^2+u^2 at h2
    exfalso
    apply hst
    nlinarith only [h1,h2,hs,ht]

theorem concentricTransversalCentre_mem_bisector (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    concentricTransversalCentre s t hs ht∈(concentricBisectorLine s t hs ht).carrier := by
  apply norm_sub_real_eq_of_sq (Real.sqrt_pos.mpr (mul_pos hs ht))
  rw [concentricTransversalCentre_re,concentricTransversalCentre_im]
  ring

theorem concentric_bisector_centre_unique (s t : ℝ) (hs : 0<s) (ht : 0<t) (p : ℍ)
    (haxis : p∈(HalfPlaneLine.vertical 0).carrier)
    (hbis : p∈(concentricBisectorLine s t hs ht).carrier) :
    p=concentricTransversalCentre s t hs ht := by
  have hpRe : p.re=0:=haxis
  have he:=norm_sub_real_eq_radius_sq hbis
  rw [hpRe] at he
  have hpIm : p.im=Real.sqrt (s*t) := by nlinarith only [he,p.im_pos,Real.sqrt_pos.mpr (mul_pos hs ht)]
  apply UpperHalfPlane.ext
  apply Complex.ext
  · simpa only [UpperHalfPlane.coe_re,concentricTransversalCentre_re] using hpRe
  · simpa only [UpperHalfPlane.coe_im,concentricTransversalCentre_im] using hpIm

theorem circle_mem_concentricTransversalCentre_iff (s t a u : ℝ) (hs : 0<s) (ht : 0<t)
    (hu : 0<u) : concentricTransversalCentre s t hs ht∈(HalfPlaneLine.circle a u hu).carrier ↔
      u^2-a^2=s*t := by
  have hm:=Real.sq_sqrt (mul_pos hs ht).le
  constructor
  · intro hp
    have he:=norm_sub_real_eq_radius_sq hp
    rw [concentricTransversalCentre_re,concentricTransversalCentre_im] at he
    nlinarith only [he,hm]
  · intro hd
    apply norm_sub_real_eq_of_sq hu
    rw [concentricTransversalCentre_re,concentricTransversalCentre_im]
    nlinarith only [hd,hm]

theorem circle_orthogonal_concentricBisector_iff (s t a u : ℝ) (hs : 0<s) (ht : 0<t)
    (hu : 0<u) : (HalfPlaneLine.circle a u hu).Orthogonal (concentricBisectorLine s t hs ht) ↔
      u^2-a^2= -(s*t) := by
  rw [HalfPlaneLine.orthogonal_iff_coefficients]
  change (a-0)^2=u^2+(Real.sqrt (s*t))^2 ↔ _
  rw [sub_zero,Real.sq_sqrt (mul_pos hs ht).le]
  constructor <;> intro h <;> linarith only [h]

theorem concentric_isAlternate_iff (s t θ : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (N : HalfPlaneLine) (hN : (HalfPlaneLine.circle 0 s hs).IsThetaTransversal (.circle 0 t ht) θ N) :
    (HalfPlaneLine.circle 0 s hs).IsAlternateTransversal (.circle 0 t ht) θ N ↔
      concentricTransversalCentre s t hs ht∈N.carrier := by
  constructor
  · rintro ⟨_,C,B,p,h1,h2,hB,hpC,hpB,hpN⟩
    have hC:=concentric_commonOrthogonal_eq s t hs ht hst C h1 h2
    have hB' : B=concentricBisectorLine s t hs ht :=
      HalfPlaneLine.carrier_injective (hB.symm.trans (concentric_bisectorSet s t hs ht hst))
    rw [hC] at hpC
    rw [hB'] at hpB
    rw [←concentric_bisector_centre_unique s t hs ht p hpC hpB]
    exact hpN
  · intro hpN
    refine ⟨hN,HalfPlaneLine.vertical 0,concentricBisectorLine s t hs ht,
      concentricTransversalCentre s t hs ht,?_,?_,concentric_bisectorSet s t hs ht hst,
      concentricTransversalCentre_re s t hs ht,concentricTransversalCentre_mem_bisector s t hs ht,hpN⟩
    · rw [HalfPlaneLine.orthogonal_iff_coefficients]
      rfl
    · rw [HalfPlaneLine.orthogonal_iff_coefficients]
      rfl

theorem concentric_isComplementary_iff (s t θ : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (N : HalfPlaneLine) (hN : (HalfPlaneLine.circle 0 s hs).IsThetaTransversal (.circle 0 t ht) θ N) :
    (HalfPlaneLine.circle 0 s hs).IsComplementaryTransversal (.circle 0 t ht) θ N ↔
      N.Orthogonal (concentricBisectorLine s t hs ht) := by
  constructor
  · rintro ⟨_,B,hB,hNB⟩
    have hB' : B=concentricBisectorLine s t hs ht :=
      HalfPlaneLine.carrier_injective (hB.symm.trans (concentric_bisectorSet s t hs ht hst))
    rwa [hB'] at hNB
  · exact fun h=>⟨hN,concentricBisectorLine s t hs ht,concentric_bisectorSet s t hs ht hst,h⟩

theorem alternateTransversal_centre_mem (s t θ : ℝ) (hs : 0<s) (ht : 0<t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) (negative : Bool) :
    concentricTransversalCentre s t hs ht∈(alternateTransversal s t θ hs ht h0 hθ negative).carrier := by
  rw [alternateTransversal,circle_mem_concentricTransversalCentre_iff]
  have he:=alternateTransversalCenter_sq s t θ hs ht h0 hθ
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,neg_sq] <;> linarith only [he]

theorem complementaryTransversal_centre_not_mem (s t θ : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) (negative : Bool) :
    concentricTransversalCentre s t hs ht∉(complementaryTransversal s t θ hst h0 hθ negative).carrier := by
  rw [complementaryTransversal,circle_mem_concentricTransversalCentre_iff]
  have he:=complementaryTransversalCenter_sq s t θ hs ht
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,neg_sq] <;>
    intro hh <;> nlinarith only [he,hh,mul_pos hs ht]

theorem complementaryTransversal_orthogonal_bisector (s t θ : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) (negative : Bool) :
    (complementaryTransversal s t θ hst h0 hθ negative).Orthogonal (concentricBisectorLine s t hs ht) := by
  rw [complementaryTransversal,circle_orthogonal_concentricBisector_iff]
  have he:=complementaryTransversalCenter_sq s t θ hs ht
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,neg_sq] <;> linarith only [he]

theorem alternateTransversal_not_orthogonal_bisector (s t θ : ℝ) (hs : 0<s) (ht : 0<t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) (negative : Bool) :
    ¬(alternateTransversal s t θ hs ht h0 hθ negative).Orthogonal (concentricBisectorLine s t hs ht) := by
  rw [alternateTransversal,circle_orthogonal_concentricBisector_iff]
  have he:=alternateTransversalCenter_sq s t θ hs ht h0 hθ
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,neg_sq] <;>
    intro hh <;> nlinarith only [he,hh,mul_pos hs ht]

theorem concentric_alternate_transversals (s t θ : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) (N : HalfPlaneLine) :
    (HalfPlaneLine.circle 0 s hs).IsAlternateTransversal (.circle 0 t ht) θ N ↔
      N∈({alternateTransversal s t θ hs ht h0 hθ false,
        alternateTransversal s t θ hs ht h0 hθ true} : Set HalfPlaneLine) := by
  constructor
  · intro hN
    have he:=(concentric_transversal_classification s t θ hs ht hst h0 hθ N).mp hN.1
    have hc:=(concentric_isAlternate_iff s t θ hs ht hst N hN.1).mp hN
    simp only [mem_insert_iff,mem_singleton_iff] at he ⊢
    rcases he with rfl|rfl|rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (complementaryTransversal_centre_not_mem s t θ hs ht hst h0 hθ false hc)
    · exact False.elim (complementaryTransversal_centre_not_mem s t θ hs ht hst h0 hθ true hc)
  · simp only [mem_insert_iff,mem_singleton_iff]
    rintro (rfl|rfl)
    · exact (concentric_isAlternate_iff s t θ hs ht hst _
        (alternateTransversal_isThetaTransversal s t θ hs ht hst h0 hθ false)).mpr
        (alternateTransversal_centre_mem s t θ hs ht h0 hθ false)
    · exact (concentric_isAlternate_iff s t θ hs ht hst _
        (alternateTransversal_isThetaTransversal s t θ hs ht hst h0 hθ true)).mpr
        (alternateTransversal_centre_mem s t θ hs ht h0 hθ true)

theorem concentric_complementary_transversals (s t θ : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) (N : HalfPlaneLine) :
    (HalfPlaneLine.circle 0 s hs).IsComplementaryTransversal (.circle 0 t ht) θ N ↔
      N∈({complementaryTransversal s t θ hst h0 hθ false,
        complementaryTransversal s t θ hst h0 hθ true} : Set HalfPlaneLine) := by
  constructor
  · intro hN
    have he:=(concentric_transversal_classification s t θ hs ht hst h0 hθ N).mp hN.1
    have hc:=(concentric_isComplementary_iff s t θ hs ht hst N hN.1).mp hN
    simp only [mem_insert_iff,mem_singleton_iff] at he ⊢
    rcases he with rfl|rfl|rfl|rfl
    · exact False.elim (alternateTransversal_not_orthogonal_bisector s t θ hs ht h0 hθ false hc)
    · exact False.elim (alternateTransversal_not_orthogonal_bisector s t θ hs ht h0 hθ true hc)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp only [mem_insert_iff,mem_singleton_iff]
    rintro (rfl|rfl)
    · exact (concentric_isComplementary_iff s t θ hs ht hst _
        (complementaryTransversal_isThetaTransversal s t θ hs ht hst h0 hθ false)).mpr
        (complementaryTransversal_orthogonal_bisector s t θ hs ht hst h0 hθ false)
    · exact (concentric_isComplementary_iff s t θ hs ht hst _
        (complementaryTransversal_isThetaTransversal s t θ hs ht hst h0 hθ true)).mpr
        (complementaryTransversal_orthogonal_bisector s t θ hs ht hst h0 hθ true)


theorem HalfPlaneLine.IsAlternateTransversal.realGLMap {L M N : HalfPlaneLine} {θ : ℝ}
    (h : L.IsAlternateTransversal M θ N) (g : GL (Fin 2) ℝ) :
    (L.realGLMap g).IsAlternateTransversal (M.realGLMap g) θ (N.realGLMap g) := by
  obtain ⟨hT,C,B,p,hLC,hMC,hB,hpC,hpB,hpN⟩:=h
  have hT' := (L.isThetaTransversal_realGL_image_iff M N (L.realGLMap g) (M.realGLMap g)
    (N.realGLMap g) g (L.realGLMap_carrier g).symm (M.realGLMap_carrier g).symm
    (N.realGLMap_carrier g).symm θ).mpr hT
  refine ⟨hT',C.realGLMap g,B.realGLMap g,g • p,?_,?_,?_,?_,?_,?_⟩
  · exact (L.orthogonal_realGL_image_iff C (L.realGLMap g) (C.realGLMap g) g
      (L.realGLMap_carrier g).symm (C.realGLMap_carrier g).symm).mpr hLC
  · exact (M.orthogonal_realGL_image_iff C (M.realGLMap g) (C.realGLMap g) g
      (M.realGLMap_carrier g).symm (C.realGLMap_carrier g).symm).mpr hMC
  · have he:=L.bisectorSet_image_isometry M (L.realGLMap g) (M.realGLMap g)
      (g • ·) (realGL_isometry g) (L.realGLMap_carrier g).symm (M.realGLMap_carrier g).symm
    rw [hB,←B.realGLMap_carrier g] at he
    exact he.symm
  · rw [C.realGLMap_carrier]
    exact mem_image_of_mem _ hpC
  · rw [B.realGLMap_carrier]
    exact mem_image_of_mem _ hpB
  · rw [N.realGLMap_carrier]
    exact mem_image_of_mem _ hpN

theorem HalfPlaneLine.IsComplementaryTransversal.realGLMap {L M N : HalfPlaneLine} {θ : ℝ}
    (h : L.IsComplementaryTransversal M θ N) (g : GL (Fin 2) ℝ) :
    (L.realGLMap g).IsComplementaryTransversal (M.realGLMap g) θ (N.realGLMap g) := by
  obtain ⟨hT,B,hB,hNB⟩:=h
  have hT' := (L.isThetaTransversal_realGL_image_iff M N (L.realGLMap g) (M.realGLMap g)
    (N.realGLMap g) g (L.realGLMap_carrier g).symm (M.realGLMap_carrier g).symm
    (N.realGLMap_carrier g).symm θ).mpr hT
  refine ⟨hT',B.realGLMap g,?_,?_⟩
  · have he:=L.bisectorSet_image_isometry M (L.realGLMap g) (M.realGLMap g)
      (g • ·) (realGL_isometry g) (L.realGLMap_carrier g).symm (M.realGLMap_carrier g).symm
    rw [hB,←B.realGLMap_carrier g] at he
    exact he.symm
  · exact (N.orthogonal_realGL_image_iff B (N.realGLMap g) (B.realGLMap g) g
      (N.realGLMap_carrier g).symm (B.realGLMap_carrier g).symm).mpr hNB

theorem HalfPlaneLine.isAlternateTransversal_realGLMap_iff (L M N : HalfPlaneLine)
    (θ : ℝ) (g : GL (Fin 2) ℝ) :
    (L.realGLMap g).IsAlternateTransversal (M.realGLMap g) θ (N.realGLMap g) ↔
      L.IsAlternateTransversal M θ N := by
  constructor
  · intro h
    simpa only [HalfPlaneLine.realGLMap_inv] using h.realGLMap g⁻¹
  · exact fun h=>h.realGLMap g

theorem HalfPlaneLine.isComplementaryTransversal_realGLMap_iff (L M N : HalfPlaneLine)
    (θ : ℝ) (g : GL (Fin 2) ℝ) :
    (L.realGLMap g).IsComplementaryTransversal (M.realGLMap g) θ (N.realGLMap g) ↔
      L.IsComplementaryTransversal M θ N := by
  constructor
  · intro h
    simpa only [HalfPlaneLine.realGLMap_inv] using h.realGLMap g⁻¹
  · exact fun h=>h.realGLMap g

theorem HalfPlaneLine.alternateSet_realGL_image (L M : HalfPlaneLine) (g : GL (Fin 2) ℝ) (θ : ℝ) :
    (fun N : HalfPlaneLine=>N.realGLMap g) '' {N | L.IsAlternateTransversal M θ N}=
      {N | (L.realGLMap g).IsAlternateTransversal (M.realGLMap g) θ N} := by
  ext N
  constructor
  · rintro ⟨P,hP,rfl⟩
    exact (L.isAlternateTransversal_realGLMap_iff M P θ g).mpr hP
  · intro hN
    obtain ⟨P,rfl⟩:=HalfPlaneLine.realGLMap_surjective g N
    exact ⟨P,(L.isAlternateTransversal_realGLMap_iff M P θ g).mp hN,rfl⟩

theorem HalfPlaneLine.complementarySet_realGL_image (L M : HalfPlaneLine) (g : GL (Fin 2) ℝ) (θ : ℝ) :
    (fun N : HalfPlaneLine=>N.realGLMap g) '' {N | L.IsComplementaryTransversal M θ N}=
      {N | (L.realGLMap g).IsComplementaryTransversal (M.realGLMap g) θ N} := by
  ext N
  constructor
  · rintro ⟨P,hP,rfl⟩
    exact (L.isComplementaryTransversal_realGLMap_iff M P θ g).mpr hP
  · intro hN
    obtain ⟨P,rfl⟩:=HalfPlaneLine.realGLMap_surjective g N
    exact ⟨P,(L.isComplementaryTransversal_realGLMap_iff M P θ g).mp hN,rfl⟩

theorem HalfPlaneLine.alternate_transversals_ncard (L M : HalfPlaneLine) (hd : L.HDisjoint M)
    (θ : ℝ) (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    {N : HalfPlaneLine | L.IsAlternateTransversal M θ N}.ncard=2 := by
  obtain ⟨g,s,t,hs,ht,_,hst,hL,hM⟩:=L.exists_concentric_normalizer M hd
  have hL' : L.realGLMap g=.circle 0 s hs:=HalfPlaneLine.carrier_injective ((L.realGLMap_carrier g).trans hL)
  have hM' : M.realGLMap g=.circle 0 t ht:=HalfPlaneLine.carrier_injective ((M.realGLMap_carrier g).trans hM)
  have he:=L.alternateSet_realGL_image M g θ
  rw [hL',hM'] at he
  have hn : {N : HalfPlaneLine | (HalfPlaneLine.circle 0 s hs).IsAlternateTransversal (.circle 0 t ht) θ N}.ncard=2 :=
    by
    have hset : {N : HalfPlaneLine | (HalfPlaneLine.circle 0 s hs).IsAlternateTransversal (.circle 0 t ht) θ N}=
        {alternateTransversal s t θ hs ht h0 hθ false,alternateTransversal s t θ hs ht h0 hθ true} := by
      ext N
      exact concentric_alternate_transversals s t θ hs ht hst h0 hθ N
    rw [hset,Set.ncard_pair (alternateTransversal_ne s t θ hs ht h0 hθ)]
  rw [←he,Set.ncard_image_of_injective _ (HalfPlaneLine.realGLMap_injective g)] at hn
  exact hn

theorem HalfPlaneLine.complementary_transversals_ncard (L M : HalfPlaneLine) (hd : L.HDisjoint M)
    (θ : ℝ) (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    {N : HalfPlaneLine | L.IsComplementaryTransversal M θ N}.ncard=2 := by
  obtain ⟨g,s,t,hs,ht,_,hst,hL,hM⟩:=L.exists_concentric_normalizer M hd
  have hL' : L.realGLMap g=.circle 0 s hs:=HalfPlaneLine.carrier_injective ((L.realGLMap_carrier g).trans hL)
  have hM' : M.realGLMap g=.circle 0 t ht:=HalfPlaneLine.carrier_injective ((M.realGLMap_carrier g).trans hM)
  have he:=L.complementarySet_realGL_image M g θ
  rw [hL',hM'] at he
  have hn : {N : HalfPlaneLine | (HalfPlaneLine.circle 0 s hs).IsComplementaryTransversal (.circle 0 t ht) θ N}.ncard=
    2 := by
    have hset : {N : HalfPlaneLine | (HalfPlaneLine.circle 0 s hs).IsComplementaryTransversal (.circle 0 t ht) θ N}=
        {complementaryTransversal s t θ hst h0 hθ false,complementaryTransversal s t θ hst h0 hθ true} := by
      ext N
      exact concentric_complementary_transversals s t θ hs ht hst h0 hθ N
    rw [hset,Set.ncard_pair (complementaryTransversal_ne s t θ hs ht hst h0 hθ)]
  rw [←he,Set.ncard_image_of_injective _ (HalfPlaneLine.realGLMap_injective g)] at hn
  exact hn

theorem concentric_transversal_types_exclusive (s t θ : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (h0 : 0<θ) (hθ : θ<Real.pi/2) (N : HalfPlaneLine)
    (hN : (HalfPlaneLine.circle 0 s hs).IsThetaTransversal (.circle 0 t ht) θ N) :
    ((HalfPlaneLine.circle 0 s hs).IsAlternateTransversal (.circle 0 t ht) θ N ∧
      ¬(HalfPlaneLine.circle 0 s hs).IsComplementaryTransversal (.circle 0 t ht) θ N) ∨
    ((HalfPlaneLine.circle 0 s hs).IsComplementaryTransversal (.circle 0 t ht) θ N ∧
      ¬(HalfPlaneLine.circle 0 s hs).IsAlternateTransversal (.circle 0 t ht) θ N) := by
  rw [concentric_alternate_transversals s t θ hs ht hst h0 hθ,
    concentric_complementary_transversals s t θ hs ht hst h0 hθ]
  have he:=(concentric_transversal_classification s t θ hs ht hst h0 hθ N).mp hN
  simp only [mem_insert_iff,mem_singleton_iff] at he ⊢
  have h3:=alternateTransversal_ne_complementary s t θ hs ht hst h0 hθ false false
  have h4:=alternateTransversal_ne_complementary s t θ hs ht hst h0 hθ false true
  have h5:=alternateTransversal_ne_complementary s t θ hs ht hst h0 hθ true false
  have h6:=alternateTransversal_ne_complementary s t θ hs ht hst h0 hθ true true
  rcases he with rfl|rfl|rfl|rfl
  · exact Or.inl ⟨Or.inl rfl,not_or.mpr ⟨h3,h4⟩⟩
  · exact Or.inl ⟨Or.inr rfl,not_or.mpr ⟨h5,h6⟩⟩
  · exact Or.inr ⟨Or.inl rfl,not_or.mpr ⟨Ne.symm h3,Ne.symm h5⟩⟩
  · exact Or.inr ⟨Or.inr rfl,not_or.mpr ⟨Ne.symm h4,Ne.symm h6⟩⟩

theorem HalfPlaneLine.theta_transversal_types_exclusive (L M : HalfPlaneLine) (hd : L.HDisjoint M)
    (θ : ℝ) (h0 : 0<θ) (hθ : θ<Real.pi/2) (N : HalfPlaneLine) (hN : L.IsThetaTransversal M θ N) :
    (L.IsAlternateTransversal M θ N ∧ ¬L.IsComplementaryTransversal M θ N) ∨
      (L.IsComplementaryTransversal M θ N ∧ ¬L.IsAlternateTransversal M θ N) := by
  obtain ⟨g,s,t,hs,ht,_,hst,hL,hM⟩:=L.exists_concentric_normalizer M hd
  have hL' : L.realGLMap g=.circle 0 s hs:=HalfPlaneLine.carrier_injective ((L.realGLMap_carrier g).trans hL)
  have hM' : M.realGLMap g=.circle 0 t ht:=HalfPlaneLine.carrier_injective ((M.realGLMap_carrier g).trans hM)
  have hN' := (L.isThetaTransversal_realGL_image_iff M N (L.realGLMap g) (M.realGLMap g)
    (N.realGLMap g) g (L.realGLMap_carrier g).symm (M.realGLMap_carrier g).symm
    (N.realGLMap_carrier g).symm θ).mpr hN
  rw [hL',hM'] at hN'
  have he:=concentric_transversal_types_exclusive s t θ hs ht hst h0 hθ (N.realGLMap g) hN'
  rw [←hL',←hM',L.isAlternateTransversal_realGLMap_iff M N θ g,
    L.isComplementaryTransversal_realGLMap_iff M N θ g] at he
  exact he


theorem DiscLine.bisectorSet_eq_iff_halfPlane (L M B : DiscLine) :
    L.bisectorSet M=B.carrier ↔ L.toHalfPlane.bisectorSet M.toHalfPlane=B.toHalfPlane.carrier := by
  have hb:=B.toHalfPlane.discCarrier_eq_cayley_image
  change B.toHalfPlane.toDiscLine.carrier=halfPlaneToDisc '' B.toHalfPlane.carrier at hb
  rw [B.toHalfPlane_spec] at hb
  rw [L.bisectorSet_eq_cayley,hb]
  constructor
  · intro he
    apply (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective).image_injective
    exact he
  · exact congrArg (fun S : Set ℍ=>halfPlaneToDisc '' S)

theorem DiscLine.isAlternateTransversal_iff_halfPlane (L M N : DiscLine) (θ : ℝ) :
    L.IsAlternateTransversal M θ N ↔ L.toHalfPlane.IsAlternateTransversal M.toHalfPlane θ N.toHalfPlane := by
  constructor
  · rintro ⟨hT,C,B,p,hLC,hMC,hB,hpC,hpB,hpN⟩
    exact ⟨(L.isThetaTransversal_iff_halfPlane M N θ).mp hT,C.toHalfPlane,B.toHalfPlane,
      discToHalfPlane p,(L.orthogonal_iff_halfPlane C).mp hLC,(M.orthogonal_iff_halfPlane C).mp hMC,
      (L.bisectorSet_eq_iff_halfPlane M B).mp hB,(C.mem_carrier p).mp hpC,
      (B.mem_carrier p).mp hpB,(N.mem_carrier p).mp hpN⟩
  · rintro ⟨hT,C,B,p,hLC,hMC,hB,hpC,hpB,hpN⟩
    refine ⟨(L.isThetaTransversal_iff_halfPlane M N θ).mpr hT,C.toDiscLine,B.toDiscLine,
      halfPlaneToDisc p,?_,?_,?_,?_,?_,?_⟩
    · apply (L.orthogonal_iff_halfPlane C.toDiscLine).mpr
      simpa only [HalfPlaneLine.toDiscLine_toHalfPlane] using hLC
    · apply (M.orthogonal_iff_halfPlane C.toDiscLine).mpr
      simpa only [HalfPlaneLine.toDiscLine_toHalfPlane] using hMC
    · apply (L.bisectorSet_eq_iff_halfPlane M B.toDiscLine).mpr
      simpa only [HalfPlaneLine.toDiscLine_toHalfPlane] using hB
    · apply (C.toDiscLine.mem_carrier _).mpr
      simpa only [HalfPlaneLine.toDiscLine_toHalfPlane,discToHalfPlane_halfPlaneToDisc] using hpC
    · apply (B.toDiscLine.mem_carrier _).mpr
      simpa only [HalfPlaneLine.toDiscLine_toHalfPlane,discToHalfPlane_halfPlaneToDisc] using hpB
    · apply (N.mem_carrier _).mpr
      simpa only [discToHalfPlane_halfPlaneToDisc] using hpN

theorem DiscLine.isComplementaryTransversal_iff_halfPlane (L M N : DiscLine) (θ : ℝ) :
    L.IsComplementaryTransversal M θ N ↔ L.toHalfPlane.IsComplementaryTransversal M.toHalfPlane θ N.toHalfPlane := by
  constructor
  · rintro ⟨hT,B,hB,hNB⟩
    exact ⟨(L.isThetaTransversal_iff_halfPlane M N θ).mp hT,B.toHalfPlane,
      (L.bisectorSet_eq_iff_halfPlane M B).mp hB,(N.orthogonal_iff_halfPlane B).mp hNB⟩
  · rintro ⟨hT,B,hB,hNB⟩
    refine ⟨(L.isThetaTransversal_iff_halfPlane M N θ).mpr hT,B.toDiscLine,?_,?_⟩
    · apply (L.bisectorSet_eq_iff_halfPlane M B.toDiscLine).mpr
      simpa only [HalfPlaneLine.toDiscLine_toHalfPlane] using hB
    · apply (N.orthogonal_iff_halfPlane B.toDiscLine).mpr
      simpa only [HalfPlaneLine.toDiscLine_toHalfPlane] using hNB

theorem DiscLine.alternateSet_eq_cayley_image (L M : DiscLine) (θ : ℝ) :
    {N : DiscLine | L.IsAlternateTransversal M θ N}=
      HalfPlaneLine.toDiscLine '' {N : HalfPlaneLine | L.toHalfPlane.IsAlternateTransversal M.toHalfPlane θ N} := by
  ext N
  constructor
  · intro hN
    exact ⟨N.toHalfPlane,(L.isAlternateTransversal_iff_halfPlane M N θ).mp hN,N.toHalfPlane_spec⟩
  · rintro ⟨P,hP,rfl⟩
    change L.toHalfPlane.IsAlternateTransversal M.toHalfPlane θ P at hP
    apply (L.isAlternateTransversal_iff_halfPlane M P.toDiscLine θ).mpr
    simpa only [HalfPlaneLine.toDiscLine_toHalfPlane] using hP

theorem DiscLine.complementarySet_eq_cayley_image (L M : DiscLine) (θ : ℝ) :
    {N : DiscLine | L.IsComplementaryTransversal M θ N}=
      HalfPlaneLine.toDiscLine '' {N : HalfPlaneLine | L.toHalfPlane.IsComplementaryTransversal M.toHalfPlane θ N} := by
  ext N
  constructor
  · intro hN
    exact ⟨N.toHalfPlane,(L.isComplementaryTransversal_iff_halfPlane M N θ).mp hN,N.toHalfPlane_spec⟩
  · rintro ⟨P,hP,rfl⟩
    change L.toHalfPlane.IsComplementaryTransversal M.toHalfPlane θ P at hP
    apply (L.isComplementaryTransversal_iff_halfPlane M P.toDiscLine θ).mpr
    simpa only [HalfPlaneLine.toDiscLine_toHalfPlane] using hP

theorem DiscLine.alternate_transversals_ncard (L M : DiscLine) (hd : L.HDisjoint M)
    (θ : ℝ) (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    {N : DiscLine | L.IsAlternateTransversal M θ N}.ncard=2 := by
  rw [L.alternateSet_eq_cayley_image,Set.ncard_image_of_injective _ HalfPlaneLine.toDiscLine_injective]
  exact L.toHalfPlane.alternate_transversals_ncard M.toHalfPlane ((L.hDisjoint_iff_halfPlane M).mp hd) θ h0 hθ

theorem DiscLine.complementary_transversals_ncard (L M : DiscLine) (hd : L.HDisjoint M)
    (θ : ℝ) (h0 : 0<θ) (hθ : θ<Real.pi/2) :
    {N : DiscLine | L.IsComplementaryTransversal M θ N}.ncard=2 := by
  rw [L.complementarySet_eq_cayley_image,Set.ncard_image_of_injective _ HalfPlaneLine.toDiscLine_injective]
  exact L.toHalfPlane.complementary_transversals_ncard M.toHalfPlane ((L.hDisjoint_iff_halfPlane M).mp hd) θ h0 hθ

theorem DiscLine.theta_transversal_types_exclusive (L M : DiscLine) (hd : L.HDisjoint M)
    (θ : ℝ) (h0 : 0<θ) (hθ : θ<Real.pi/2) (N : DiscLine) (hN : L.IsThetaTransversal M θ N) :
    (L.IsAlternateTransversal M θ N ∧ ¬L.IsComplementaryTransversal M θ N) ∨
      (L.IsComplementaryTransversal M θ N ∧ ¬L.IsAlternateTransversal M θ N) := by
  rw [L.isAlternateTransversal_iff_halfPlane M N θ,L.isComplementaryTransversal_iff_halfPlane M N θ]
  exact L.toHalfPlane.theta_transversal_types_exclusive M.toHalfPlane ((L.hDisjoint_iff_halfPlane M).mp hd)
    θ h0 hθ N.toHalfPlane ((L.isThetaTransversal_iff_halfPlane M N θ).mp hN)

end
end LowDimensionalTopology.Geometry.Hyperbolic
