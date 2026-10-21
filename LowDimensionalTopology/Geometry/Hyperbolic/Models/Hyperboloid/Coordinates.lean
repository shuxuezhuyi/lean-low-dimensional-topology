/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Ball.PathMetric

/-!
# The hyperboloid and its projective ball chart

Lorentz vectors use a time coordinate and a Euclidean spatial coordinate.
The positive sheet is homeomorphic to the actual open unit ball. The
Lorentz-orthogonal tangent space has a positive length element, including
for derivatives of actual curves in the sheet. Path-distance comparison
with the ball is a subsequent construction.
-/

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}










def hyperboloidProjectRaw (x : LorentzVector n) : Inversive.Euclidean n :=
  (1+x.1)⁻¹ • x.2

theorem hyperboloidProjectRaw_norm_sq (x : Hyperboloid n) :
    ‖hyperboloidProjectRaw x.val‖^2=(x.val.1-1)/(x.val.1+1) := by
  have hx := hyperboloid_time_sq x
  have hp : 0<x.val.1+1 := by linarith [x.property.2]
  simp only [hyperboloidProjectRaw,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow]
  rw [add_comm 1]
  field_simp [hp.ne']
  nlinarith

theorem hyperboloidProjectRaw_mem_ball (x : Hyperboloid n) :
    hyperboloidProjectRaw x.val ∈ unitBallDomain n := by
  have hnorm := hyperboloidProjectRaw_norm_sq x
  have hp : 0<x.val.1+1 := by linarith [x.property.2]
  have hquot : (x.val.1-1)/(x.val.1+1)<1 := (div_lt_one hp).mpr (by linarith)
  change dist (hyperboloidProjectRaw x.val) 0<1
  rw [dist_zero_right]
  nlinarith [norm_nonneg (hyperboloidProjectRaw x.val)]

def hyperboloidProject (x : Hyperboloid n) : unitBallDomain n :=
  ⟨hyperboloidProjectRaw x.val,hyperboloidProjectRaw_mem_ball x⟩

def ballHyperboloidRaw (y : Inversive.Euclidean n) : LorentzVector n :=
  ((1+‖y‖^2)/(1-‖y‖^2), (2/(1-‖y‖^2)) • y)

theorem ballHyperboloidRaw_mem (y : unitBallDomain n) :
    ballHyperboloidRaw y.val ∈ hyperboloidSet n := by
  have hy := unitBallDomain_norm_lt y
  have hd : 0<1-‖y.val‖^2 := by nlinarith [norm_nonneg y.val]
  constructor
  · rw [lorentzForm_self]
    simp only [ballHyperboloidRaw,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_pow]
    field_simp
    ring
  · change 0<(1+‖y.val‖^2)/(1-‖y.val‖^2)
    exact div_pos (by positivity) hd

def ballHyperboloid (y : unitBallDomain n) : Hyperboloid n :=
  ⟨ballHyperboloidRaw y.val,ballHyperboloidRaw_mem y⟩

theorem ballHyperboloid_hyperboloidProject (x : Hyperboloid n) :
    ballHyperboloid (hyperboloidProject x)=x := by
  have ht : 0<x.val.1+1 := by linarith [x.property.2]
  have hden : 0<1-(x.val.1-1)/(x.val.1+1) :=
    sub_pos.mpr ((div_lt_one ht).mpr (by linarith))
  apply Subtype.ext
  apply Prod.ext
  · change (1+‖hyperboloidProjectRaw x.val‖^2)/(1-‖hyperboloidProjectRaw x.val‖^2)=x.val.1
    rw [hyperboloidProjectRaw_norm_sq]
    field_simp [hden.ne',ht.ne']
    ring
  · change (2/(1-‖hyperboloidProjectRaw x.val‖^2)) • hyperboloidProjectRaw x.val=x.val.2
    rw [hyperboloidProjectRaw_norm_sq]
    unfold hyperboloidProjectRaw
    rw [smul_smul]
    have hc : 2/(1-(x.val.1-1)/(x.val.1+1)) * (1+x.val.1)⁻¹=1 := by
      rw [add_comm 1]
      field_simp [hden.ne',ht.ne']
      ring
    rw [hc,one_smul]

theorem hyperboloidProject_ballHyperboloid (y : unitBallDomain n) :
    hyperboloidProject (ballHyperboloid y)=y := by
  have hy := unitBallDomain_norm_lt y
  have hd : 0<1-‖y.val‖^2 := by nlinarith [norm_nonneg y.val]
  apply Subtype.ext
  change (1+(1+‖y.val‖^2)/(1-‖y.val‖^2))⁻¹ • ((2/(1-‖y.val‖^2)) • y.val)=y.val
  rw [smul_smul]
  have hc : (1+(1+‖y.val‖^2)/(1-‖y.val‖^2))⁻¹ * (2/(1-‖y.val‖^2))=1 := by
    have hp : 0<1+(1+‖y.val‖^2)/(1-‖y.val‖^2) :=
      by positivity
    field_simp [hp.ne',hd.ne']
    ring
  rw [hc,one_smul]

def hyperboloidBallHomeomorph (n : ℕ) : Hyperboloid n ≃ₜ unitBallDomain n where
  toFun := hyperboloidProject
  invFun := ballHyperboloid
  left_inv := ballHyperboloid_hyperboloidProject
  right_inv := hyperboloidProject_ballHyperboloid
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun x : Hyperboloid n => (1+x.val.1)⁻¹ • x.val.2)
    exact ((continuous_const.add continuous_subtype_val.fst).inv₀
      (fun x => by
        change 1+x.val.1≠0
        have hp := x.property.2
        linarith)).smul continuous_subtype_val.snd
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun y : unitBallDomain n => ‖y.val‖^2) :=
      (continuous_norm.comp continuous_subtype_val).pow 2
    have hd : Continuous (fun y : unitBallDomain n => 1-‖y.val‖^2) := continuous_const.sub hc
    have hn : ∀ y : unitBallDomain n, 1-‖y.val‖^2≠0 := by
      intro y
      have h:=unitBallDomain_norm_lt y
      have hp : 0<1-‖y.val‖^2 := by nlinarith [norm_nonneg y.val]
      exact hp.ne'
    exact ((continuous_const.add hc).div hd hn).prodMk
      ((continuous_const.div hd hn).smul continuous_subtype_val)

def hyperboloidLineElement (v : LorentzVector n) : ℝ := Real.sqrt (-lorentzForm v v)

theorem hyperboloidLineElement_sq (x : Hyperboloid n) (v : LorentzVector n)
    (hv : HyperboloidTangent x v) :
    (hyperboloidLineElement v)^2=‖v.2‖^2-v.1^2 := by
  have hn : 0≤-lorentzForm v v := by
    by_cases h0 : v=0
    · simp [h0,lorentzForm]
    · exact (hyperboloid_tangent_positive x v hv h0).le
  rw [hyperboloidLineElement,Real.sq_sqrt hn,lorentzForm_self]
  ring

theorem hyperboloid_curve_tangent {c : ℝ → LorentzVector n} {v : LorentzVector n} {t : ℝ}
    (hc : HasDerivAt c v t)
    (hQ : ∀ᶠ u in nhds t, c u ∈ hyperboloidSet n) :
    lorentzForm (c t) v=0 := by
  have ht : HasDerivAt (fun u => (c u).1) v.1 t := by
    simpa using hc.hasFDerivAt.fst.hasDerivAt
  have hs : HasDerivAt (fun u => (c u).2) v.2 t := by
    simpa using hc.hasFDerivAt.snd.hasDerivAt
  have hd := (ht.mul ht).sub (hs.inner ℝ hs)
  have he : (fun _ : ℝ => (1 : ℝ)) =ᶠ[nhds t]
      (fun u => (c u).1*(c u).1-inner ℝ (c u).2 (c u).2) := by
    filter_upwards [hQ] with u hu
    exact hu.1.symm
  have hderiv := (hd.congr_of_eventuallyEq he).unique (hasDerivAt_const t (1 : ℝ))
  unfold lorentzForm
  nlinarith [real_inner_comm (c t).2 v.2]

theorem hyperboloid_curve_lineElement_sq {c : ℝ → LorentzVector n}
    {v : LorentzVector n} {t : ℝ} (hc : HasDerivAt c v t)
    (hQ : ∀ u, c u ∈ hyperboloidSet n) :
    (hyperboloidLineElement v)^2=‖v.2‖^2-v.1^2 :=
  hyperboloidLineElement_sq ⟨c t,hQ t⟩ v
    (hyperboloid_curve_tangent hc (Filter.Eventually.of_forall hQ))

def hyperboloidCurveLength (c : ℝ → LorentzVector n) (a b : ℝ) : ℝ :=
  ∫ t in a..b, hyperboloidLineElement (deriv c t)

end LowDimensionalTopology.Geometry.Hyperbolic
