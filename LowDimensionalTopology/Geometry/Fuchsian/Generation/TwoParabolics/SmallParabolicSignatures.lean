/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Data
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Fuchsian

theorem parabolic_signature_small_genus (s : FuchsianSignature)
    (hp : 1≤s.parabolicEnds) (hs : s.deficit<1/2) : s.genus=0 := by
  have hsum:=signature_elliptic_sum_lower s.ellipticOrders s.ellipticOrders_two_le
  have hn : (0:ℝ)≤s.ellipticOrders.length:=Nat.cast_nonneg _
  have hP : (1:ℝ)≤s.parabolicEnds:=by exact_mod_cast hp
  have hB : (0:ℝ)≤s.boundaryHyperbolicEnds:=Nat.cast_nonneg _
  have hg : (s.genus:ℝ)<1:=by unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit at hs;linarith
  have hgN : s.genus<1:=by exact_mod_cast hg
  omega

theorem parabolic_signature_small_ends (s : FuchsianSignature)
    (hp : 1≤s.parabolicEnds) (hpos : 0<s.deficit) (hs : s.deficit<1/2) :
    s.parabolicEnds=1 ∧ s.boundaryHyperbolicEnds=0 := by
  have hg:=parabolic_signature_small_genus s hp hs
  have hl:=signature_elliptic_sum_lower s.ellipticOrders s.ellipticOrders_two_le
  have hn : (0:ℝ)≤s.ellipticOrders.length:=Nat.cast_nonneg _
  have hends : s.parabolicEnds+s.boundaryHyperbolicEnds≤2 := by
    have hr : (s.parabolicEnds:ℝ)+s.boundaryHyperbolicEnds<3:=by
      unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit at hs
      rw [hg] at hs
      norm_num at hs
      simp only [one_div] at hl
      linarith
    have hnat : s.parabolicEnds+s.boundaryHyperbolicEnds<3:=by exact_mod_cast hr
    omega
  have hnot : s.parabolicEnds+s.boundaryHyperbolicEnds≠2 := by
    intro he
    have heR : (s.parabolicEnds:ℝ)+s.boundaryHyperbolicEnds=2:=by exact_mod_cast he
    have hdelta : s.deficit=(s.ellipticOrders.map (fun m:ℕ=>1-1/(m:ℝ))).sum := by
      unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit
      rw [hg]
      norm_num
      linarith
    have hlen : s.ellipticOrders.length<1 := by
      have hr : (s.ellipticOrders.length:ℝ)<1:=by rw [hdelta] at hs;linarith
      exact_mod_cast hr
    have hempty : s.ellipticOrders=[]:=List.length_eq_zero_iff.mp (by omega)
    rw [hdelta,hempty] at hpos
    norm_num at hpos
  omega

theorem parabolic_signature_small_two_orders (s : FuchsianSignature)
    (hp : 1≤s.parabolicEnds) (hpos : 0<s.deficit) (hs : s.deficit<1/2) :
    s.ellipticOrders.length=2 := by
  have hg:=parabolic_signature_small_genus s hp hs
  obtain ⟨hP,hB⟩:=parabolic_signature_small_ends s hp hpos hs
  have hdelta : s.deficit= -1+(s.ellipticOrders.map (fun m:ℕ=>1-1/(m:ℝ))).sum := by
    simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, hg, hP, hB, Nat.cast_zero,
      Nat.cast_one]
    ring
  have hl:=signature_elliptic_sum_lower s.ellipticOrders s.ellipticOrders_two_le
  have hne : s.ellipticOrders≠[]:=by intro he;rw [hdelta,he] at hpos;norm_num at hpos
  have hu:=signature_elliptic_sum_lt_length s.ellipticOrders s.ellipticOrders_two_le hne
  rw [hdelta] at hpos hs
  have hrlo : (1:ℝ)<s.ellipticOrders.length:=by linarith
  have hrhi : (s.ellipticOrders.length:ℝ)<3:=by linarith
  have hlo : 1<s.ellipticOrders.length:=by exact_mod_cast hrlo
  have hhi : s.ellipticOrders.length<3:=by exact_mod_cast hrhi
  omega

theorem parabolic_small_pair_classification (p q : ℕ) (hp : 2≤p) (hpq : p≤q)
    (hpos : 0<1-1/(p:ℝ)-1/(q:ℝ)) (hs : 1-1/(p:ℝ)-1/(q:ℝ)<1/2) :
    (p=2 ∧ 3≤q) ∨ (p=3 ∧ (q=3 ∨ q=4 ∨ q=5)) := by
  have hp4 : p<4 := by
    by_contra hn
    have h4p : 4≤p:=by omega
    have h4q : 4≤q:=by omega
    have h1:=signature_reciprocal_le 4 p (by decide) h4p
    have h2:=signature_reciprocal_le 4 q (by decide) h4q
    norm_num at h1 h2
    simp only [one_div] at hs
    linarith
  have hc : p=2 ∨ p=3:=by omega
  rcases hc with rfl|rfl
  · left
    refine ⟨rfl,?_⟩
    by_contra hn
    have hq : q=2:=by omega
    rw [hq] at hpos
    norm_num at hpos
  · right
    refine ⟨rfl,?_⟩
    have hq6 : q<6 := by
      by_contra hn
      have h6q : 6≤q:=by omega
      have h2:=signature_reciprocal_le 6 q (by decide) h6q
      norm_num at h2 hs
      linarith
    omega

/-- Complete numerical classification, with no initial restriction on the genus,
the number of ends, or the elliptic-order list. The geometric area bridge is separate. -/
theorem parabolic_signature_below_half (s : FuchsianSignature)
    (hp : 1≤s.parabolicEnds) (hpos : 0<s.deficit) (hs : s.deficit<1/2) :
    s.genus=0 ∧ s.parabolicEnds=1 ∧ s.boundaryHyperbolicEnds=0 ∧
      ((∃q:ℕ,3≤q ∧ s.ellipticOrders.Perm [2,q]) ∨
        (∃q:ℕ,(q=3 ∨ q=4 ∨ q=5) ∧ s.ellipticOrders.Perm [3,q])) := by
  have hg:=parabolic_signature_small_genus s hp hs
  obtain ⟨hP,hB⟩:=parabolic_signature_small_ends s hp hpos hs
  have hlen:=parabolic_signature_small_two_orders s hp hpos hs
  obtain ⟨a,b,hab⟩:=List.length_eq_two.mp hlen
  have ha : 2≤a:=s.ellipticOrders_two_le a (by rw [hab];simp)
  have hb : 2≤b:=s.ellipticOrders_two_le b (by rw [hab];simp)
  have hdelta : s.deficit=1-1/(a:ℝ)-1/(b:ℝ) := by
    simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit,hg,hP,hB,hab,Nat.cast_zero,Nat.cast_one,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    ring
  rw [hdelta] at hpos hs
  refine ⟨hg,hP,hB,?_⟩
  rcases le_total a b with hab'|hba
  · rcases parabolic_small_pair_classification a b ha hab' hpos hs with hc|hc
    · left
      refine ⟨b,hc.2,?_⟩
      rw [hab,hc.1]
    · right
      refine ⟨b,hc.2,?_⟩
      rw [hab,hc.1]
  · have hd : 1-1/(b:ℝ)-1/(a:ℝ)=1-1/(a:ℝ)-1/(b:ℝ):=by ring
    rcases parabolic_small_pair_classification b a hb hba (by rw [hd];exact hpos)
      (by rw [hd];exact hs) with hc|hc
    · left
      refine ⟨a,hc.2,?_⟩
      rw [hab,hc.1]
      exact List.Perm.swap _ _ []
    · right
      refine ⟨a,hc.2,?_⟩
      rw [hab,hc.1]
      exact List.Perm.swap _ _ []

/-- The same complete numerical classification in the geometric area-expression scale. -/
theorem parabolic_signature_area_below_pi (s : FuchsianSignature)
    (hp : 1≤s.parabolicEnds) (hpos : 0<s.areaFormulaValue)
    (hs : s.areaFormulaValue<Real.pi) :
    s.genus=0 ∧ s.parabolicEnds=1 ∧ s.boundaryHyperbolicEnds=0 ∧
      ((∃q:ℕ,3≤q ∧ s.ellipticOrders.Perm [2,q]) ∨
        (∃q:ℕ,(q=3 ∨ q=4 ∨ q=5) ∧ s.ellipticOrders.Perm [3,q])) := by
  have hpπ:=Real.pi_pos
  have hmul : 0<2*Real.pi:=by positivity
  have hdpos : 0<s.deficit:=by
    unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.areaFormulaValue at hpos
    exact (mul_pos_iff_of_pos_left hmul).mp hpos
  have hdsmall : s.deficit<1/2:=by
    unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.areaFormulaValue at hs
    nlinarith
  exact parabolic_signature_below_half s hp hdpos hdsmall

theorem finite_hecke_deficit_bounds (q : ℕ) (hq : 3≤q) :
    0<1/2-1/(q:ℝ) ∧ 1/2-1/(q:ℝ)<1/2 := by
  have hrec:=signature_reciprocal_le 3 q (by decide) hq
  have hpos : 0<1/(q:ℝ):=one_div_pos.mpr (by exact_mod_cast (show 0<q by omega))
  norm_num at hrec
  simp only [one_div] at hpos ⊢
  constructor <;> linarith

theorem finite_hecke_deficit_mono (p q : ℕ) (hp : 3≤p) (hpq : p≤q) :
    1/2-1/(p:ℝ)≤1/2-1/(q:ℝ) := by
  have h:=signature_reciprocal_le p q (by omega) hpq
  linarith

/-- The exact arithmetic contradiction used after the genuine index-area and torsion
order comparisons. Those geometric/group comparisons are not asserted here. -/
theorem finite_hecke_proper_index_impossible (p q k : ℕ) (hp : 3≤p) (hpq : p≤q)
    (hk : 2≤k) :
    (k:ℝ)*(1/2-1/(q:ℝ))≠1/2-1/(p:ℝ) := by
  have hpos:=(finite_hecke_deficit_bounds p hp).1
  have hmono:=finite_hecke_deficit_mono p q hp hpq
  have hkR : (2:ℝ)≤k:=by exact_mod_cast hk
  intro he
  nlinarith [mul_le_mul_of_nonneg_right hkR (show 0≤1/2-1/(q:ℝ) by linarith)]

end LowDimensionalTopology.Geometry.Fuchsian
