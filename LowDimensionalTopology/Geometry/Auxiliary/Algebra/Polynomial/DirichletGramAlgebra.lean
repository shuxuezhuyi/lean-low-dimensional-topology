/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Polynomial identities for Möbius displacement

Coefficient identities for a Gram expression distinguish diagonal, translation and
rotation normal forms of real Möbius transformations. The calculations take place
in real polynomial rings after clearing the common metric denominator.
-/

@[expose] public section
noncomputable section
open Polynomial
namespace LowDimensionalTopology.Geometry.Auxiliary.Algebra

/-- The squared norm of the actual real Mobius displacement numerator along an arbitrary real polynomial curve. -/
def gramDisplacementNormPolynomial (a b c d : ℝ) (x y : Polynomial ℝ) : Polynomial ℝ :=
  (C c*(x^2-y^2)+C (d-a)*x-C b)^2+y^2*(C 2*C c*x+C (d-a))^2

/-- The actual three-center Gram expression after clearing the positive common metric denominator. -/
def gramPairPolynomial (a b c d e f g h : ℝ) (x y : Polynomial ℝ) : Polynomial ℝ :=
  4*gramDisplacementNormPolynomial a b c d x y*gramDisplacementNormPolynomial e f g h x y-
    (gramDisplacementNormPolynomial a b c d x y+gramDisplacementNormPolynomial e f g h x y-
      gramDisplacementNormPolynomial (d*e-b*g) (d*f-b*h) (a*g-c*e) (a*h-c*f) x y)^2

/-- For a genuine hyperbolic diagonal normal form the constant coefficient forces the second map's upper-right coefficient to vanish. -/
theorem gramPair_diagonal_coeff_zero (t a b c d : ℝ) :
    (gramPairPolynomial t 0 0 (1/t) a b c d 0 X).coeff 0=
      -(b^2-(b/t)^2)^2 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [gramPairPolynomial,gramDisplacementNormPolynomial]
  ring

/-- The highest coefficient detects the second map's lower-left coefficient in the same genuine hyperbolic normal form. -/
theorem gramPair_diagonal_coeff_eight (t a b c d : ℝ) :
    (gramPairPolynomial t 0 0 (1/t) a b c d 0 X).coeff 8=
      -(c^2-(t*c)^2)^2 := by
  unfold gramPairPolynomial gramDisplacementNormPolynomial
  ring_nf
  simp only [mul_assoc,←Polynomial.C_ofNat,←Polynomial.C_mul,←Polynomial.C_pow,Polynomial.coeff_add,
    Polynomial.coeff_sub,Polynomial.coeff_neg,Polynomial.coeff_mul_C,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow,Polynomial.coeff_C]
  norm_num
  ring

/-- A genuine nontrivial parabolic normal form has a highest coefficient which detects a different fixed point. -/
theorem gramPair_translation_coeff_six (t a b c d : ℝ) :
    (gramPairPolynomial 1 t 0 1 a b c d X 0).coeff 6= -4*t^2*c^4 := by
  unfold gramPairPolynomial gramDisplacementNormPolynomial
  ring_nf
  simp only [mul_assoc,←Polynomial.C_ofNat,←Polynomial.C_mul,←Polynomial.C_pow,Polynomial.coeff_add,
    Polynomial.coeff_sub,Polynomial.coeff_neg,Polynomial.coeff_mul_C,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow,Polynomial.coeff_X,Polynomial.coeff_C]
  norm_num
  ring

/-- Once the parabolic highest coefficient vanishes, the remaining pure-height coefficient detects the two diagonal entries. -/
theorem gramPair_translation_coeff_two_of_c_zero (t a b d : ℝ) :
    (gramPairPolynomial 1 t 0 1 a b 0 d 0 X).coeff 2=4*t^2*(a-d)^2 := by
  unfold gramPairPolynomial gramDisplacementNormPolynomial
  ring_nf
  simp only [mul_assoc,←Polynomial.C_ofNat,←Polynomial.C_mul,←Polynomial.C_pow,Polynomial.coeff_add,
    Polynomial.coeff_sub,Polynomial.coeff_mul_C,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow,Polynomial.coeff_C]
  norm_num
  ring


/-- The three scalar coefficients which determine the second coefficient of a genuine polynomial product. -/
theorem gramPolynomial_coeff_two_mul (P Q : Polynomial ℝ) :
    (P*Q).coeff 2=P.coeff 0*Q.coeff 2+P.coeff 1*Q.coeff 1+P.coeff 2*Q.coeff 0 := by
  rw [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

/-- The exact second coefficient of Gram degeneracy at a fixed point of the first transformation. -/
theorem gramPolynomial_coeff_two_fixed (G H K : Polynomial ℝ) (N : ℝ)
    (hG0 : G.coeff 0=0) (hG1 : G.coeff 1=0) (hH0 : H.coeff 0=N) (hK0 : K.coeff 0=N) :
    (4*G*H-(G+H-K)^2).coeff 2=4*G.coeff 2*N-(H.coeff 1-K.coeff 1)^2 := by
  rw [show 4*G*H=4*(G*H) by ring,Polynomial.coeff_sub,Polynomial.coeff_ofNat_mul,
    pow_two,gramPolynomial_coeff_two_mul,gramPolynomial_coeff_two_mul]
  simp only [Polynomial.coeff_sub,Polynomial.coeff_add,hG0,hG1,hH0,hK0]
  ring

/-- The exact value at the actual upper-half-plane elliptic fixed point. -/
theorem gramNorm_at_i_coeff_zero (a b c d dx dy : ℝ) :
    (gramDisplacementNormPolynomial a b c d (C dx*X) (1+C dy*X)).coeff 0=
      (b+c)^2+(d-a)^2 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [gramDisplacementNormPolynomial]
  ring

/-- The first-order displacement numerator at the actual elliptic fixed point. -/
theorem gramNorm_at_i_coeff_one (a b c d dx dy : ℝ) :
    (gramDisplacementNormPolynomial a b c d (C dx*X) (1+C dy*X)).coeff 1=
      dx*(2*(c-b)*(d-a))+dy*(4*c*(c+b)+2*(d-a)^2) := by
  unfold gramDisplacementNormPolynomial
  ring_nf
  simp only [mul_assoc,←Polynomial.C_ofNat,←Polynomial.C_mul,←Polynomial.C_pow,
    Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
    Polynomial.coeff_mul_C,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,Polynomial.coeff_C]
  norm_num
  ring

/-- The first nonzero numerator coefficient for a genuine elliptic rotation is quadratic and isotropic. -/
theorem gramNorm_rotation_at_i_coeff_two (u v dx dy : ℝ) :
    (gramDisplacementNormPolynomial u v (-v) u (C dx*X) (1+C dy*X)).coeff 2=
      4*v^2*(dx^2+dy^2) := by
  unfold gramDisplacementNormPolynomial
  ring_nf
  simp only [mul_assoc,←Polynomial.C_ofNat,←Polynomial.C_mul,←Polynomial.C_pow,
    Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
    Polynomial.coeff_mul_C,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,Polynomial.coeff_C]
  norm_num
  ring

/-- The actual first-coordinate variation of a rotated displacement numerator. -/
theorem gram_rotation_first_variation_x (u v a b c d : ℝ) (hunit : u^2+v^2=1) :
    2*(c-b)*(d-a)-2*((v*a+u*c)-(u*b-v*d))*((v*b+u*d)-(u*a-v*c))=
      2*v*(u*(a^2+b^2-c^2-d^2)-2*v*(a*c+b*d)) := by
  linear_combination -2*(a-d)*(b-c)*hunit

/-- The actual second-coordinate variation of the same rotated displacement numerator. -/
theorem gram_rotation_first_variation_y (u v a b c d : ℝ) (hunit : u^2+v^2=1) :
    4*c*(c+b)+2*(d-a)^2-
      (4*(v*a+u*c)*((v*a+u*c)+(u*b-v*d))+2*((v*b+u*d)-(u*a-v*c))^2)=
      -2*v*(v*(a^2+b^2-c^2-d^2)+2*u*(a*c+b*d)) := by
  linear_combination -2*(a^2-2*a*d+2*b*c+2*c^2+d^2)*hunit

/-- The two spatial displacement components satisfy the exact determinant-one norm identity. -/
theorem gram_rotation_spatial_identity (a b c d : ℝ) (hdet : a*d-b*c=1) :
    (a^2+b^2-c^2-d^2)^2+4*(a*c+b*d)^2=
      ((a-d)^2+(b+c)^2)*(((a-d)^2+(b+c)^2)+4) := by
  linear_combination 4*((a-d)^2+(b+c)^2)*hdet

/-- The genuine second-order metric degeneration at an elliptic fixed point has an explicit two-dimensional quadratic form. -/
theorem gramPair_rotation_at_i_coeff_two (u v a b c d dx dy : ℝ) (hunit : u^2+v^2=1) :
    (gramPairPolynomial u v (-v) u a b c d (C dx*X) (1+C dy*X)).coeff 2=
      16*v^2*((a-d)^2+(b+c)^2)*(dx^2+dy^2)-
      (dx*(2*v*(u*(a^2+b^2-c^2-d^2)-2*v*(a*c+b*d)))+
        dy*(-2*v*(v*(a^2+b^2-c^2-d^2)+2*u*(a*c+b*d))))^2 := by
  let G:=gramDisplacementNormPolynomial u v (-v) u (C dx*X) (1+C dy*X)
  let H:=gramDisplacementNormPolynomial a b c d (C dx*X) (1+C dy*X)
  let K:=gramDisplacementNormPolynomial (u*a-v*c) (u*b-v*d) (u*c+v*a) (u*d+v*b)
    (C dx*X) (1+C dy*X)
  let N:ℝ:=(a-d)^2+(b+c)^2
  let Lx:ℝ:=2*v*(u*(a^2+b^2-c^2-d^2)-2*v*(a*c+b*d))
  let Ly:ℝ:= -2*v*(v*(a^2+b^2-c^2-d^2)+2*u*(a*c+b*d))
  have hG0 : G.coeff 0=0 := by rw [gramNorm_at_i_coeff_zero];ring
  have hG1 : G.coeff 1=0 := by rw [gramNorm_at_i_coeff_one];ring
  have hH0 : H.coeff 0=N := by rw [gramNorm_at_i_coeff_zero];dsimp [N];ring
  have hK0 : K.coeff 0=N := by
    rw [gramNorm_at_i_coeff_zero]
    dsimp [N]
    linear_combination ((a-d)^2+(b+c)^2)*hunit
  have hL : H.coeff 1-K.coeff 1=dx*Lx+dy*Ly := by
    rw [gramNorm_at_i_coeff_one,gramNorm_at_i_coeff_one]
    dsimp [Lx,Ly]
    linear_combination dx*(gram_rotation_first_variation_x u v a b c d hunit)+
      dy*(gram_rotation_first_variation_y u v a b c d hunit)
  unfold gramPairPolynomial
  simp only [neg_mul,sub_neg_eq_add]
  change (4*G*H-(G+H-K)^2).coeff 2=_
  rw [gramPolynomial_coeff_two_fixed G H K N hG0 hG1 hH0 hK0,hL]
  change 4*(gramDisplacementNormPolynomial u v (-v) u (C dx*X) (1+C dy*X)).coeff 2*N-
    (dx*Lx+dy*Ly)^2=_
  rw [gramNorm_rotation_at_i_coeff_two]
  dsimp [N,Lx,Ly]
  ring

/-- Identical two-dimensional Gram degeneration for a genuine nonidentity elliptic rotation forces a common actual interior fixed point. -/
theorem gramPair_rotation_zero_forces_rotation (u v a b c d : ℝ)
    (hunit : u^2+v^2=1) (hv : v≠0) (hdet : a*d-b*c=1)
    (hline : ∀dx dy : ℝ,gramPairPolynomial u v (-v) u a b c d (C dx*X) (1+C dy*X)=0) :
    a=d ∧ b= -c := by
  let N:ℝ:=(a-d)^2+(b+c)^2
  let U:ℝ:=a*c+b*d
  let W:ℝ:=a^2+b^2-c^2-d^2
  let Lx:ℝ:=2*v*(u*W-2*v*U)
  let Ly:ℝ:= -2*v*(v*W+2*u*U)
  have hnorm : Lx^2+Ly^2=4*v^2*N*(N+4) := by
    calc
      Lx^2+Ly^2=4*v^2*(u^2+v^2)*(W^2+4*U^2) := by dsimp [Lx,Ly];ring
      _=4*v^2*N*(N+4) := by
        rw [hunit,mul_one]
        have hh:=gram_rotation_spatial_identity a b c d hdet
        change W^2+4*U^2=N*(N+4) at hh
        rw [hh]
        ring
  have hzero:=congrArg (fun p : Polynomial ℝ=>p.coeff 2) (hline Ly (-Lx))
  rw [gramPair_rotation_at_i_coeff_two _ _ _ _ _ _ _ _ hunit,Polynomial.coeff_zero] at hzero
  change 16*v^2*N*(Ly^2+(-Lx)^2)-(Ly*Lx+(-Lx)*Ly)^2=0 at hzero
  have he : 16*v^2*N*(Lx^2+Ly^2)=0 := by
    have hid : 16*v^2*N*(Ly^2+(-Lx)^2)-(Ly*Lx+(-Lx)*Ly)^2 =
        16*v^2*N*(Lx^2+Ly^2) := by ring
    exact hid.symm.trans hzero
  have hN : N=0 := by
    have hn : 0≤N:=by dsimp [N];positivity
    by_contra hne
    have hp : 0<N:=lt_of_le_of_ne hn (Ne.symm hne)
    have hnormpos : 0<Lx^2+Ly^2 := by rw [hnorm];positivity
    have hprod : 0<16*v^2*N*(Lx^2+Ly^2):=by positivity
    exact (ne_of_gt hprod) he
  have had : (a-d)^2=0 := by dsimp [N] at hN;nlinarith only [hN,sq_nonneg (b+c)]
  have hbc : (b+c)^2=0 := by dsimp [N] at hN;nlinarith only [hN,sq_nonneg (a-d)]
  exact ⟨sub_eq_zero.mp (eq_zero_of_pow_eq_zero had),eq_neg_of_add_eq_zero_left (eq_zero_of_pow_eq_zero hbc)⟩

/-- The complete elliptic degeneracy consists only of the identity or the first true transformation, allowing the harmless determinant-one sign. -/
theorem gramPair_rotation_zero_classification (u v a b c d : ℝ)
    (hunit : u^2+v^2=1) (hv : v≠0) (hdet : a*d-b*c=1)
    (hline : ∀dx dy : ℝ,gramPairPolynomial u v (-v) u a b c d (C dx*X) (1+C dy*X)=0) :
    a=d ∧ c= -b ∧ ((b=0 ∧ a^2=1) ∨ ∃k : ℝ,k^2=1 ∧ a=k*u ∧ b=k*v) := by
  obtain ⟨had,hbc⟩:=gramPair_rotation_zero_forces_rotation u v a b c d hunit hv hdet hline
  have hc : c= -b:=by linarith only [hbc]
  subst d
  subst c
  refine ⟨rfl,rfl,?_⟩
  have hAB : a^2+b^2=1:=by nlinarith only [hdet]
  have hh:=congrArg (Polynomial.eval (1:ℝ)) (hline 0 (-1))
  simp [gramPairPolynomial,gramDisplacementNormPolynomial] at hh
  let R:ℝ:=u*b-v*a
  let S:ℝ:=v*b+u*a
  have hzero : 4*v^2*b^2-(v^2+b^2-R^2)^2=0 := by
    dsimp [R]
    convert hh using 1; ring
  have hSR : S^2+R^2=1 := by
    calc
      S^2+R^2=(u^2+v^2)*(a^2+b^2) := by dsimp [S,R];ring
      _=1 := by rw [hunit,hAB];norm_num
  have hmid : v^2+b^2-R^2=2*v*b*S := by
    dsimp [R,S]
    linear_combination -v^2*hAB-b^2*hunit
  have hfactor : 4*v^2*b^2-(v^2+b^2-R^2)^2=4*v^2*b^2*R^2 := by
    rw [hmid]
    linear_combination -4*v^2*b^2*hSR
  have hprod : 4*v^2*b^2*R^2=0:=hfactor.symm.trans hzero
  rcases mul_eq_zero.mp hprod with hleft|hR
  · have hb : b=0:=eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hleft).resolve_left
      (mul_ne_zero (by norm_num : (4:ℝ)≠0) (pow_ne_zero 2 hv)))
    exact Or.inl ⟨hb,by simpa [hb] using hAB⟩
  · have hR0 : R=0:=eq_zero_of_pow_eq_zero hR
    let k:ℝ:=b/v
    have hbK : b=k*v := (div_mul_cancel₀ b hv).symm
    have haK : a=k*u := by
      apply mul_right_cancel₀ hv
      calc
        a*v=u*b := by dsimp [R] at hR0;nlinarith only [hR0]
        _=(k*u)*v := by dsimp [k];field_simp
    have hk : k^2=1 := by
      rw [haK,hbK] at hAB
      have he : (k*u)^2+(k*v)^2=k^2*(u^2+v^2):=by ring
      rw [he,hunit,mul_one] at hAB
      exact hAB
    exact Or.inr ⟨k,hk,haK,hbK⟩

/-- Identical Gram degeneracy for a genuine nontrivial parabolic normal form forces the second map to have the same actual ideal fixed point. -/
theorem gramPair_translation_zero_forces_common_infty (t a b c d : ℝ) (ht : t≠0)
    (hdet : a*d-b*c=1)
    (hX : gramPairPolynomial 1 t 0 1 a b c d X 0=0)
    (hY : gramPairPolynomial 1 t 0 1 a b c d 0 X=0) :
    c=0 ∧ a=d ∧ a^2=1 := by
  have hh:=congrArg (fun p : Polynomial ℝ=>p.coeff 6) hX
  rw [gramPair_translation_coeff_six,Polynomial.coeff_zero] at hh
  have hc : c=0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hh).resolve_left
    (mul_ne_zero (by norm_num : (-4:ℝ)≠0) (pow_ne_zero 2 ht)))
  subst c
  have h2:=congrArg (fun p : Polynomial ℝ=>p.coeff 2) hY
  rw [gramPair_translation_coeff_two_of_c_zero,Polynomial.coeff_zero] at h2
  have he : a-d=0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h2).resolve_left
    (mul_ne_zero (by norm_num : (4:ℝ)≠0) (pow_ne_zero 2 ht)))
  have had : a=d:=sub_eq_zero.mp he
  refine ⟨rfl,had,?_⟩
  rw [mul_zero,sub_zero,←had,←pow_two] at hdet
  exact hdet

/-- In the genuine hyperbolic diagonal normal form, identical Gram degeneracy forces the second map to preserve both actual ideal endpoints. -/
theorem gramPair_diagonal_zero_forces_diagonal (t a b c d : ℝ) (ht : t≠0) (htsq : t^2≠1)
    (hY : gramPairPolynomial t 0 0 (1/t) a b c d 0 X=0) : b=0 ∧ c=0 := by
  have h0:=congrArg (fun p : Polynomial ℝ=>p.coeff 0) hY
  rw [gramPair_diagonal_coeff_zero,Polynomial.coeff_zero,neg_eq_zero] at h0
  have hbe : b^2=(b/t)^2 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)
  rw [div_pow] at hbe
  have hbe':= (eq_div_iff (pow_ne_zero 2 ht)).mp hbe
  have hbprod : b^2*(t^2-1)=0 := by nlinarith only [hbe']
  have hb : b=0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hbprod).resolve_right (sub_ne_zero.mpr htsq))
  have h8:=congrArg (fun p : Polynomial ℝ=>p.coeff 8) hY
  rw [gramPair_diagonal_coeff_eight,Polynomial.coeff_zero,neg_eq_zero] at h8
  have hce : c^2=(t*c)^2 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero h8)
  have hcprod : c^2*(t^2-1)=0 := by nlinarith only [hce]
  have hc : c=0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hcprod).resolve_right (sub_ne_zero.mpr htsq))
  exact ⟨hb,hc⟩

/-- The remaining genuine diagonal degeneracy is only the identity or the first actual map, up to determinant-one representative sign. -/
theorem gramPair_diagonal_zero_classification (t a b c d : ℝ) (ht : t≠0) (htsq : t^2≠1)
    (hdet : a*d-b*c=1) (hY : gramPairPolynomial t 0 0 (1/t) a b c d 0 X=0) :
    b=0 ∧ c=0 ∧ (a^2=1 ∨ a^2=t^2) := by
  obtain ⟨hb,hc⟩:=gramPair_diagonal_zero_forces_diagonal t a b c d ht htsq hY
  refine ⟨hb,hc,?_⟩
  subst b
  subst c
  have hdet' : a*d=1:=by simpa using hdet
  have ha : a≠0:=by intro he;rw [he,zero_mul] at hdet';norm_num at hdet'
  have hd : d=1/a := (eq_div_iff ha).mpr (by nlinarith only [hdet'])
  have hh:=congrArg (Polynomial.eval (1:ℝ)) hY
  simp only [gramPairPolynomial,gramDisplacementNormPolynomial,eval_sub,eval_add,eval_mul,
    eval_pow,eval_C,eval_X,eval_zero,eval_ofNat,zero_mul,mul_zero,zero_add,add_zero,sub_zero,one_pow] at hh
  rw [hd] at hh
  have hfactor : 4*(t-1/t)^2*(a-1/a)^2-
      ((t-1/t)^2+(a-1/a)^2-(a/t-t/a)^2)^2=
      -((t^2-1)^2*(a^2-1)^2*(a^2-t^2)^2)/(a^4*t^4) := by
    field_simp [ha,ht]
    ring
  have he : 4*(t-1/t)^2*(a-1/a)^2-
      ((t-1/t)^2+(a-1/a)^2-(a/t-t/a)^2)^2=0 := by
    convert hh using 1; ring
  rw [hfactor,div_eq_zero_iff,neg_eq_zero] at he
  have hprod := he.resolve_right (mul_ne_zero (pow_ne_zero 4 ha) (pow_ne_zero 4 ht))
  rcases mul_eq_zero.mp hprod with hleft|hright
  · exact Or.inl (sub_eq_zero.mp (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hleft).resolve_left
      (pow_ne_zero 2 (sub_ne_zero.mpr htsq)))))
  · exact Or.inr (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hright))

end LowDimensionalTopology.Geometry.Auxiliary.Algebra
