module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Strict separation and supporting hyperplanes in Euclidean space.

Convex separation supplies linear inequalities and supporting directions. The planar
specializations use the real inner product on the complex plane.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Pointwise

namespace LowDimensionalTopology.Geometry.Euclidean

/-- An actual nonzero normal strictly separates disjoint nonempty open convex planar sets. -/
theorem convex_open_disjoint_strict_separator {U V : Set ℂ}
    (hUc : Convex ℝ U) (hUo : IsOpen U) (hUn : U.Nonempty)
    (hVc : Convex ℝ V) (hVo : IsOpen V) (hVn : V.Nonempty) (hd : Disjoint U V) :
    ∃ (n : ℂ) (t : ℝ), n ≠ 0 ∧ (∀ z ∈ U, inner ℝ n z < t) ∧ ∀ z ∈ V, t < inner ℝ n z := by
  obtain ⟨f, t, hUf, hVf⟩ := geometric_hahn_banach_open_open hUc hUo hVc hVo hd
  have hf : f ≠ 0 := by
    intro he
    obtain ⟨u, hu⟩ := hUn
    obtain ⟨v, hv⟩ := hVn
    have h1 := hUf u hu
    have h2 := hVf v hv
    rw [he] at h1 h2
    simp only [zero_apply] at h1 h2
    exact h1.not_ge h2.le
  let n : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm f
  have hn : n ≠ 0 := by
    intro he
    apply hf
    apply (InnerProductSpace.toDual ℝ ℂ).symm.injective
    simpa only [map_zero] using he
  refine ⟨n, t, hn, ?_, ?_⟩
  · intro z hz
    change inner ℝ ((InnerProductSpace.toDual ℝ ℂ).symm f) z < t
    rw [InnerProductSpace.toDual_symm_apply]
    exact hUf z hz
  · intro z hz
    change t < inner ℝ ((InnerProductSpace.toDual ℝ ℂ).symm f) z
    rw [InnerProductSpace.toDual_symm_apply]
    exact hVf z hz

/-- Strict separation becomes equality on every point common to both closures. -/
theorem inner_eq_of_common_closures {U V : Set ℂ} {n : ℂ} {t : ℝ}
    (hl : ∀ z ∈ U, inner ℝ n z < t) (hr : ∀ z ∈ V, t < inner ℝ n z)
    {x : ℂ} (hx : x ∈ closure U ∩ closure V) : inner ℝ n x = t := by
  have hUl : closure U ⊆ {z | inner ℝ n z ≤ t} := closure_minimal
    (fun z hz => (hl z hz).le) (isClosed_le (continuous_const.inner continuous_id) continuous_const)
  have hVr : closure V ⊆ {z | t ≤ inner ℝ n z} := closure_minimal
    (fun z hz => (hr z hz).le) (isClosed_le continuous_const (continuous_const.inner continuous_id))
  exact le_antisymm (hUl hx.1) (hVr hx.2)

/-- Two affine forms vanishing on the same actual planar line have proportional differences. -/
theorem complex_affine_difference_cross {n m a b x u : ℂ} {t s : ℝ}
    (hn : n ≠ 0) (hm : m ≠ 0) (hab : a ≠ b)
    (hna : inner ℝ n a = t) (hnb : inner ℝ n b = t)
    (hma : inner ℝ m a = s) (hmb : inner ℝ m b = s) :
    (inner ℝ m x - s) * (inner ℝ n u - t) =
      (inner ℝ n x - t) * (inner ℝ m u - s) := by
  have he (z : ℂ) : inner ℝ n z = t ↔ inner ℝ m z = s :=
    complex_affine_equations_iff_of_two_points hn hm hab hna hnb hma hmb
  by_cases hu : inner ℝ n u = t
  · rw [hu, (he u).mp hu, sub_self, sub_self, mul_zero, mul_zero]
  have hden : inner ℝ n u - t ≠ 0 := sub_ne_zero.mpr hu
  let r := (inner ℝ n x - t) / (inner ℝ n u - t)
  let y := x - r • (u - a)
  have hny : inner ℝ n y = t := by
    dsimp only [y]
    rw [inner_sub_right, inner_smul_right, inner_sub_right, hna]
    dsimp only [r]
    field_simp [hden]
    ring
  have hmy := (he y).mp hny
  change inner ℝ m (x - r • (u - a)) = s at hmy
  rw [inner_sub_right, inner_smul_right, inner_sub_right, hma] at hmy
  have hmxy : inner ℝ m x - s = r * (inner ℝ m u - s) := by linarith
  rw [hmxy]
  dsimp only [r]
  field_simp [hden]

/-- Three pairwise disjoint nonempty open convex planar sets cannot share a nondegenerate closed segment. -/
theorem three_disjoint_open_convex_closures_subsingleton {U V W : Set ℂ}
    (hUc : Convex ℝ U) (hUo : IsOpen U) (hUn : U.Nonempty)
    (hVc : Convex ℝ V) (hVo : IsOpen V) (hVn : V.Nonempty)
    (hWc : Convex ℝ W) (hWo : IsOpen W) (hWn : W.Nonempty)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    (closure U ∩ closure V ∩ closure W).Subsingleton := by
  intro a ha b hb
  by_contra hab
  obtain ⟨n, t, hn, hlU, hrV⟩ := convex_open_disjoint_strict_separator hUc hUo hUn hVc hVo hVn hUV
  obtain ⟨m, s, hm, hlU', hrW⟩ := convex_open_disjoint_strict_separator hUc hUo hUn hWc hWo hWn hUW
  obtain ⟨l, r, hl, hlV, hrW'⟩ := convex_open_disjoint_strict_separator hVc hVo hVn hWc hWo hWn hVW
  have hna := inner_eq_of_common_closures hlU hrV ha.1
  have hnb := inner_eq_of_common_closures hlU hrV hb.1
  have hma := inner_eq_of_common_closures hlU' hrW ⟨ha.1.1, ha.2⟩
  have hmb := inner_eq_of_common_closures hlU' hrW ⟨hb.1.1, hb.2⟩
  have hla := inner_eq_of_common_closures hlV hrW' ⟨ha.1.2, ha.2⟩
  have hlb := inner_eq_of_common_closures hlV hrW' ⟨hb.1.2, hb.2⟩
  obtain ⟨u, hu⟩ := hUn
  obtain ⟨v, hv⟩ := hVn
  obtain ⟨w, hw⟩ := hWn
  have hcross := complex_affine_difference_cross (x := w) (u := u) hn hm hab hna hnb hma hmb
  have hcross' := complex_affine_difference_cross (x := w) (u := v) hn hl hab hna hnb hla hlb
  have hFw : t < inner ℝ n w := by
    by_contra h
    have h1 := mul_neg_of_pos_of_neg (sub_pos.mpr (hrW w hw)) (sub_neg.mpr (hlU u hu))
    have h2 := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))
      (sub_nonpos.mpr (hlU' u hu).le)
    linarith
  have h1 := mul_pos (sub_pos.mpr (hrW' w hw)) (sub_pos.mpr (hrV v hv))
  have h2 := mul_neg_of_pos_of_neg (sub_pos.mpr hFw) (sub_neg.mpr (hlV v hv))
  linarith

end LowDimensionalTopology.Geometry.Euclidean
