module
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import LowDimensionalTopology.External.LeanPool.Schoenflies.JordanClosed
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Boundary accessibility in the plane

Simple arcs approaching an accessible boundary point are constructed from shrinking
arc chains. The auxiliary results control planar separation and locally finite tiles
using the Jordan and Schoenflies theorems.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Metric Topology Schoenflies
open scoped Topology

namespace LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- The shrinking simple-arc chain in the accessibility argument has a simple limiting arc, including its limiting endpoint. -/
theorem exists_arc_of_shrinking_arc_chain (f : ℕ → ℝ → Plane) (a : Plane)
    (hc : ∀ n, ContinuousOn (f n) (Icc 0 1))
    (hi : ∀ n, InjOn (f n) (Icc 0 1))
    (hjoin : ∀ n, f n 1 = f (n + 1) 0)
    (hball : ∀ n, f n '' Icc 0 1 ⊆ ball a ((1 / 2 : ℝ) ^ n))
    (havoid : ∀ n, a ∉ f n '' Icc 0 1)
    (hmeet : ∀ m n, m < n →
      (f m '' Icc 0 1) ∩ (f n '' Icc 0 1) ⊆ {f n 0})
    (hfar : ∀ m n, m + 1 < n → f n 0 ∉ f m '' Icc 0 1) :
    ∃ A : Set Plane, IsArcBetween A (f 0 0) a ∧ A \ {a} ⊆ ⋃ n, f n '' Icc 0 1 := by
  classical
  let G : ℝ → Plane := fun t => f ⌊t⌋₊ (t - (⌊t⌋₊ : ℝ))
  have harg : ∀ t : ℝ, 0 ≤ t → t - (⌊t⌋₊ : ℝ) ∈ Ico (0 : ℝ) 1 := by
    intro t ht
    refine ⟨sub_nonneg.mpr (Nat.floor_le ht), ?_⟩
    have hh := Nat.lt_floor_add_one t
    linarith
  have hGeq : ∀ (n : ℕ) (t : ℝ), t ∈ Icc (n : ℝ) ((n : ℝ) + 1) →
      G t = f n (t - (n : ℝ)) := by
    intro n t ht
    by_cases hlt : t < (n : ℝ) + 1
    · have hfl : ⌊t⌋₊ = n := (Nat.floor_eq_iff
        ((Nat.cast_nonneg n).trans ht.1)).mpr ⟨ht.1, hlt⟩
      simp only [G, hfl]
    · have hteq : t = (n : ℝ) + 1 := le_antisymm ht.2 (le_of_not_gt hlt)
      subst t
      have hfl : ⌊(n : ℝ) + 1⌋₊ = n + 1 := by
        rw [← Nat.cast_one, ← Nat.cast_add, Nat.floor_natCast]
      simp only [G, hfl, Nat.cast_add, Nat.cast_one, sub_self, add_sub_cancel_left]
      exact (hjoin n).symm
  have hLF : LocallyFinite (fun n : ℕ => Icc (n : ℝ) ((n : ℝ) + 1)) := by
    intro t
    refine ⟨Iio (t + 1), isOpen_Iio.mem_nhds (by change t < t + 1; linarith),
      (Set.finite_Iic ⌈t + 1⌉₊).subset ?_⟩
    rintro n ⟨s, hs, hslt⟩
    exact_mod_cast hs.1.trans (hslt.le.trans (Nat.le_ceil (t + 1)))
  have hGcont : ContinuousOn G (Ici (0 : ℝ)) := by
    have hloc : ∀ n : ℕ, ContinuousOn G (Icc (n : ℝ) ((n : ℝ) + 1)) := by
      intro n
      have hh : ContinuousOn (fun t : ℝ => f n (t - (n : ℝ)))
          (Icc (n : ℝ) ((n : ℝ) + 1)) :=
        (hc n).comp (continuous_id.sub continuous_const).continuousOn
          (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      exact hh.congr (fun t ht => hGeq n t ht)
    refine (hLF.continuousOn_iUnion (fun _ => isClosed_Icc) hloc).mono ?_
    intro t ht
    exact mem_iUnion.mpr ⟨⌊t⌋₊, Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  have hnoeq : ∀ m n, m < n → ∀ s ∈ Ico (0 : ℝ) 1,
      ∀ t ∈ Ico (0 : ℝ) 1, f m s ≠ f n t := by
    intro m n hmn s hs t ht heq
    have hshare : f m s = f n 0 := hmeet m n hmn
      ⟨⟨s, ⟨hs.1, hs.2.le⟩, rfl⟩, ⟨t, ⟨ht.1, ht.2.le⟩, heq.symm⟩⟩
    by_cases hgap : m + 1 < n
    · exact hfar m n hgap ⟨s, ⟨hs.1, hs.2.le⟩, hshare⟩
    · have hn : n = m + 1 := by omega
      subst n
      have he : f m s = f m 1 := hshare.trans (hjoin m).symm
      have hs1 : s = 1 := hi m ⟨hs.1, hs.2.le⟩ ⟨by norm_num, le_rfl⟩ he
      exact hs.2.ne hs1
  have hGinj : InjOn G (Ici (0 : ℝ)) := by
    intro s hs t ht heq
    rcases lt_trichotomy ⌊s⌋₊ ⌊t⌋₊ with hlt | he | hgt
    · exact (hnoeq _ _ hlt _ (harg s hs) _ (harg t ht) heq).elim
    · have hh : s - (⌊s⌋₊ : ℝ) = t - (⌊t⌋₊ : ℝ) := by
        apply hi ⌊s⌋₊ ⟨(harg s hs).1, (harg s hs).2.le⟩
          ⟨(harg t ht).1, (harg t ht).2.le⟩
        simpa only [G, he] using heq
      rw [he] at hh
      linarith
    · exact (hnoeq _ _ hgt _ (harg t ht) _ (harg s hs) heq.symm).elim
  have hGavoid : ∀ t : ℝ, 0 ≤ t → G t ≠ a := by
    intro t ht heq
    exact havoid ⌊t⌋₊ ⟨t - (⌊t⌋₊ : ℝ),
      ⟨(harg t ht).1, (harg t ht).2.le⟩, heq⟩
  have hGsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ s : ℝ,
      (N : ℝ) ≤ s → dist (G s) a < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨N, fun s hs => ?_⟩
    have hs0 : 0 ≤ s := (Nat.cast_nonneg N).trans hs
    have hNs : N ≤ ⌊s⌋₊ := Nat.le_floor hs
    have hbound : dist (G s) a < (1 / 2 : ℝ) ^ ⌊s⌋₊ :=
      hball ⌊s⌋₊ ⟨s - (⌊s⌋₊ : ℝ), ⟨(harg s hs0).1, (harg s hs0).2.le⟩, rfl⟩
    have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hNs
    exact (hbound.trans_le hpow).trans hN
  let q : ℝ → ℝ := fun t => t / (1 - t)
  let g : ℝ → Plane := fun t => if t < 1 then G (q t) else a
  have hq : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ q t := fun t ht =>
    div_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hg1 : g 1 = a := by simp [g]
  have hgcont : ContinuousOn g (Icc (0 : ℝ) 1) := by
    intro t ht
    by_cases ht1 : t = 1
    · subst t
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hGsmall ε hε
      have hNp : 0 < (N : ℝ) + 1 := by positivity
      refine ⟨1 / ((N : ℝ) + 1), by positivity, ?_⟩
      intro s hs hsd
      rw [hg1]
      by_cases hs1 : s = 1
      · simpa only [hs1, hg1, dist_self] using hε
      · have hsl : s < 1 := lt_of_le_of_ne hs.2 hs1
        have hd : 0 < 1 - s := sub_pos.mpr hsl
        have hsd' : 1 - s < 1 / ((N : ℝ) + 1) := by
          simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2), neg_sub] using hsd
        have hmul : (1 - s) * ((N : ℝ) + 1) < 1 := (lt_div_iff₀ hNp).mp hsd'
        have hNs : (N : ℝ) ≤ q s := (le_div_iff₀ hd).mpr (by nlinarith)
        simpa only [g, ite_eq_left hsl] using hN (q s) hNs
    · have htl : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hqc : ContinuousWithinAt q (Icc (0 : ℝ) 1) t :=
        (continuousAt_id.div (continuousAt_const.sub continuousAt_id)
          (sub_ne_zero.mpr (Ne.symm (ne_of_lt htl)))).continuousWithinAt
      have hcomp : ContinuousWithinAt (fun s => G (q s)) (Icc (0 : ℝ) 1) t :=
        (hGcont (q t) (hq t ht)).comp hqc (fun s hs => hq s hs)
      apply hcomp.congr_of_eventuallyEq_of_mem _ ht
      have he : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t, s < 1 :=
        mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds htl)
      filter_upwards [he] with s hs
      exact ite_eq_left hs
  have hginj : InjOn g (Icc (0 : ℝ) 1) := by
    intro s hs t ht heq
    by_cases hs1 : s = 1
    · subst s
      by_contra ht1
      have htl : t < 1 := lt_of_le_of_ne ht.2 (Ne.symm ht1)
      have hh : G (q t) = a := by simpa only [hg1, g, ite_eq_left htl] using heq.symm
      exact hGavoid (q t) (hq t ht) hh
    · by_cases ht1 : t = 1
      · subst t
        have hsl : s < 1 := lt_of_le_of_ne hs.2 hs1
        have hh : G (q s) = a := by simpa only [hg1, g, ite_eq_left hsl] using heq
        exact (hGavoid (q s) (hq s hs) hh).elim
      · have hsl : s < 1 := lt_of_le_of_ne hs.2 hs1
        have htl : t < 1 := lt_of_le_of_ne ht.2 ht1
        have hqq : q s = q t := hGinj (hq s hs) (hq t ht)
          (by simpa only [g, ite_eq_left hsl, ite_eq_left htl] using heq)
        have hh := (div_eq_div_iff (sub_pos.mpr hsl).ne' (sub_pos.mpr htl).ne').mp hqq
        nlinarith
  have hg0 : g 0 = f 0 0 := by norm_num [g, q, G]
  refine ⟨g '' Icc 0 1, ⟨g, hgcont, hginj, rfl, hg0, hg1⟩, ?_⟩
  rintro y ⟨⟨t, ht, rfl⟩, hya⟩
  have ht1 : t ≠ 1 := fun hh => hya (hh ▸ hg1)
  have htl : t < 1 := lt_of_le_of_ne ht.2 ht1
  refine mem_iUnion.mpr ⟨⌊q t⌋₊, q t - (⌊q t⌋₊ : ℝ),
    ⟨(harg (q t) (hq t ht)).1, (harg (q t) (hq t ht)).2.le⟩, ?_⟩
  simp only [g, ite_eq_left htl, G]

theorem access_radial_segment_avoids_segment {q v z x : Plane}
    (hv : q ≠ v) (hz : dist z q < dist v q)
    (hzn : z ∉ segment ℝ q v) (hx : x ∈ segment ℝ q z) (hxq : x ≠ q) :
    x ∉ segment ℝ q v := by
  intro hxv
  rw [segment_eq_image' ℝ q z] at hx
  rw [segment_eq_image' ℝ q v] at hxv
  obtain ⟨t, ht, htx⟩ := hx
  obtain ⟨s, hs, hsx⟩ := hxv
  have htpos : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro heq
    apply hxq
    simpa only [← heq, zero_smul, add_zero] using htx.symm
  have heq : t • (z - q) = s • (v - q) := add_left_cancel (htx.trans hsx.symm)
  have hzrep : z = q + (s / t) • (v - q) := by
    have h := congrArg (fun w : Plane => t⁻¹ • w) heq
    simp only [smul_smul, inv_mul_cancel₀ htpos.ne', one_smul] at h
    rw [← div_eq_inv_mul] at h
    calc
      z = q + (z - q) := by abel
      _ = q + (s / t) • (v - q) := by rw [h]
  have hc : 0 ≤ s / t := div_nonneg hs.1 htpos.le
  have hvnorm : 0 < ‖v - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv.symm)
  have hnorm : dist z q = (s / t) * dist v q := by
    rw [hzrep, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hc, dist_eq_norm]
  have hc1 : s / t ≤ 1 := by
    rw [hnorm] at hz
    have hdist : 0 < dist v q := dist_pos.mpr hv.symm
    nlinarith
  apply hzn
  rw [segment_eq_image' ℝ q v]
  exact ⟨s / t, ⟨hc, hc1⟩, hzrep.symm⟩

theorem access_segment_diff_left_preconnected {q z : Plane} (hne : q ≠ z) :
    IsPreconnected (segment ℝ q z \ {q}) := by
  have heq : segment ℝ q z \ {q} =
      (fun s : ℝ => q + s • (z - q)) '' Ioc 0 1 := by
    ext x
    constructor
    · rintro ⟨hx, hxq⟩
      rw [segment_eq_image' ℝ q z] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      refine ⟨s, ⟨?_, hs.2⟩, rfl⟩
      apply lt_of_le_of_ne hs.1
      intro heq
      apply hxq
      simp only [← heq, zero_smul, add_zero, mem_singleton_iff]
    · rintro ⟨s, hs, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [segment_eq_image' ℝ q z]
        exact ⟨s, ⟨hs.1.le, hs.2⟩, rfl⟩
      · intro heq
        have hsmul : s • (z - q) = 0 := by simpa using heq
        rcases smul_eq_zero.mp hsmul with hs0 | hzq
        · exact hs.1.ne' hs0
        · exact hne (sub_eq_zero.mp hzq).symm
  rw [heq]
  exact isPreconnected_Ioc.image _ (by fun_prop)

theorem continuous_access_small_time {γ : ℝ → Plane} {a : Plane}
    (hγ : ContinuousOn γ (Icc 0 1)) (hγ0 : γ 0 = a)
    {t ε : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hε : 0 < ε) :
    ∃ s ∈ Ioo 0 t, ∀ r ∈ Icc 0 s, γ r ∈ ball a ε := by
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousWithinAt_iff.mp
    (hγ 0 ⟨le_rfl, zero_le_one⟩) ε hε
  let s := min (t / 2) (δ / 2)
  have hs : 0 < s := lt_min (half_pos ht) (half_pos hδ)
  have hst : s < t := lt_of_le_of_lt (min_le_left _ _) (half_lt_self ht)
  refine ⟨s, ⟨hs, hst⟩, ?_⟩
  intro r hr
  rw [mem_ball, ← hγ0]
  apply hnear ⟨hr.1, hr.2.trans (hst.le.trans ht1)⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
  exact lt_of_le_of_lt (hr.2.trans (min_le_right _ _)) (half_lt_self hδ)

private structure AccessStage (Ω : Set Plane) (γ : ℝ → Plane) (a b : Plane) (n : ℕ) where
  time : ℝ
  trace : Set Plane
  time_mem : time ∈ Ioc 0 1
  arc : IsArcBetween trace b (γ time)
  polygonal : IsPolygonal trace
  subset : trace ⊆ Ω
  tail : ∀ s ∈ Ioo 0 time, γ s ∈ Ω \ trace
  shrinking : ∀ s ∈ Ioc 0 time, γ s ∈ ball a ((1 / 2 : ℝ) ^ n)

private theorem theta_outside_contradiction
    {A D : Fin 3 → Set Plane} {u v : Plane} {p : Fin 3 → Plane}
    (hA : ∀ i, IsArcBetween (A i) u v)
    (hmeet : ∀ i j, i ≠ j → A i ∩ A j ⊆ {u, v})
    (hD : ∀ i, IsJordanCurve (D i))
    (hcover : ∀ i, (⋃ j, A j) ⊆ A i ∪ D i)
    (hends : ∀ i, ({u, v} : Set Plane) ⊆ D i)
    (hp : ∀ i, p i ∈ A i) (hout : ∀ i, p i ∈ outside (D i)) : False := by
  classical
  let H : Set Plane := ⋃ i, A i
  have hHc : IsCompact H := isCompact_iUnion fun i => (hA i).isArc.isCompact
  have hsep : ∀ i, IsSeparating (D i) := fun i => jordan_curve_theorem (hD i)
  let K : Set Plane := H ∪ ⋃ i, (inside (D i) ∪ D i)
  have hKb : Bornology.IsBounded K :=
    hHc.isBounded.union (Bornology.isBounded_iUnion.mpr fun i =>
      (hsep i).isBounded_inside.union (hD i).isCompact.isBounded)
  have hnot : ¬ outside (D 0) ⊆ K := fun hh =>
    (hsep 0).not_isBounded_outside (hKb.subset hh)
  obtain ⟨z, _hz0, hzK⟩ := Set.not_subset.mp hnot
  have hzH : z ∉ H := fun hz => hzK (Or.inl hz)
  have hzout : ∀ i, z ∈ outside (D i) := by
    intro i
    have hzD : z ∉ D i := fun hz => hzK (Or.inr (mem_iUnion.mpr ⟨i, Or.inr hz⟩))
    have hzI : z ∉ inside (D i) := fun hz => hzK (Or.inr (mem_iUnion.mpr ⟨i, Or.inl hz⟩))
    have hh : z ∈ inside (D i) ∪ outside (D i) := by
      rw [inside_union_outside]
      exact hzD
    exact hh.resolve_left hzI
  let Ω : Set Plane := connectedComponentIn Hᶜ z
  have hΩopen : IsOpen Ω := Plane.isOpen_connectedComponentIn hHc.isClosed.isOpen_compl
  have hΩconn : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hΩH : Disjoint Ω H := Set.disjoint_left.mpr fun x hx =>
    connectedComponentIn_subset Hᶜ z hx
  have hacc : ∀ i, ∃ w ∈ A i, w ∉ ({u, v} : Set Plane) ∧ PolyAccessible Ω w := by
    intro i
    obtain ⟨vs, hvs, hvsub, hvhead, hvlast⟩ := exists_poly_of_isPreconnected
      (hsep i).isOpen_outside (hsep i).isConnected_outside.isPreconnected (hzout i) (hout i)
    have hlist : z :: vs.tail = vs := by
      rw [← hvhead]
      exact List.cons_head_tail hvs
    have hvsub' : poly (z :: vs.tail) ⊆ outside (D i) := hlist ▸ hvsub
    have hsub : poly (z :: vs.tail) ⊆ Hᶜ ∪ H := by
      intro x _
      exact (em (x ∈ H)).elim Or.inr Or.inl
    have hmeeting : (poly (z :: vs.tail) ∩ H).Nonempty := by
      refine ⟨p i, ?_, mem_iUnion.mpr ⟨i, hp i⟩⟩
      rw [hlist]
      exact hvlast ▸ getLast_mem_poly hvs
    obtain ⟨w, hw, hwacc⟩ := polyAccessible_first_meeting
      hHc.isClosed disjoint_compl_left hzH hsub hmeeting
    have hwD : w ∉ D i := (hvsub' hw.1).1
    have hwA : w ∈ A i := (hcover i hw.2).resolve_right hwD
    exact ⟨w, hwA, fun he => hwD (hends i he), hwacc⟩
  choose w hwA hwends hwacc using hacc
  have hwinj : Function.Injective w := by
    intro i j hij
    by_contra hne
    exact hwends i (hmeet i j hne ⟨hwA i, hij ▸ hwA j⟩)
  have hwH : ∀ i, w i ∈ H := fun i => mem_iUnion.mpr ⟨i, hwA i⟩
  obtain ⟨x, hxΩ, T0, T1, T2, hT0, hT1, hT2, hT0Ω, hT1Ω, hT2Ω,
      hT01, hT02, hT12⟩ := exists_tripod hΩopen hΩconn hΩH
    (hwH 0) (hwH 1) (hwH 2)
    (fun hh => by have := hwinj hh; norm_num at this)
    (fun hh => by have := hwinj hh; norm_num at this)
    (fun hh => by have := hwinj hh; norm_num at this)
    (hwacc 0) (hwacc 1) (hwacc 2)
  let T : Fin 3 → Set Plane := ![T0, T1, T2]
  have hT : ∀ i, IsArcBetween (T i) x (w i) := by
    intro i
    fin_cases i
    · exact hT0
    · exact hT1
    · exact hT2
  have hTΩ : ∀ i, T i \ {w i} ⊆ Ω := by
    intro i
    fin_cases i
    · exact hT0Ω
    · exact hT1Ω
    · exact hT2Ω
  have hTT : ∀ i j, i ≠ j → T i ∩ T j ⊆ {x} := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hT01
    · exact hT02
    · exact fun y hy => hT01 ⟨hy.2, hy.1⟩
    · exact (hij rfl).elim
    · exact hT12
    · exact fun y hy => hT02 ⟨hy.2, hy.1⟩
    · exact fun y hy => hT12 ⟨hy.2, hy.1⟩
    · exact (hij rfl).elim
  have hsplit : ∀ i, ∃ L R, IsArcBetween L u (w i) ∧ IsArcBetween R (w i) v ∧
      L ∪ R = A i ∧ L ∩ R = {w i} := fun i =>
    (hA i).exists_split (hwA i) (fun hh => hwends i (Or.inl hh))
      (fun hh => hwends i (Or.inr hh))
  choose L R hL hR hLR hLRmeet using hsplit
  let X : Fin 3 → Plane := ![u, v, x]
  let P : Fin 3 → Fin 3 → Set Plane := ![L, R, T]
  have hparc : ∀ i j, IsArcBetween (P i j) (X i) (w j) := by
    intro i j
    fin_cases i
    · exact hL j
    · exact (hR j).reverse
    · exact hT j
  have huH : u ∈ H := mem_iUnion.mpr ⟨0, (hA 0).left_mem⟩
  have hvH : v ∈ H := mem_iUnion.mpr ⟨0, (hA 0).right_mem⟩
  have hxH : x ∉ H := Set.disjoint_left.mp hΩH hxΩ
  have huv : u ≠ v := by
    obtain ⟨f, _hfc, hfi, _hfim, hf0, hf1⟩ := hA 0
    intro hh
    have : (0 : ℝ) = 1 := hfi (by constructor <;> norm_num) (by constructor <;> norm_num)
      (by rw [hf0, hf1, hh])
    norm_num at this
  have hXinj : Function.Injective X := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (huv hij).elim
    · change u = x at hij
      exact (hxH (hij ▸ huH)).elim
    · exact (huv hij.symm).elim
    · rfl
    · change v = x at hij
      exact (hxH (hij ▸ hvH)).elim
    · change x = u at hij
      exact (hxH (hij.symm ▸ huH)).elim
    · change x = v at hij
      exact (hxH (hij.symm ▸ hvH)).elim
    · rfl
  have hXw : ∀ i j, X i ≠ w j := by
    intro i j
    fin_cases i
    · exact fun hh => hwends j (Or.inl hh.symm)
    · exact fun hh => hwends j (Or.inr hh.symm)
    · change x ≠ w j
      exact fun hh => hxH (hh.symm ▸ hwH j)
  have hAT : ∀ j l, A j ∩ T l ⊆ {w j} := by
    intro j l y hy
    have hyH : y ∈ H := mem_iUnion.mpr ⟨j, hy.1⟩
    have hyw : y = w l := by
      by_contra hne
      exact Set.disjoint_left.mp hΩH (hTΩ l ⟨hy.2, hne⟩) hyH
    by_cases hjl : j = l
    · simpa only [hjl, mem_singleton_iff] using hyw
    · exfalso
      exact hwends l (hmeet l j (Ne.symm hjl) ⟨hwA l, hyw ▸ hy.1⟩)
  exact (Graph.isArcK33_of_pieces (x := X) (y := w) (P := P) (Ch := A) (Sg := T)
    hparc hXinj hwinj hXw
    (fun j => (hLR j) ▸ subset_union_left)
    (fun j => (hLR j) ▸ subset_union_right)
    (fun _ => subset_rfl)
    (fun j => (hLRmeet j).subset) hmeet hAT hTT).elim

private theorem access_arc_prefix_to_closed_target
    {Ω A K : Set Plane} {a p : Plane}
    (hK : IsClosed K) (haK : a ∉ K) (hAK : (A ∩ K).Nonempty)
    (hA : IsArcBetween A a p) (hAΩ : A \ {a} ⊆ Ω) :
    ∃ q ∈ K ∩ Ω, ∃ Q : Set Plane, IsArcBetween Q a q ∧
      Q \ {a} ⊆ Ω ∧ Q ∩ K ⊆ {q} := by
  obtain ⟨f, hfc, hfi, hfim, hf0, _hf1⟩ := hA
  obtain ⟨z, hzA, hzK⟩ := hAK
  have hzimg : z ∈ f '' Icc 0 1 := hfim.symm ▸ hzA
  obtain ⟨t0, ht0, rfl⟩ := hzimg
  obtain ⟨s, hs, _hsts, hsK, hbefore⟩ := exists_first_mem_Icc hfc hK ht0 hzK
  have hsne : s ≠ 0 := by
    intro he
    exact haK (by simpa only [he, hf0] using hsK)
  have hQarc : IsArcBetween (f '' Icc 0 s) a (f s) := by
    have hh := isArcBetween_subarc_of_injOn_I hfc hfi
      (by constructor <;> norm_num) hs (Ne.symm hsne)
    rwa [uIcc_of_le hs.1, hf0] at hh
  have hsub : f '' Icc 0 s ⊆ A := by
    rw [← hfim]
    exact image_mono (Icc_subset_Icc le_rfl hs.2)
  have hqa : f s ≠ a := fun hh => haK (hh ▸ hsK)
  have hqΩ : f s ∈ Ω := hAΩ ⟨hsub hQarc.right_mem, hqa⟩
  refine ⟨f s, ⟨hsK, hqΩ⟩, f '' Icc 0 s, hQarc,
    fun z hz => hAΩ ⟨hsub hz.1, hz.2⟩, ?_⟩
  rintro z ⟨⟨t, ht, rfl⟩, htK⟩
  have hts : t = s := le_antisymm ht.2 (le_of_not_gt fun hlt =>
    hbefore t ⟨ht.1, ht.2.trans hs.2⟩ hlt htK)
  exact congrArg f hts

/-- The countable exceptional-set argument used for the noncompact tiles. -/
theorem locallyFinite_closure_of_countable_exceptional
    {X ι : Type*} [MetricSpace X] [ProperSpace X] (U : ι → Set X)
    (hconn : ∀ i, IsConnected (U i))
    (hncompact : ∀ i, ¬ IsCompact (closure (U i)))
    (hcount : {x : X | ¬ ∃ N ∈ 𝓝 x,
      {i | (closure (U i) ∩ N).Nonempty}.Finite}.Countable) :
    LocallyFinite (fun i => closure (U i)) := by
  classical
  intro x
  let E : Set X := {y : X | ¬ ∃ N ∈ 𝓝 y,
    {i | (closure (U i) ∩ N).Nonempty}.Finite}
  have hE : E.Countable := hcount
  obtain ⟨r, hravoid, hr⟩ := ((hE.image (fun y => dist y x)).dense_compl ℝ).exists_mem_open
    (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) 1)) ⟨1 / 2, by norm_num⟩
  have hregular : ∀ y ∈ sphere x r, ∃ N ∈ 𝓝 y,
      {i | (closure (U i) ∩ N).Nonempty}.Finite := by
    intro y hy
    have hyE : y ∉ E := fun hh => hravoid ⟨y, hh, mem_sphere.mp hy⟩
    exact Classical.not_not.mp hyE
  choose N hN hNfin using hregular
  obtain ⟨t, ht⟩ := (isCompact_sphere x r).elim_nhds_subcover' N hN
  have hsphere : {i | (closure (U i) ∩ sphere x r).Nonempty}.Finite := by
    refine (t.finite_toSet.biUnion (fun y _ => hNfin y.val y.prop)).subset ?_
    rintro i ⟨y, hyU, hysphere⟩
    obtain ⟨z, hzt, hyN⟩ := mem_iUnion₂.mp (ht hysphere)
    exact mem_biUnion hzt ⟨y, hyU, hyN⟩
  refine ⟨ball x r, ball_mem_nhds x hr.1, hsphere.subset ?_⟩
  rintro i ⟨y, hyU, hyball⟩
  have hnot : ¬ closure (U i) ⊆ closedBall x r := fun hh =>
    hncompact i ((isCompact_closedBall x r).of_isClosed_subset isClosed_closure hh)
  obtain ⟨z, hzU, hzball⟩ := Set.not_subset.mp hnot
  have hylt : dist y x < r := mem_ball.mp hyball
  have hzgt : r < dist z x := lt_of_not_ge (fun hh => hzball (mem_closedBall.mpr hh))
  obtain ⟨w, hwU, hwdist⟩ := (hconn i).closure.isPreconnected.intermediate_value hyU hzU
    (continuous_id.dist continuous_const).continuousOn ⟨hylt.le, hzgt.le⟩
  exact ⟨w, hwU, mem_sphere.mpr hwdist⟩

theorem jordan_inside_regular_for_noncompact_tiles {ι : Type*} (U : ι → Set Plane)
    (hconn : ∀ i, IsConnected (U i))
    (hncompact : ∀ i, ¬ IsCompact (closure (U i)))
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (closure (U j)))
    (i j : ι) {C : Set Plane} (hC : IsJordanCurve C)
    (hCsub : C ⊆ closure (U i) ∪ closure (U j)) :
    ∀ x ∈ inside C, ∃ N ∈ 𝓝 x,
      {k | (closure (U k) ∩ N).Nonempty}.Finite := by
  classical
  have hsep := jordan_curve_theorem hC
  have hother : ∀ k, k ≠ i → k ≠ j → Disjoint (closure (U k)) (inside C) := by
    intro k hki hkj
    have hUkC : Disjoint (U k) C := by
      apply Set.disjoint_left.mpr
      intro y hy hyC
      rcases hCsub hyC with hyi | hyj
      · exact Set.disjoint_left.mp (hdisj k i hki) hy hyi
      · exact Set.disjoint_left.mp (hdisj k j hkj) hy hyj
    have hUkI : Disjoint (U k) (inside C) := by
      apply Set.disjoint_left.mpr
      intro y hy hyI
      have hcover : U k ⊆ inside C ∪ outside C := by
        rw [inside_union_outside]
        exact fun z hz => Set.disjoint_left.mp hUkC hz
      have hsub : U k ⊆ inside C :=
        (hconn k).isPreconnected.subset_left_of_subset_union
          hsep.isOpen_inside hsep.isOpen_outside disjoint_inside_outside
          hcover ⟨y, hy, hyI⟩
      apply hncompact k
      exact isCompact_iff_isClosed_bounded.mpr
        ⟨isClosed_closure, (hsep.isBounded_inside.subset hsub).closure⟩
    exact hUkI.closure_left hsep.isOpen_inside
  intro x hx
  refine ⟨inside C, hsep.isOpen_inside.mem_nhds hx, ((Set.finite_singleton j).insert i).subset ?_⟩
  intro k hk
  by_contra hnot
  have hki : k ≠ i := fun heq => hnot (Or.inl heq)
  have hkj : k ≠ j := fun heq => hnot (Or.inr heq)
  obtain ⟨y, hyK, hyI⟩ := hk
  exact Set.disjoint_left.mp (hother k hki hkj) hyK hyI

private theorem access_branches_cross_intersection
    {U V A B : Set Plane} {a b : Plane}
    (hUV : Disjoint U V) (haV : a ∉ V) (hbU : b ∉ U)
    (hA : A \ {a} ⊆ U) (hB : B \ {b} ⊆ V) :
    A ∩ B ⊆ ({a} : Set Plane) ∩ {b} := by
  rintro z ⟨hzA, hzB⟩
  have hza : z = a := by
    by_contra hne
    have hzU := hA ⟨hzA, hne⟩
    by_cases hzb : z = b
    · exact hbU (hzb ▸ hzU)
    · exact Set.disjoint_left.mp hUV hzU (hB ⟨hzB, hzb⟩)
  have hzb : z = b := by
    by_contra hne
    exact haV (hza ▸ hB ⟨hzB, hne⟩)
  exact ⟨hza, hzb⟩

private theorem access_branch_subset_closure {U A : Set Plane} {a : Plane}
    (hA : A \ {a} ⊆ U) (ha : a ∈ closure U) : A ⊆ closure U := by
  intro z hz
  rcases eq_or_ne z a with rfl | hne
  · exact ha
  · exact subset_closure (hA ⟨hz, hne⟩)

theorem polygonalArc_endpoint_small_radials {K : Set Plane} {b q : Plane}
    (hK : IsArcBetween K b q) (hpoly : IsPolygonal K) :
    ∃ ε > 0, ∀ z ∈ ball q ε \ K,
      segment ℝ q z \ {q} ⊆ ball q ε \ K := by
  classical
  obtain ⟨n, A, hcar, hfirst, hlast⟩ :=
    isPolyArcCarrier_of_isPolygonal hK hpoly
  let F : Set Plane := ⋃ j ∈ ({j : ℕ | j < n} : Set ℕ), A.edge j
  have hFc : IsClosed F := by
    exact (Set.finite_lt_nat n).isClosed_biUnion fun j hj => A.isCompact_edge.isClosed
  have hqF : q ∉ F := by
    intro hq
    obtain ⟨j, hj⟩ := mem_iUnion.mp hq
    obtain ⟨hj, hqj⟩ := mem_iUnion.mp hj
    have hjlt : j < n := hj
    exact A.vertex_notMem_edge (i := n + 1) (j := j) (by omega) (by omega)
      (by omega) (by omega) (hlast.symm ▸ hqj)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hFc.isOpen_compl q hqF
  have hqv : q ≠ A.vertex n := by
    rw [← hlast]
    exact fun heq => Nat.succ_ne_self n (A.vertex_inj heq)
  let ε := min δ (dist (A.vertex n) q)
  have hε : 0 < ε := lt_min hδ (dist_pos.mpr hqv.symm)
  refine ⟨ε, hε, ?_⟩
  intro z hz x hx
  have hxball : x ∈ ball q ε :=
    (convex_ball q ε).segment_subset (mem_ball_self hε) hz.1 hx.1
  refine ⟨hxball, ?_⟩
  intro hxK
  have hxF : x ∉ F := hδsub (ball_subset_ball (min_le_left _ _) hxball)
  have hxedge : x ∈ A.edge n := by
    rw [← hcar, A.mem_carrier_iff] at hxK
    obtain ⟨j, hj, hxj⟩ := hxK
    by_cases hjn : j < n
    · exact False.elim (hxF (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjn, hxj⟩⟩))
    · obtain rfl : j = n := by omega
      exact hxj
  have hzn : z ∉ segment ℝ q (A.vertex n) := by
    intro hzseg
    apply hz.2
    rw [← hcar]
    apply A.edge_subset_carrier (i := n) le_rfl
    simpa only [PolyArc.edge, hlast, segment_symm] using hzseg
  apply access_radial_segment_avoids_segment hqv
    (lt_of_lt_of_le hz.1 (min_le_right _ _)) hzn hx.1 hx.2
  simpa only [PolyArc.edge, hlast, segment_symm] using hxedge

private theorem continuous_access_initial_stage {Ω : Set Plane} {γ : ℝ → Plane} {a : Plane}
    (hΩ : IsOpen Ω) (ha : a ∉ Ω) (hγ : ContinuousOn γ (Icc 0 1))
    (hγ0 : γ 0 = a) (hinto : ∀ t ∈ Ioc 0 1, γ t ∈ Ω) :
    ∃ b : Plane, Nonempty (AccessStage Ω γ a b 0) := by
  classical
  obtain ⟨v, hv, hvsmall⟩ := continuous_access_small_time hγ hγ0 zero_lt_one le_rfl zero_lt_one
  let c := γ v
  let U := Ω ∩ ball a 1
  have hU : IsOpen U := hΩ.inter isOpen_ball
  have hcU : c ∈ U := ⟨hinto v ⟨hv.1, hv.2.le⟩,
    hvsmall v ⟨hv.1.le, le_rfl⟩⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU c hcU
  have hball : ∀ᶠ z in 𝓝[≠] c, z ∈ ball c ε :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c hε)
  have hne : ∀ᶠ z in 𝓝[≠] c, z ≠ c := self_mem_nhdsWithin
  obtain ⟨d, hd, hdc⟩ := (hball.and hne).exists
  let K := segment ℝ c d
  have hKU : K ⊆ U :=
    ((convex_ball c ε).segment_subset (mem_ball_self hε) hd).trans hεU
  have haK : γ 0 ∉ K := fun hx => ha (hγ0 ▸ (hKU hx).1)
  obtain ⟨t, ht, htv, htK, hbefore⟩ := exists_first_mem_Icc
    (hγ.mono (Icc_subset_Icc le_rfl hv.2.le)) (isCompact_segment c d).isClosed
    (right_mem_Icc.mpr hv.1.le) (left_mem_segment ℝ c d)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro heq
    exact haK (heq ▸ htK))
  have ht1 : t ≤ 1 := htv.trans hv.2.le
  have hex : ∃ b ∈ K, b ≠ γ t := by
    by_cases hct : c = γ t
    · exact ⟨d, right_mem_segment ℝ c d, by simpa only [← hct] using hdc⟩
    · exact ⟨c, left_mem_segment ℝ c d, hct⟩
  obtain ⟨b, hbK, hbt⟩ := hex
  let L := segment ℝ b (γ t)
  have hLK : L ⊆ K := (convex_segment c d).segment_subset hbK htK
  refine ⟨b, ⟨⟨t, L, ⟨htpos, ht1⟩, isArcBetween_segment hbt,
    isPolygonal_segment b (γ t), hLK.trans (hKU.trans inter_subset_left), ?_, ?_⟩⟩⟩
  · intro s hs
    refine ⟨hinto s ⟨hs.1, hs.2.le.trans ht1⟩, ?_⟩
    exact fun hx => hbefore s ⟨hs.1.le, hs.2.le.trans htv⟩ hs.2 (hLK hx)
  · intro s hs
    simpa only [pow_zero] using hvsmall s ⟨hs.1.le, hs.2.trans htv⟩

private structure AccessStep {Ω : Set Plane} {γ : ℝ → Plane} {a b : Plane} {n : ℕ}
    (S : AccessStage Ω γ a b n) where
  next : AccessStage Ω γ a b (n + 1)
  piece : ℝ → Plane
  continuousOn : ContinuousOn piece (Icc 0 1)
  injOn : InjOn piece (Icc 0 1)
  zero : piece 0 = γ S.time
  one : piece 1 = γ next.time
  subset : piece '' Icc 0 1 ⊆ Ω ∩ ball a ((1 / 2 : ℝ) ^ n)
  old_inter : (piece '' Icc 0 1) ∩ S.trace ⊆ {γ S.time}
  next_prefix : next.trace = S.trace ∪ piece '' Icc 0 1
  newend_not_old : γ next.time ∉ S.trace

/-- The theta-curve separation needed by, for arbitrary simple arcs. -/
theorem theta_middle_point_mem_inside
    {A B C : Set Plane} {u v a b c : Plane}
    (hA : IsArcBetween A u v) (hB : IsArcBetween B u v) (hC : IsArcBetween C u v)
    (hAB : A ∩ B ⊆ {u, v}) (hAC : A ∩ C ⊆ {u, v}) (hBC : B ∩ C ⊆ {u, v})
    (ha : a ∈ A \ {u, v}) (hb : b ∈ B \ {u, v}) (hc : c ∈ C \ {u, v}) :
    a ∈ inside (B ∪ C) ∨ b ∈ inside (A ∪ C) ∨ c ∈ inside (A ∪ B) := by
  classical
  by_contra hn
  push Not at hn
  let S : Fin 3 → Set Plane := ![A, B, C]
  let D : Fin 3 → Set Plane := ![B ∪ C, A ∪ C, A ∪ B]
  let p : Fin 3 → Plane := ![a, b, c]
  have hS : ∀ i, IsArcBetween (S i) u v := by intro i; fin_cases i <;> assumption
  have hSS : ∀ i j, i ≠ j → S i ∩ S j ⊆ {u, v} := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hAB
    · exact hAC
    · exact fun y hy => hAB ⟨hy.2, hy.1⟩
    · exact (hij rfl).elim
    · exact hBC
    · exact fun y hy => hAC ⟨hy.2, hy.1⟩
    · exact fun y hy => hBC ⟨hy.2, hy.1⟩
    · exact (hij rfl).elim
  have hD : ∀ i, IsJordanCurve (D i) := by
    intro i
    fin_cases i
    · exact isJordanCurve_union hB hC fun y hy hz => hBC ⟨hy, hz⟩
    · exact isJordanCurve_union hA hC fun y hy hz => hAC ⟨hy, hz⟩
    · exact isJordanCurve_union hA hB fun y hy hz => hAB ⟨hy, hz⟩
  have hcover : ∀ i, (⋃ j, S j) ⊆ S i ∪ D i := by
    intro i y hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    fin_cases i <;> fin_cases j <;> simp_all [S, D]
  have hends : ∀ i, ({u, v} : Set Plane) ⊆ D i := by
    intro i y hy
    rcases hy with rfl | rfl <;> fin_cases i
    · exact Or.inl hB.left_mem
    · exact Or.inl hA.left_mem
    · exact Or.inl hA.left_mem
    · exact Or.inl hB.right_mem
    · exact Or.inl hA.right_mem
    · exact Or.inl hA.right_mem
  have hp : ∀ i, p i ∈ S i := by
    intro i
    fin_cases i
    · exact ha.1
    · exact hb.1
    · exact hc.1
  have hpD : ∀ i, p i ∉ D i := by
    intro i
    fin_cases i
    · rintro (hh | hh)
      · exact ha.2 (hAB ⟨ha.1, hh⟩)
      · exact ha.2 (hAC ⟨ha.1, hh⟩)
    · rintro (hh | hh)
      · exact hb.2 (hAB ⟨hh, hb.1⟩)
      · exact hb.2 (hBC ⟨hb.1, hh⟩)
    · rintro (hh | hh)
      · exact hc.2 (hAC ⟨hh, hc.1⟩)
      · exact hc.2 (hBC ⟨hh, hc.1⟩)
  have hpI : ∀ i, p i ∉ inside (D i) := by
    intro i
    fin_cases i
    · exact hn.1
    · exact hn.2.1
    · exact hn.2.2
  apply theta_outside_contradiction hS hSS hD hcover hends hp
  intro i
  have hh : p i ∈ inside (D i) ∪ outside (D i) := by
    rw [inside_union_outside]
    exact hpD i
  exact hh.resolve_left (hpI i)

private theorem arc_from_access_to_closed_target
    {Ω A K : Set Plane} {a p : Plane}
    (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω) (haΩ : a ∉ Ω)
    (hK : IsClosed K) (hKΩ : (K ∩ Ω).Nonempty) (haK : a ∉ K)
    (hpΩ : p ∈ Ω) (hA : IsArcBetween A a p) (hAΩ : A \ {a} ⊆ Ω) :
    ∃ q ∈ K ∩ Ω, ∃ Q : Set Plane, IsArcBetween Q a q ∧
      Q \ {a} ⊆ Ω ∧ Q ∩ K ⊆ {q} := by
  classical
  by_cases hAK : (A ∩ K).Nonempty
  · exact access_arc_prefix_to_closed_target hK haK hAK hA hAΩ
  · obtain ⟨k, hkK, hkΩ⟩ := hKΩ
    have hpK : p ∉ K := fun hh => hAK ⟨p, hA.right_mem, hh⟩
    have hpk : p ≠ k := fun hh => hpK (hh.symm ▸ hkK)
    obtain ⟨C, hCΩ, _hCpoly, hC⟩ := exists_simple_arc_of_isPreconnected
      hΩopen hΩconn hpΩ hkΩ hpk
    obtain ⟨q, hq, D, hD, hDoff, hDK⟩ := access_arc_prefix_to_closed_target
      hK hpK ⟨k, hC.right_mem, hkK⟩ hC (fun z hz => hCΩ hz.1)
    have hDΩ : D ⊆ Ω := by
      intro z hz
      rcases eq_or_ne z p with rfl | hne
      · exact hpΩ
      · exact hDoff ⟨hz, hne⟩
    obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hD
    have hg0A : g 0 ∈ A := hg0.symm ▸ hA.right_mem
    obtain ⟨t, ht, _ht0, htA, hafter⟩ := exists_last_mem_Icc hgc hA.isArc.isClosed
      (by constructor <;> norm_num) hg0A
    have htne : t ≠ 1 := by
      intro he
      have hqA : q ∈ A := by simpa only [he, hg1] using htA
      exact hAK ⟨q, hqA, hq.1⟩
    have htlt : t < 1 := lt_of_le_of_ne ht.2 htne
    have hgtD : g t ∈ D := hgim ▸ ⟨t, ht, rfl⟩
    have hgta : g t ≠ a := fun hh => haΩ (hh ▸ hDΩ hgtD)
    obtain ⟨P, hPA, hP⟩ := hA.isArc.exists_isArcBetween_subset hA.left_mem htA (Ne.symm hgta)
    let T : Set Plane := g '' Icc t 1
    have hT : IsArcBetween T (g t) q := by
      have hh := isArcBetween_subarc_of_injOn_I hgc hgi ht
        (by constructor <;> norm_num) (ne_of_lt htlt)
      rwa [uIcc_of_le ht.2, hg1] at hh
    have hTD : T ⊆ D := by
      rw [← hgim]
      exact image_mono (Icc_subset_Icc ht.1 le_rfl)
    have hAT : ∀ z ∈ A, z ∈ T → z = g t := by
      rintro z hzA ⟨s, hs, rfl⟩
      have hst : s = t := le_antisymm (le_of_not_gt fun hlt =>
        hafter s ⟨ht.1.trans hs.1, hs.2⟩ hlt hzA) hs.1
      exact congrArg g hst
    have hPT : IsArcBetween (P ∪ T) a q :=
      hP.concatenate hT (fun z hzP hzT => hAT z (hPA hzP) hzT)
    refine ⟨q, hq, P ∪ T, hPT, ?_, ?_⟩
    · rintro z ⟨hzP | hzT, hza⟩
      · exact hAΩ ⟨hPA hzP, hza⟩
      · exact hDΩ (hTD hzT)
    · rintro z ⟨hzP | hzT, hzK⟩
      · exact (hAK ⟨z, hPA hzP, hzK⟩).elim
      · exact hDK ⟨hTD hzT, hzK⟩

theorem continuous_access_polygonal_endpoint_component {U K : Set Plane}
    {γ : ℝ → Plane} {b q : Plane} {t : ℝ}
    (hU : IsOpen U) (hK : IsArcBetween K b q) (hpoly : IsPolygonal K)
    (hq : q ∈ U) (hγ : ContinuousOn γ (Icc 0 1))
    (ht : t ∈ Ioc 0 1) (hγt : γ t = q)
    (htail : ∀ s ∈ Ioo 0 t, γ s ∈ U \ K) :
    PolyAccessible (connectedComponentIn (U \ K) (γ (t / 2))) q := by
  obtain ⟨ε, hε, hrad⟩ := polygonalArc_endpoint_small_radials hK hpoly
  obtain ⟨η, hη, hηU⟩ := Metric.isOpen_iff.mp hU q hq
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousWithinAt_iff.mp
    (hγ t ⟨ht.1.le, ht.2⟩) (min ε η) (lt_min hε hη)
  let d := min (t / 2) (δ / 2)
  have hd : 0 < d := lt_min (half_pos ht.1) (half_pos hδ)
  let s := t - d
  have hs : s ∈ Ioo 0 t := by
    dsimp only [s]
    constructor
    · have hdt : d ≤ t / 2 := min_le_left _ _
      linarith
    · linarith
  have hsI : s ∈ Icc 0 1 := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hstδ : dist s t < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2.le)]
    have hdδ : d ≤ δ / 2 := min_le_right _ _
    dsimp only [s]
    linarith
  have hzsmall : γ s ∈ ball q (min ε η) := by
    rw [mem_ball, ← hγt]
    exact hnear hsI hstδ
  have hzK : γ s ∉ K := (htail s hs).2
  have hqz : q ≠ γ s := fun heq => hzK (heq ▸ hK.right_mem)
  let T : Set Plane := γ '' Ioo 0 t
  let S : Set Plane := segment ℝ q (γ s) \ {q}
  have hTU : T ⊆ U \ K := by
    rintro _ ⟨r, hr, rfl⟩
    exact htail r hr
  have hSU : S ⊆ U \ K := by
    intro x hx
    have hxε := hrad (γ s)
      ⟨ball_subset_ball (min_le_left _ _) hzsmall, hzK⟩ hx
    refine ⟨hηU ?_, hxε.2⟩
    exact (convex_ball q η).segment_subset (mem_ball_self hη)
      (ball_subset_ball (min_le_right _ _) hzsmall) hx.1
  have hzS : γ s ∈ S := ⟨right_mem_segment ℝ _ _, hqz.symm⟩
  have hzT : γ s ∈ T := ⟨s, hs, rfl⟩
  have hTconn : IsPreconnected T :=
    isPreconnected_Ioo.image _ (hγ.mono (by
      intro r hr
      exact ⟨hr.1.le, hr.2.le.trans ht.2⟩))
  have hSTconn : IsPreconnected (S ∪ T) :=
    IsPreconnected.union' ⟨γ s, hzS, hzT⟩
      (access_segment_diff_left_preconnected hqz) hTconn
  have hmid : γ (t / 2) ∈ S ∪ T := by
    right
    exact ⟨t / 2, ⟨half_pos ht.1, half_lt_self ht.1⟩, rfl⟩
  have hsub := hSTconn.subset_connectedComponentIn hmid (union_subset hSU hTU)
  apply PolyAccessible.of_openSegment (hsub (Or.inl hzS))
  intro x hx
  apply hsub (Or.inl ?_)
  exact ⟨openSegment_subset_segment ℝ q (γ s) hx,
    fun heq => hqz ((left_mem_openSegment_iff.mp (heq ▸ hx)))⟩

/--
The general-access tripod needed for. The access arcs may be arbitrary
simple topological arcs, and need not be polygonal.
-/
theorem exists_tripod_of_access_arcs
    {Ω : Set Plane} {a b c : Plane}
    (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (haΩ : a ∉ Ω) (hbΩ : b ∉ Ω) (hcΩ : c ∉ Ω)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ∃ p ∈ Ω, ∃ A : Set Plane, IsArcBetween A a p ∧ A \ {a} ⊆ Ω)
    (hb : ∃ p ∈ Ω, ∃ A : Set Plane, IsArcBetween A b p ∧ A \ {b} ⊆ Ω)
    (hc : ∃ p ∈ Ω, ∃ A : Set Plane, IsArcBetween A c p ∧ A \ {c} ⊆ Ω) :
    ∃ x ∈ Ω, ∃ Ta Tb Tc : Set Plane,
      IsArcBetween Ta x a ∧ IsArcBetween Tb x b ∧ IsArcBetween Tc x c ∧
        Ta \ {a} ⊆ Ω ∧ Tb \ {b} ⊆ Ω ∧ Tc \ {c} ⊆ Ω ∧
        Ta ∩ Tb ⊆ {x} ∧ Ta ∩ Tc ⊆ {x} ∧ Tb ∩ Tc ⊆ {x} := by
  obtain ⟨pa, hpaΩ, A, hA, hAΩ⟩ := ha
  obtain ⟨pb, hpbΩ, B, hB, hBΩ⟩ := hb
  obtain ⟨pc, hpcΩ, C, hC, hCΩ⟩ := hc
  have haB : a ∉ B := by
    intro haB
    exact haΩ (hBΩ ⟨haB, hab⟩)
  obtain ⟨q, hq, Q, hQ, hQΩ, hQB⟩ := arc_from_access_to_closed_target
    hΩopen hΩconn haΩ hB.isArc.isClosed ⟨pb, hB.right_mem, hpbΩ⟩ haB hpaΩ hA hAΩ
  have hbq : b ≠ q := fun hh => hbΩ (hh.symm ▸ hq.2)
  obtain ⟨B0, hB0B, hB0⟩ := hB.isArc.exists_isArcBetween_subset hB.left_mem hq.1 hbq
  let J : Set Plane := Q ∪ B0
  have hJ : IsArcBetween J a b :=
    hQ.concatenate hB0.reverse (fun z hzQ hzB0 => hQB ⟨hzQ, hB0B hzB0⟩)
  have hJΩ : J \ {a, b} ⊆ Ω := by
    rintro z ⟨hzQ | hzB0, hzab⟩
    · exact hQΩ ⟨hzQ, fun hh => hzab (Or.inl hh)⟩
    · exact hBΩ ⟨hB0B hzB0, fun hh => hzab (Or.inr hh)⟩
  have hcJ : c ∉ J := by
    intro hh
    exact hcΩ (hJΩ ⟨hh, fun h => h.elim (fun he => hac he.symm) (fun he => hbc he.symm)⟩)
  have hqJ : q ∈ J := Or.inl hQ.right_mem
  obtain ⟨x, hx, R, hR, hRΩ, hRJ⟩ := arc_from_access_to_closed_target
    hΩopen hΩconn hcΩ hJ.isArc.isClosed ⟨q, hqJ, hq.2⟩ hcJ hpcΩ hC hCΩ
  have hxa : x ≠ a := fun hh => haΩ (hh ▸ hx.2)
  have hxb : x ≠ b := fun hh => hbΩ (hh ▸ hx.2)
  obtain ⟨L, M, hL, hM, hLM, hLMmeet⟩ := hJ.exists_split hx.1 hxa hxb
  have hLJ : L ⊆ J := hLM ▸ subset_union_left
  have hMJ : M ⊆ J := hLM ▸ subset_union_right
  have hbL : b ∉ L := by
    intro hh
    have hbx : b ∈ ({x} : Set Plane) := hLMmeet ▸ (⟨hh, hM.right_mem⟩ : b ∈ L ∩ M)
    exact hxb hbx.symm
  have haM : a ∉ M := by
    intro hh
    have hax : a ∈ ({x} : Set Plane) := hLMmeet ▸ (⟨hL.left_mem, hh⟩ : a ∈ L ∩ M)
    exact hxa hax.symm
  refine ⟨x, hx.2, L, M, R, hL.reverse, hM, hR.reverse, ?_, ?_, hRΩ,
    hLMmeet.subset, ?_, ?_⟩
  · rintro z ⟨hzL, hza⟩
    exact hJΩ ⟨hLJ hzL, fun h => h.elim hza (fun hh => hbL (hh ▸ hzL))⟩
  · rintro z ⟨hzM, hzb⟩
    exact hJΩ ⟨hMJ hzM, fun h => h.elim (fun hh => haM (hh ▸ hzM)) hzb⟩
  · exact fun z hz => hRJ ⟨hz.2, hLJ hz.1⟩
  · exact fun z hz => hRJ ⟨hz.2, hMJ hz.1⟩

theorem continuous_access_extend_prefix {Ω K : Set Plane}
    {γ : ℝ → Plane} {a b q : Plane} {t r ε : ℝ}
    (hΩ : IsOpen Ω) (ha : a ∉ Ω)
    (hγ : ContinuousOn γ (Icc 0 1)) (hγ0 : γ 0 = a)
    (hK : IsArcBetween K b q) (hpoly : IsPolygonal K) (hKΩ : K ⊆ Ω)
    (ht : t ∈ Ioc 0 1) (hγt : γ t = q)
    (htail : ∀ s ∈ Ioo 0 t, γ s ∈ Ω \ K)
    (hrange : ∀ s ∈ Ioc 0 t, γ s ∈ ball a r) (hε : 0 < ε) :
    ∃ s ∈ Ioo 0 t, ∃ L : Set Plane,
      IsPolygonal L ∧ IsArcBetween L q (γ s) ∧
      L \ {q} ⊆ (Ω ∩ ball a r) \ K ∧
      (∀ u ∈ Ioo 0 s, γ u ∉ K ∪ L) ∧
      (∀ u ∈ Ioc 0 s, γ u ∈ ball a ε) := by
  classical
  let U : Set Plane := Ω ∩ ball a r
  let O : Set Plane := connectedComponentIn (U \ K) (γ (t / 2))
  have hU : IsOpen U := hΩ.inter isOpen_ball
  have htailU : ∀ s ∈ Ioo 0 t, γ s ∈ U \ K := by
    intro s hs
    exact ⟨⟨(htail s hs).1, hrange s ⟨hs.1, hs.2.le⟩⟩, (htail s hs).2⟩
  have hqU : q ∈ U := ⟨hKΩ hK.right_mem, hγt ▸ hrange t ⟨ht.1, le_rfl⟩⟩
  have hacc : PolyAccessible O q :=
    continuous_access_polygonal_endpoint_component hU hK hpoly hqU hγ ht hγt htailU
  have hOopen : IsOpen O :=
    Schoenflies.Plane.isOpen_connectedComponentIn
      (hU.sdiff hK.isArc.isClosed)
  have hOsub : O ⊆ U \ K := connectedComponentIn_subset _ _
  obtain ⟨v, hv, hvsmall⟩ := continuous_access_small_time hγ hγ0 ht.1 ht.2 hε
  have hvO : γ v ∈ O := by
    have hsub : γ '' Ioo 0 t ⊆ O := by
      apply (isPreconnected_Ioo.image γ (hγ.mono (by
        intro s hs
        exact ⟨hs.1.le, hs.2.le.trans ht.2⟩))).subset_connectedComponentIn
      · exact ⟨t / 2, ⟨half_pos ht.1, half_lt_self ht.1⟩, rfl⟩
      · rintro _ ⟨s, hs, rfl⟩
        exact htailU s hs
    exact hsub ⟨v, hv, rfl⟩
  have hqv : q ≠ γ v := fun heq => (hOsub hvO).2 (heq ▸ hK.right_mem)
  obtain ⟨Q, hQpoly, hQarc, hQO⟩ :=
    exists_simple_arc_of_polyAccessible hOopen isPreconnected_connectedComponentIn
      hqv hacc (polyAccessible_of_mem hvO)
  have hQsub : Q \ {q} ⊆ O := by
    intro x hx
    by_cases hxv : x = γ v
    · exact hxv ▸ hvO
    · exact hQO ⟨hx.1, fun h => h.elim hx.2 hxv⟩
  have hQΩ : Q ⊆ Ω := by
    intro x hx
    by_cases hxq : x = q
    · exact hxq ▸ hqU.1
    · exact (hOsub (hQsub ⟨hx, hxq⟩)).1.1
  have haQ : γ 0 ∉ Q := fun h => ha (hγ0 ▸ hQΩ h)
  obtain ⟨s, hs, hsv, hsQ, hbefore⟩ := exists_first_mem_Icc
    (hγ.mono (Icc_subset_Icc le_rfl (hv.2.le.trans ht.2))) hQarc.isArc.isClosed
    (right_mem_Icc.mpr hv.1.le) hQarc.right_mem
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (by
    intro heq
    exact haQ (heq ▸ hsQ))
  have hst : s < t := hsv.trans_lt hv.2
  have hqs : q ≠ γ s := fun heq =>
    (htail s ⟨hspos, hst⟩).2 (heq ▸ hK.right_mem)
  obtain ⟨ws, hws, _hhead, _hlast, hLsub, hLarc⟩ :=
    exists_simple_poly_of_isPolygonal hQpoly hQarc.isArc.isConnected.isPreconnected
      hqs hQarc.left_mem hsQ
  refine ⟨s, ⟨hspos, hst⟩, poly ws, ⟨ws, rfl⟩, hLarc, ?_, ?_, ?_⟩
  · intro x hx
    exact hOsub (hQsub ⟨hLsub hx.1, hx.2⟩)
  · intro u hu hmem
    rcases hmem with huK | huL
    · exact (htail u ⟨hu.1, hu.2.trans hst⟩).2 huK
    · exact hbefore u ⟨hu.1.le, hu.2.le.trans hsv⟩ hu.2 (hLsub huL)
  · intro u hu
    exact hvsmall u ⟨hu.1.le, hu.2.trans hsv⟩

private theorem no_three_exceptional_common_access_points
    {ι : Type*} (U : ι → Set Plane)
    (hopen : ∀ i, IsOpen (U i)) (hconn : ∀ i, IsConnected (U i))
    (hncompact : ∀ i, ¬ IsCompact (closure (U i)))
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (closure (U j)))
    (hacc : ∀ i x, x ∈ frontier (U i) →
      ∃ p ∈ U i, ∃ A : Set Plane, IsArcBetween A x p ∧ A \ {x} ⊆ U i)
    (i j : ι) (hij : i ≠ j) {a b c : Plane}
    (ha : a ∈ frontier (U i) ∩ frontier (U j))
    (hb : b ∈ frontier (U i) ∩ frontier (U j))
    (hc : c ∈ frontier (U i) ∩ frontier (U j))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haE : ¬ ∃ N ∈ 𝓝 a, {k | (closure (U k) ∩ N).Nonempty}.Finite)
    (hbE : ¬ ∃ N ∈ 𝓝 b, {k | (closure (U k) ∩ N).Nonempty}.Finite)
    (hcE : ¬ ∃ N ∈ 𝓝 c, {k | (closure (U k) ∩ N).Nonempty}.Finite) : False := by
  have hnot : ∀ k p, p ∈ frontier (U k) → p ∉ U k := by
    intro k p hp
    rw [(hopen k).frontier_eq] at hp
    exact hp.2
  have haUi := hnot i a ha.1
  have haUj := hnot j a ha.2
  have hbUi := hnot i b hb.1
  have hbUj := hnot j b hb.2
  have hcUi := hnot i c hc.1
  have hcUj := hnot j c hc.2
  have hUV : Disjoint (U i) (U j) := (hdisj i j hij).mono_right subset_closure
  obtain ⟨x, hx, Ta, Tb, Tc, hTa, hTb, hTc, hTaU, hTbU, hTcU, hTaTb, hTaTc, hTbTc⟩ :=
    exists_tripod_of_access_arcs (hopen i) (hconn i).isPreconnected
      haUi hbUi hcUi hab hac hbc (hacc i a ha.1) (hacc i b hb.1) (hacc i c hc.1)
  obtain ⟨y, hy, Sa, Sb, Sc, hSa, hSb, hSc, hSaV, hSbV, hScV, hSaSb, hSaSc, hSbSc⟩ :=
    exists_tripod_of_access_arcs (hopen j) (hconn j).isPreconnected
      haUj hbUj hcUj hab hac hbc (hacc j a ha.2) (hacc j b hb.2) (hacc j c hc.2)
  let P : Set Plane := Ta ∪ Sa
  let Q : Set Plane := Tb ∪ Sb
  let R : Set Plane := Tc ∪ Sc
  have hP : IsArcBetween P x y := hTa.concatenate hSa.reverse fun z hzT hzS =>
    (access_branches_cross_intersection hUV haUj haUi hTaU hSaV ⟨hzT, hzS⟩).1
  have hQ : IsArcBetween Q x y := hTb.concatenate hSb.reverse fun z hzT hzS =>
    (access_branches_cross_intersection hUV hbUj hbUi hTbU hSbV ⟨hzT, hzS⟩).1
  have hR : IsArcBetween R x y := hTc.concatenate hSc.reverse fun z hzT hzS =>
    (access_branches_cross_intersection hUV hcUj hcUi hTcU hScV ⟨hzT, hzS⟩).1
  have hpairMeet : ∀ {p q : Plane} {T S T' S' : Set Plane}, p ≠ q →
      p ∉ U i → p ∉ U j → q ∉ U i → q ∉ U j →
      T \ {p} ⊆ U i → S \ {p} ⊆ U j → T' \ {q} ⊆ U i → S' \ {q} ⊆ U j →
      T ∩ T' ⊆ {x} → S ∩ S' ⊆ {y} → (T ∪ S) ∩ (T' ∪ S') ⊆ {x, y} := by
    intro p q T S T' S' hpq hpUi hpUj hqUi hqUj hTU hSV hT'U hS'V hTT hSS
    rintro z ⟨hzT | hzS, hzT' | hzS'⟩
    · exact Or.inl (hTT ⟨hzT, hzT'⟩)
    · have hh := access_branches_cross_intersection hUV hpUj hqUi hTU hS'V ⟨hzT, hzS'⟩
      exact (hpq (hh.1.symm.trans hh.2)).elim
    · have hh := access_branches_cross_intersection hUV hqUj hpUi hT'U hSV ⟨hzT', hzS⟩
      exact (hpq (hh.2.symm.trans hh.1)).elim
    · exact Or.inr (hSS ⟨hzS, hzS'⟩)
  have hPQ : P ∩ Q ⊆ {x, y} := hpairMeet hab haUi haUj hbUi hbUj
    hTaU hSaV hTbU hSbV hTaTb hSaSb
  have hPR : P ∩ R ⊆ {x, y} := hpairMeet hac haUi haUj hcUi hcUj
    hTaU hSaV hTcU hScV hTaTc hSaSc
  have hQR : Q ∩ R ⊆ {x, y} := hpairMeet hbc hbUi hbUj hcUi hcUj
    hTbU hSbV hTcU hScV hTbTc hSbSc
  have hterm : ∀ {p : Plane}, p ∉ U i → p ∉ U j → p ∉ ({x, y} : Set Plane) := by
    intro p hpUi hpUj hh
    exact hh.elim (fun he => hpUi (he.symm ▸ hx)) (fun he => hpUj (he.symm ▸ hy))
  have haP : a ∈ P \ {x, y} := ⟨Or.inl hTa.right_mem, hterm haUi haUj⟩
  have hbQ : b ∈ Q \ {x, y} := ⟨Or.inl hTb.right_mem, hterm hbUi hbUj⟩
  have hcR : c ∈ R \ {x, y} := ⟨Or.inl hTc.right_mem, hterm hcUi hcUj⟩
  have hPsub : P ⊆ closure (U i) ∪ closure (U j) :=
    union_subset (fun z hz => Or.inl (access_branch_subset_closure hTaU
      (frontier_subset_closure ha.1) hz)) (fun z hz => Or.inr (access_branch_subset_closure hSaV
      (frontier_subset_closure ha.2) hz))
  have hQsub : Q ⊆ closure (U i) ∪ closure (U j) :=
    union_subset (fun z hz => Or.inl (access_branch_subset_closure hTbU
      (frontier_subset_closure hb.1) hz)) (fun z hz => Or.inr (access_branch_subset_closure hSbV
      (frontier_subset_closure hb.2) hz))
  have hRsub : R ⊆ closure (U i) ∪ closure (U j) :=
    union_subset (fun z hz => Or.inl (access_branch_subset_closure hTcU
      (frontier_subset_closure hc.1) hz)) (fun z hz => Or.inr (access_branch_subset_closure hScV
      (frontier_subset_closure hc.2) hz))
  rcases theta_middle_point_mem_inside hP hQ hR hPQ hPR hQR haP hbQ hcR with h | h | h
  · exact haE (jordan_inside_regular_for_noncompact_tiles U hconn hncompact hdisj i j
      (isJordanCurve_union hQ hR (fun z hzQ hzR => hQR ⟨hzQ, hzR⟩))
      (union_subset hQsub hRsub) a h)
  · exact hbE (jordan_inside_regular_for_noncompact_tiles U hconn hncompact hdisj i j
      (isJordanCurve_union hP hR (fun z hzP hzR => hPR ⟨hzP, hzR⟩))
      (union_subset hPsub hRsub) b h)
  · exact hcE (jordan_inside_regular_for_noncompact_tiles U hconn hncompact hdisj i j
      (isJordanCurve_union hP hQ (fun z hzP hzQ => hPQ ⟨hzP, hzQ⟩))
      (union_subset hPsub hQsub) c h)

private theorem continuous_access_stage_step {Ω : Set Plane} {γ : ℝ → Plane}
    {a b : Plane} {n : ℕ} (hΩ : IsOpen Ω) (ha : a ∉ Ω)
    (hγ : ContinuousOn γ (Icc 0 1)) (hγ0 : γ 0 = a)
    (S : AccessStage Ω γ a b n) : Nonempty (AccessStep S) := by
  classical
  obtain ⟨s, hs, L, hLpoly, hLarc, hLint, htail, hsmall⟩ :=
    continuous_access_extend_prefix hΩ ha hγ hγ0 S.arc S.polygonal S.subset
      S.time_mem rfl S.tail S.shrinking (ε := (1 / 2 : ℝ) ^ (n + 1)) (pow_pos (by norm_num) _)
  have hLsub : L ⊆ Ω ∩ ball a ((1 / 2 : ℝ) ^ n) := by
    intro x hx
    by_cases heq : x = γ S.time
    · exact heq ▸ ⟨S.subset S.arc.right_mem,
        S.shrinking S.time ⟨S.time_mem.1, le_rfl⟩⟩
    · exact (hLint ⟨hx, heq⟩).1
  have hmeet : ∀ x ∈ S.trace, x ∈ L → x = γ S.time := by
    intro x hxK hxL
    by_contra hxq
    exact (hLint ⟨hxL, hxq⟩).2 hxK
  let T : AccessStage Ω γ a b (n + 1) := {
    time := s
    trace := S.trace ∪ L
    time_mem := ⟨hs.1, hs.2.le.trans S.time_mem.2⟩
    arc := S.arc.concatenate hLarc hmeet
    polygonal := S.polygonal.union hLpoly ⟨γ S.time, S.arc.right_mem, hLarc.left_mem⟩
    subset := union_subset S.subset (hLsub.trans inter_subset_left)
    tail := fun u hu => ⟨(S.tail u ⟨hu.1, hu.2.trans hs.2⟩).1, htail u hu⟩
    shrinking := hsmall }
  obtain ⟨f, hfcont, hfinj, hfimage, hfzero, hfone⟩ := hLarc
  refine ⟨⟨T, f, hfcont, hfinj, hfzero, hfone, hfimage ▸ hLsub, ?_, ?_, ?_⟩⟩
  · intro x hx
    exact hmeet x hx.2 (hfimage ▸ hx.1)
  · change S.trace ∪ L = S.trace ∪ f '' Icc 0 1
    rw [hfimage]
  · exact (S.tail s hs).2

/--
The plane-family criterion used by: accessible paired boundaries
and noncompact connected tiles force local finiteness of their closures.
-/
theorem locallyFinite_plane_tiles_of_access_boundary_mates
    {ι : Type*} [Countable ι] (U : ι → Set Plane)
    (hopen : ∀ i, IsOpen (U i)) (hconn : ∀ i, IsConnected (U i))
    (hncompact : ∀ i, ¬ IsCompact (closure (U i)))
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (closure (U j)))
    (hcover : ∀ x, ∃ i, x ∈ closure (U i))
    (hacc : ∀ i x, x ∈ frontier (U i) →
      ∃ p ∈ U i, ∃ A : Set Plane, IsArcBetween A x p ∧ A \ {x} ⊆ U i)
    (hmate : ∀ i x, x ∈ frontier (U i) → ∃ j, j ≠ i ∧ x ∈ frontier (U j)) :
    LocallyFinite (fun i => closure (U i)) := by
  classical
  let E : Set Plane := {x | ¬ ∃ N ∈ 𝓝 x,
    {i | (closure (U i) ∩ N).Nonempty}.Finite}
  have hEout : ∀ x ∈ E, ∀ i, x ∉ U i := by
    intro x hx i hxi
    apply hx
    refine ⟨U i, (hopen i).mem_nhds hxi, (Set.finite_singleton i).subset ?_⟩
    intro j hj
    by_contra hji
    obtain ⟨y, hyj, hyi⟩ := hj
    exact Set.disjoint_left.mp (hdisj i j (Ne.symm hji)) hyi hyj
  let S : ι → ι → Set Plane := fun i j => E ∩ frontier (U i) ∩ frontier (U j)
  have hpair : ∀ i j, i ≠ j → (S i j).Finite := by
    intro i j hij
    by_cases hne : (S i j).Nonempty
    · obtain ⟨a, ha⟩ := hne
      by_cases htwo : ∃ b ∈ S i j, b ≠ a
      · obtain ⟨b, hb, hba⟩ := htwo
        refine ((Set.finite_singleton b).insert a).subset ?_
        intro c hc
        by_cases hca : c = a
        · exact Or.inl hca
        · by_cases hcb : c = b
          · exact Or.inr hcb
          · exact (no_three_exceptional_common_access_points U hopen hconn hncompact hdisj hacc
              i j hij ⟨ha.1.2, ha.2⟩ ⟨hb.1.2, hb.2⟩ ⟨hc.1.2, hc.2⟩
              (Ne.symm hba) (Ne.symm hca) (Ne.symm hcb) ha.1.1 hb.1.1 hc.1.1).elim
      · refine (Set.finite_singleton a).subset ?_
        intro b hb
        by_contra hba
        exact htwo ⟨b, hb, hba⟩
    · have hSempty : S i j = ∅ := not_nonempty_iff_eq_empty.mp hne
      rw [hSempty]
      exact finite_empty
  let T : ι → ι → Set Plane := fun i j => if i ≠ j then S i j else ∅
  have hT : ∀ i j, (T i j).Countable := by
    intro i j
    by_cases hij : i ≠ j
    · simpa only [T, ite_eq_left hij] using (hpair i j hij).countable
    · simp only [T, ite_eq_right hij]
      exact countable_empty
  have hcount : (⋃ i, ⋃ j, T i j).Countable :=
    Set.countable_iUnion fun i => Set.countable_iUnion (hT i)
  have hEcount : E.Countable := hcount.mono (by
    intro x hx
    obtain ⟨i, hxi⟩ := hcover x
    have hxf : x ∈ frontier (U i) := by
      rw [(hopen i).frontier_eq]
      exact ⟨hxi, hEout x hx i⟩
    obtain ⟨j, hji, hxj⟩ := hmate i x hxf
    refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, ?_⟩⟩
    simp only [T, ite_eq_left (Ne.symm hji)]
    exact ⟨⟨hx, hxf⟩, hxj⟩)
  exact locallyFinite_closure_of_countable_exceptional U hconn hncompact hEcount

theorem continuous_access_shrinking_arc_chain {Ω : Set Plane} {γ : ℝ → Plane} {a : Plane}
    (hΩ : IsOpen Ω) (ha : a ∉ Ω) (hγ : ContinuousOn γ (Icc 0 1))
    (hγ0 : γ 0 = a) (hinto : ∀ t ∈ Ioc 0 1, γ t ∈ Ω) :
    ∃ f : ℕ → ℝ → Plane,
      (∀ n, ContinuousOn (f n) (Icc 0 1)) ∧
      (∀ n, InjOn (f n) (Icc 0 1)) ∧
      (∀ n, f n 1 = f (n + 1) 0) ∧
      (∀ n, f n '' Icc 0 1 ⊆ ball a ((1 / 2 : ℝ) ^ n)) ∧
      (∀ n, a ∉ f n '' Icc 0 1) ∧
      (∀ m n, m < n → (f m '' Icc 0 1) ∩ (f n '' Icc 0 1) ⊆ {f n 0}) ∧
      (∀ m n, m + 1 < n → f n 0 ∉ f m '' Icc 0 1) ∧
      f 0 0 ∈ Ω ∧ (⋃ n, f n '' Icc 0 1) ⊆ Ω := by
  classical
  obtain ⟨b, ⟨S0⟩⟩ := continuous_access_initial_stage hΩ ha hγ hγ0 hinto
  let next : ∀ n (S : AccessStage Ω γ a b n), AccessStep S :=
    fun _ S => Classical.choice (continuous_access_stage_step hΩ ha hγ hγ0 S)
  let seq : ∀ n, AccessStage Ω γ a b n :=
    Nat.rec S0 (fun n S => (next n S).next)
  let f : ℕ → ℝ → Plane := fun n => (next n (seq n)).piece
  have hseq : ∀ n, seq (n + 1) = (next n (seq n)).next := fun _ => rfl
  have hmono : Monotone (fun n => (seq n).trace) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hseq, (next n (seq n)).next_prefix]
    exact subset_union_left
  have hsub : ∀ n, f n '' Icc 0 1 ⊆ (seq (n + 1)).trace := by
    intro n
    rw [hseq, (next n (seq n)).next_prefix]
    exact subset_union_right
  have hfΩ : ∀ n, f n '' Icc 0 1 ⊆ Ω := fun n =>
    (next n (seq n)).subset.trans inter_subset_left
  refine ⟨f, (fun n => (next n (seq n)).continuousOn),
    (fun n => (next n (seq n)).injOn), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (next n (seq n)).one.trans (next (n + 1) (seq (n + 1))).zero.symm
  · intro n
    exact (next n (seq n)).subset.trans inter_subset_right
  · intro n hx
    exact ha (hfΩ n hx)
  · intro m n hmn x hx
    have hxold : x ∈ (seq n).trace :=
      hmono (Nat.succ_le_iff.mpr hmn) (hsub m hx.1)
    have hxeq : x = γ (seq n).time := (next n (seq n)).old_inter ⟨hx.2, hxold⟩
    exact hxeq.trans (next n (seq n)).zero.symm
  · intro m n hmn hx
    cases n with
    | zero => omega
    | succ k =>
      have hxold : f (k + 1) 0 ∈ (seq k).trace := hmono (by omega) (hsub m hx)
      change (next (k + 1) (seq (k + 1))).piece 0 ∈ (seq k).trace at hxold
      rw [(next (k + 1) (seq (k + 1))).zero, hseq] at hxold
      exact (next k (seq k)).newend_not_old hxold
  · change (next 0 (seq 0)).piece 0 ∈ Ω
    rw [(next 0 (seq 0)).zero]
    exact (seq 0).subset (seq 0).arc.right_mem
  · exact iUnion_subset hfΩ

/--
The literal continuous-access condition supplies a simple access arc; no polygonal
accessibility is assumed. This is the access step.
-/
theorem continuous_boundary_access_simple_arc {Ω : Set Schoenflies.Plane}
    {γ : ℝ → Schoenflies.Plane} {a : Schoenflies.Plane}
    (hΩ : IsOpen Ω) (ha : a ∉ Ω) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = a) (hinto : ∀ t ∈ Set.Ioc 0 1, γ t ∈ Ω) :
    ∃ b ∈ Ω, ∃ A : Set Schoenflies.Plane,
      Schoenflies.IsArcBetween A a b ∧ A \ {a} ⊆ Ω := by
  obtain ⟨f, hc, hi, hj, hb, hav, hm, hf, hstart, hU⟩ :=
    continuous_access_shrinking_arc_chain hΩ ha hγ hγ0 hinto
  obtain ⟨A, hA, hsub⟩ := exists_arc_of_shrinking_arc_chain f a hc hi hj hb hav hm hf
  exact ⟨f 0 0, hstart, A, hA.reverse, hsub.trans hU⟩

end LowDimensionalTopology.Geometry.Auxiliary.Topology
