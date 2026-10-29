module

public import LowDimensionalTopology.Geometry.Quasiconformal.WirtingerWeakApproximation
public import LowDimensionalTopology.Geometry.Quasiconformal.RectanglePrimitive
public import LowDimensionalTopology.Geometry.Quasiconformal.RealPotentialRigidity
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.LocalPotentialMonodromy
public import Mathlib.Tactic.LinearCombination

/-!
# C1 primitives of continuous distributionally closed planar real forms

Actual locally L1 weak derivatives give zero boundary integrals on rectangles
inside the original domain. Local real C1 potentials have locally constant
transitions; the genuine local-potential germ covering glues them over the same
simply connected open domain. The result gives both actual ordinary Wirtinger
derivatives at every point, with no stronger regularity or global Lp hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Metric MeasureTheory Filter Topology Complex TopologicalSpace
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The real one-form associated to `u dz + v dbar z` has zero integral around
every axis-parallel closed rectangle inside the original domain. The equality
of the represented weak complex derivatives is an a.e. equality on that domain. -/
theorem distributional_wirtinger_rect_integral_eq_zero
    {D : Set ℂ} {u uz uzb v vz vzb : ℂ → ℂ}
    (hD : IsOpen D) (hu : ContinuousOn u D) (hv : ContinuousOn v D)
    (hwu : HasDistributionalWirtingerDerivatives u uz uzb D)
    (hwv : HasDistributionalWirtingerDerivatives v vz vzb D)
    (hclosed : uzb =ᵐ[volume.restrict D] vz)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hR : closedRect a b c d ⊆ D) :
    (∫ x in a..b, u ((x : ℂ) + (c : ℂ) * I) + v ((x : ℂ) + (c : ℂ) * I)) +
      (∫ y in c..d, I * (u ((b : ℂ) + (y : ℂ) * I) - v ((b : ℂ) + (y : ℂ) * I))) -
      (∫ x in a..b, u ((x : ℂ) + (d : ℂ) * I) + v ((x : ℂ) + (d : ℂ) * I)) -
      (∫ y in c..d, I * (u ((a : ℂ) + (y : ℂ) * I) - v ((a : ℂ) + (y : ℂ) * I))) = 0 := by
  obtain ⟨haclU, hux, huy⟩ := isACL_of_distributional_wirtinger hD hu hwu
  obtain ⟨haclV, hvx, hvy⟩ := isACL_of_distributional_wirtinger hD hv hwv
  have huxloc : ∀ C ⊆ D, IsCompact C → IntegrableOn (partialX u) C := by
    intro C hCD hC
    exact (hwu.real_partials.1.2.1.integrableOn_compact_subset hCD hC).congr
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hCD hux))
  have huyloc : ∀ C ⊆ D, IsCompact C → IntegrableOn (partialY u) C := by
    intro C hCD hC
    exact (hwu.real_partials.2.2.1.integrableOn_compact_subset hCD hC).congr
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hCD huy))
  have hvxloc : ∀ C ⊆ D, IsCompact C → IntegrableOn (partialX v) C := by
    intro C hCD hC
    exact (hwv.real_partials.1.2.1.integrableOn_compact_subset hCD hC).congr
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hCD hvx))
  have hvyloc : ∀ C ⊆ D, IsCompact C → IntegrableOn (partialY v) C := by
    intro C hCD hC
    exact (hwv.real_partials.2.2.1.integrableOn_compact_subset hCD hC).congr
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hCD hvy))
  have hOR : openRect a b c d ⊆ closedRect a b c d :=
    fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  have hOD : openRect a b c d ⊆ D := hOR.trans hR
  have huxi := (huxloc _ hR (isCompact_closedRect a b c d)).mono_set hOR
  have huyi := (huyloc _ hR (isCompact_closedRect a b c d)).mono_set hOR
  have hvxi := (hvxloc _ hR (isCompact_closedRect a b c d)).mono_set hOR
  have hvyi := (hvyloc _ hR (isCompact_closedRect a b c d)).mono_set hOR
  have hcurl : ∀ᵐ z ∂(volume.restrict (openRect a b c d)),
      I * (partialX u z - partialX v z) - (partialY u z + partialY v z) = 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hOD hux,
      ae_restrict_of_ae_restrict_of_subset hOD huy,
      ae_restrict_of_ae_restrict_of_subset hOD hvx,
      ae_restrict_of_ae_restrict_of_subset hOD hvy,
      ae_restrict_of_ae_restrict_of_subset hOD hclosed] with z hxU hyU hxV hyV hc
    rw [hxU, hyU, hxV, hyV, hc]
    ring
  have hzero : I * ((∫ z in openRect a b c d, partialX u z) -
      ∫ z in openRect a b c d, partialX v z) -
      ((∫ z in openRect a b c d, partialY u z) +
        ∫ z in openRect a b c d, partialY v z) = 0 := by
    calc
      _ = ∫ z in openRect a b c d,
          I * (partialX u z - partialX v z) - (partialY u z + partialY v z) := by
        have hsplit := integral_sub ((huxi.sub hvxi).const_mul I) (huyi.add hvyi)
        have hxsplit := integral_sub huxi hvxi
        have hysplit := integral_add huyi hvyi
        simp only [Pi.sub_apply, Pi.add_apply] at hsplit hxsplit hysplit
        rw [hsplit, integral_const_mul, hxsplit, hysplit]
      _ = ∫ _z in openRect a b c d, (0 : ℂ) := integral_congr_ae hcurl
      _ = 0 := by simp
  have huH := eq9_9_green haclU huyloc hab hcd hR
  have huV := eq9_10_green haclU huxloc hab hcd hR
  have hvH := eq9_9_green haclV hvyloc hab hcd hR
  have hvV := eq9_10_green haclV hvxloc hab hcd hR
  have hH (f : ℂ → ℂ) (hf : ContinuousOn f D) (t : ℝ) (ht : t ∈ Icc c d) :
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (t : ℂ) * I)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab.le
    refine hf.comp
      (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (t : ℂ) * I).continuousOn
      fun x hx => hR ?_
    exact ⟨by simpa using hx.1, by simpa using hx.2, by simpa using ht.1,
      by simpa using ht.2⟩
  have hV (f : ℂ → ℂ) (hf : ContinuousOn f D) (s : ℝ) (hs : s ∈ Icc a b) :
      IntervalIntegrable (fun y : ℝ => f ((s : ℂ) + (y : ℂ) * I)) volume c d := by
    apply ContinuousOn.intervalIntegrable_of_Icc hcd.le
    refine hf.comp
      (by fun_prop : Continuous fun y : ℝ => (s : ℂ) + (y : ℂ) * I).continuousOn
      fun y hy => hR ?_
    exact ⟨by simpa using hs.1, by simpa using hs.2, by simpa using hy.1,
      by simpa using hy.2⟩
  rw [intervalIntegral.integral_add (hH u hu c ⟨le_rfl, hcd.le⟩)
      (hH v hv c ⟨le_rfl, hcd.le⟩),
    intervalIntegral.integral_add (hH u hu d ⟨hcd.le, le_rfl⟩)
      (hH v hv d ⟨hcd.le, le_rfl⟩),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hV u hu b ⟨hab.le, le_rfl⟩)
      (hV v hv b ⟨hab.le, le_rfl⟩),
    intervalIntegral.integral_sub (hV u hu a ⟨le_rfl, hab.le⟩)
      (hV v hv a ⟨le_rfl, hab.le⟩)]
  linear_combination huH + hvH + I * huV - I * hvV + hzero

/-- Genuine weak closedness gives actual real C1 potentials on neighborhoods
of every point of the original open domain. -/
theorem exists_local_wirtinger_potential
    {D : Set ℂ} {u uz uzb v vz vzb : ℂ → ℂ}
    (hD : IsOpen D) (hu : ContinuousOn u D) (hv : ContinuousOn v D)
    (hwu : HasDistributionalWirtingerDerivatives u uz uzb D)
    (hwv : HasDistributionalWirtingerDerivatives v vz vzb D)
    (hclosed : uzb =ᵐ[volume.restrict D] vz)
    {x : ℂ} (hx : x ∈ D) :
    ∃ (r : ℝ) (F : ℂ → ℂ), 0 < r ∧ ball x r ⊆ D ∧
      ContDiffOn ℝ 1 F (ball x r) ∧
      ∀ z ∈ ball x r,
        fderiv ℝ F z 1 = u z + v z ∧ fderiv ℝ F z I = I * (u z - v z) := by
  obtain ⟨q, hab, hcd, hRD, hxR⟩ := acl_exists_rat_rect hD hx
  obtain ⟨F, hFC1, hFder⟩ := exists_contDiffOn_primitive_on_rectangle hab hcd
    ((hu.add hv).mono hRD)
    ((continuousOn_const.mul (hu.sub hv)).mono hRD)
    (fun a b c d hab' hcd' hsub =>
      distributional_wirtinger_rect_integral_eq_zero hD hu hv hwu hwv hclosed
        hab' hcd' (hsub.trans hRD))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((acl_isOpen_openRect q.1 q.2.1 q.2.2.1 q.2.2.2).mem_nhds hxR)
  have hOD : openRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ D :=
    (fun z hz => hRD ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩)
  exact ⟨r, F, hr, hball.trans hOD, hFC1.mono hball,
    fun z hz => hFder z (hball hz)⟩

/-- Actual local real C1 potentials of a real one-form on an arbitrary simply
connected open planar domain glue to an actual real C1 potential on that domain. -/
theorem exists_contDiffOn_primitive_of_local_potentials
    {D : Set ℂ} {P Q : ℂ → ℂ} (hD : IsOpen D) (hSC : IsSimplyConnected D)
    (hlocal : ∀ x ∈ D, ∃ (r : ℝ) (F : ℂ → ℂ), 0 < r ∧ ball x r ⊆ D ∧
      ContDiffOn ℝ 1 F (ball x r) ∧
      ∀ z ∈ ball x r, fderiv ℝ F z 1 = P z ∧ fderiv ℝ F z I = Q z) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ 1 f D ∧
      ∀ z ∈ D, fderiv ℝ f z 1 = P z ∧ fderiv ℝ f z I = Q z := by
  classical
  have : SimplyConnectedSpace D := hSC.simplyConnectedSpace
  have : LocallyPathConnectedSpace D := hD.locallyPathConnectedSpace
  choose r F hr hsub hC1 hcoord using fun x : D => hlocal x x.property
  let U : D → Opens (TopCat.of D) := fun i =>
    ⟨Subtype.val ⁻¹' ball (i : ℂ) (r i), isOpen_ball.preimage continuous_subtype_val⟩
  have himage (i : D) : Subtype.val '' (U i : Set D) = ball (i : ℂ) (r i) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hz
      exact ⟨⟨z, hsub i hz⟩, hz, rfl⟩
  have hcover : ∀ x : D, ∃ i : D, x ∈ U i :=
    fun x => ⟨x, mem_ball_self (hr x)⟩
  have hconnected : ∀ i : D, IsPreconnected (U i : Set D) := by
    intro i
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [himage]
    exact (convex_ball (i : ℂ) (r i)).isPreconnected
  have htransition : ∀ i j x : D, x ∈ U i → x ∈ U j →
      ∀ᶠ (y : D) in 𝓝 x, F i (y : ℂ) - F j (y : ℂ) = F i (x : ℂ) - F j (x : ℂ) := by
    intro i j x hxi hxj
    have hFi : DifferentiableOn ℝ (F i)
        (ball (i : ℂ) (r i) ∩ ball (j : ℂ) (r j)) :=
      (hC1 i).differentiableOn_one.mono inter_subset_left
    have hFj : DifferentiableOn ℝ (F j)
        (ball (i : ℂ) (r i) ∩ ball (j : ℂ) (r j)) :=
      (hC1 j).differentiableOn_one.mono inter_subset_right
    have hnear := potential_difference_eventually_constant (isOpen_ball.inter isOpen_ball)
      hFi hFj (fun z hz => ((hcoord i z hz.1).1).trans ((hcoord j z hz.2).1).symm)
      (fun z hz => ((hcoord i z hz.1).2).trans ((hcoord j z hz.2).2).symm)
      (show (x : ℂ) ∈ ball (i : ℂ) (r i) ∩ ball (j : ℂ) (r j) from ⟨hxi, hxj⟩)
    exact continuous_subtype_val.continuousAt.eventually hnear
  obtain ⟨φ, hφ⟩ :=
    LowDimensionalTopology.Geometry.exists_global_potential_of_local_constant_transitions
      U (fun i x => F i (x : ℂ)) hcover hconnected htransition
  let f : ℂ → ℂ := fun z => if hz : z ∈ D then φ ⟨z, hz⟩ else 0
  have hrecovery : ∀ x ∈ D, ContDiffAt ℝ 1 f x ∧
      fderiv ℝ f x 1 = P x ∧ fderiv ℝ f x I = Q x := by
    intro x hx
    obtain ⟨i, c, hxi, hnear⟩ := hφ ⟨x, hx⟩
    obtain ⟨V, hVsub, hVopen, hxV⟩ := _root_.mem_nhds_iff.mp hnear
    have hWopen : IsOpen (Subtype.val '' V : Set ℂ) :=
      hD.isOpenMap_subtype_val V hVopen
    have hxW : x ∈ (Subtype.val '' V : Set ℂ) := ⟨⟨x, hx⟩, hxV, rfl⟩
    have heq : f =ᶠ[𝓝 x] (fun z => F i z + c) := by
      filter_upwards [hWopen.mem_nhds hxW] with z hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hfval : f (y : ℂ) = φ y := by simp only [f, dite_eq_left y.property]
      exact hfval.trans (hVsub hy)
    have hFC1 : ContDiffAt ℝ 1 (F i) x :=
      (hC1 i).contDiffAt (isOpen_ball.mem_nhds hxi)
    have hdf : HasFDerivAt f (fderiv ℝ (F i) x) x :=
      ((hFC1.differentiableAt one_ne_zero).hasFDerivAt.add_const c).congr_of_eventuallyEq heq
    refine ⟨(hFC1.add contDiffAt_const).congr_of_eventuallyEq heq, ?_, ?_⟩
    · rw [hdf.fderiv]
      exact (hcoord i x hxi).1
    · rw [hdf.fderiv]
      exact (hcoord i x hxi).2
  exact ⟨f, hD.contDiffOn_iff.mpr (fun _ hx => (hrecovery _ hx).1),
    fun z hz => (hrecovery z hz).2⟩

/-- Continuous coefficients on the original
simply connected domain, genuine locally L1 weak derivatives, and their actual
distributional closedness give a real C1 function with both prescribed
ordinary Wirtinger derivatives at every point. -/
theorem exists_contDiffOn_wirtinger_primitive
    {D : Set ℂ} {u uz uzb v vz vzb : ℂ → ℂ}
    (hD : IsOpen D) (hSC : IsSimplyConnected D)
    (hu : ContinuousOn u D) (hv : ContinuousOn v D)
    (hwu : HasDistributionalWirtingerDerivatives u uz uzb D)
    (hwv : HasDistributionalWirtingerDerivatives v vz vzb D)
    (hclosed : uzb =ᵐ[MeasureTheory.volume.restrict D] vz) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ 1 f D ∧
      ∀ z ∈ D, LiZhongQC.dz f z = u z ∧ LiZhongQC.dzbar f z = v z := by
  obtain ⟨f, hC1, hcoord⟩ := exists_contDiffOn_primitive_of_local_potentials hD hSC
    (fun x hx => exists_local_wirtinger_potential hD hu hv hwu hwv hclosed hx)
  refine ⟨f, hC1, fun z hz => ?_⟩
  obtain ⟨h1, hI⟩ := hcoord z hz
  have hII : I * (I * (u z - v z)) = -(u z - v z) := by
    rw [← mul_assoc, I_mul_I, neg_one_mul]
  constructor
  · change (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2 = u z
    rw [h1, hI, hII]
    ring
  · change (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2 = v z
    rw [h1, hI, hII]
    ring

/-- The same result using represented weak derivatives in the two real
coordinate directions, as in the hypothesis of the English statement. -/
theorem exists_contDiffOn_wirtinger_primitive_of_distributional_partials
    {D : Set ℂ} {u ux uy v vx vy : ℂ → ℂ}
    (hD : IsOpen D) (hSC : IsSimplyConnected D)
    (hu : ContinuousOn u D) (hv : ContinuousOn v D)
    (hwu : HasDistributionalPartials u ux uy D)
    (hwv : HasDistributionalPartials v vx vy D)
    (hclosed : (fun z => (ux z + I * uy z) / 2) =ᵐ[MeasureTheory.volume.restrict D]
      (fun z => (vx z - I * vy z) / 2)) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ 1 f D ∧
      ∀ z ∈ D, LiZhongQC.dz f z = u z ∧ LiZhongQC.dzbar f z = v z :=
  exists_contDiffOn_wirtinger_primitive hD hSC hu hv hwu.wirtinger hwv.wirtinger hclosed

end LowDimensionalTopology.Geometry.Quasiconformal
