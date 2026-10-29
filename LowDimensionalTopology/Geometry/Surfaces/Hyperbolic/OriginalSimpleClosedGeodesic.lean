module

public import LowDimensionalTopology.Geometry.Fuchsian.Action.SourceHalfPlaneGroup
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicLength
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HalfPlaneH3
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalCollarModels
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Int.Init

/-!
# Original single-traversal closed geodesics and their actual axis stabilizers

The actual period-circle map supplies single traversal of the original curve.
Its complete lift and full-period matrix are constructed in the same covering.
Integer equivariance and the actual free deck action identify every return of
an axis point with a power of that same matrix in the projective group.
The native entire-axis embedding then gives simplicity and the full stabilizer.
-/

public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane MatrixGroups Pointwise

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

private theorem integer_equivariance
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (f : ℝ → ℍ)
    (hperiod : ∀ t : ℝ, f (t + 1) = A • f t) (n : ℤ) (t : ℝ) :
    A ^ n • f t = f (t + (n : ℝ)) := by
  have hstep (s : ℝ) : A • f s = f (s + 1) := (hperiod s).symm
  have hinv (s : ℝ) : A⁻¹ • f s = f (s - 1) := by
    calc
      A⁻¹ • f s = A⁻¹ • f ((s - 1) + 1) := by rw [sub_add_cancel]
      _ = A⁻¹ • (A • f (s - 1)) := by rw [hperiod]
      _ = f (s - 1) := inv_smul_smul A _
  induction n using Int.induction_on generalizing t with
  | zero => simp
  | succ n ih =>
    rw [zpow_add, zpow_one, mul_smul, hstep, ih]
    congr 1
    push_cast
    ring
  | pred n ih =>
    rw [zpow_sub, zpow_one, mul_smul, hinv, ih]
    congr 1
    push_cast
    ring

private theorem axis_point_move_mem_zpowers
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X))
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAΓ : A ∈ Γ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (f : C(ℝ, ℍ)) (hproj : ∀ t : ℝ, M.halfPlaneCover (f t) = q.curve t)
    (hperiod : ∀ t : ℝ, f (t + 1) = A • f t)
    (hfull : range f = (hHyperbolicAxis A hA ht).carrier)
    (C : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hC : C ∈ Γ)
    (z : ℍ) (hz : z ∈ (hHyperbolicAxis A hA ht).carrier)
    (hCz : C • z ∈ (hHyperbolicAxis A hA ht).carrier) :
    realSLMobius C ∈ Subgroup.zpowers (realSLMobius A) := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨s, hs⟩ := (hfull.symm ▸ hz : z ∈ range f)
  obtain ⟨t, hft⟩ := (hfull.symm ▸ hCz : C • z ∈ range f)
  have hq : q.curve s = q.curve t := by
    rw [← hproj s, ← hproj t, hs, hft, LiZhongQC.s30a_p_smul hp hC]
  have hcircleeq : (t : AddCircle (1 : ℝ)) = (s : AddCircle (1 : ℝ)) := by
    apply hcircle
    change q.curve t = q.curve s
    exact hq.symm
  have hzero : ((t - s : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, hcircleeq, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  have hts : t = s + (n : ℝ) := by
    simp only [zsmul_eq_mul, mul_one] at hn
    linarith
  have hact : C • f s = A ^ n • f s := by
    calc
      C • f s = C • z := congrArg (fun w : ℍ => C • w) hs
      _ = f t := hft.symm
      _ = f (s + (n : ℝ)) := congrArg f hts
      _ = A ^ n • f s := (integer_equivariance A f hperiod n s).symm
  let D := (A ^ n)⁻¹ * C
  have hDΓ : D ∈ Γ := Γ.mul_mem (Γ.inv_mem (Γ.zpow_mem hAΓ n)) hC
  have hfix : D • f s = f s := by
    dsimp only [D]
    rw [mul_smul, hact, inv_smul_smul]
  have hD : realSLMobius D = 1 := by
    rcases LiZhongQC.s27g_actsFreely hp D hDΓ (f s) hfix with he | he
    · rw [he, map_one]
    · rw [he, realSLMobius_neg, map_one]
  have he : (realSLMobius A ^ n)⁻¹ * realSLMobius C = 1 := by
    simpa only [D, map_mul, map_inv, map_zpow] using hD
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, inv_mul_eq_one.mp he⟩

/-- Injectivity of the actual period-circle map makes the internally constructed
full-period matrix simple and generates its entire actual axis stabilizer. -/
theorem OriginalClosedGeodesic.exists_simple_axis_of_circle_injective
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ∃ (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (_hA : realSLMobius A ≠ 1)
      (_ht : 4 < (Matrix.trace A.val) ^ 2), A ∈ Γ ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      Fuchsian.IsSimple (Γ.map realSLMobius) (realSLMobius A) ∧
      Fuchsian.axisSetStabilizer (Γ.map realSLMobius) (realSLMobius A) =
        Subgroup.zpowers (realSLMobius A) := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨A, hA, ht, hAΓ, hcov, f, hproj, hperiod, hfull⟩ :=
    q.exists_actual_hyperbolic_axis_lift hp
  let H := Γ.map realSLMobius
  let a := realSLMobius A
  let S := mobiusGeodesicAxis a
  have haH : a ∈ H := Subgroup.mem_map.mpr ⟨A, hAΓ, rfl⟩
  have hpoint (g : complexMobiusGroup) (hg : g ∈ H) (x : UpperHalfSpace)
      (hx : x ∈ S) (hgx : g • x ∈ S) : g ∈ Subgroup.zpowers a := by
    change g ∈ Γ.map realSLMobius at hg
    obtain ⟨C, hC, rfl⟩ := Subgroup.mem_map.mp hg
    change x ∈ mobiusGeodesicAxis (realSLMobius A) at hx
    change realSLMobius C • x ∈ mobiusGeodesicAxis (realSLMobius A) at hgx
    rw [halfPlaneH3Embed_hyperbolic_axis A hA ht] at hx hgx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [halfPlaneH3Embed_realSL] at hgx
    obtain ⟨w, hw, hew⟩ := hgx
    have hCz : C • z ∈ (hHyperbolicAxis A hA ht).carrier :=
      (halfPlaneH3Embed_injective hew) ▸ hw
    exact axis_point_move_mem_zpowers q hp hcircle A hAΓ hA ht f hproj hperiod hfull
      C hC z hz hCz
  have hstable : a ∈ Fuchsian.axisSetStabilizer H a := by
    refine ⟨haH, ?_⟩
    change (fun x : UpperHalfSpace => a • x) '' mobiusGeodesicAxis a = mobiusGeodesicAxis a
    simpa only [mul_inv_cancel_right] using (mobiusGeodesicAxis_conjugation a a).symm
  have hpowle : Subgroup.zpowers a ≤ Fuchsian.axisSetStabilizer H a :=
    Subgroup.zpowers_le.mpr hstable
  have hx0 : halfPlaneH3Embed (f 0) ∈ S := by
    change halfPlaneH3Embed (f 0) ∈ mobiusGeodesicAxis (realSLMobius A)
    rw [halfPlaneH3Embed_hyperbolic_axis A hA ht]
    refine ⟨f 0, ?_, rfl⟩
    rw [← hfull]
    exact mem_range_self 0
  have hgen : Fuchsian.axisSetStabilizer H a = Subgroup.zpowers a := by
    apply le_antisymm
    · intro g hg
      apply hpoint g hg.1 (halfPlaneH3Embed (f 0)) hx0
      have he : (fun x : UpperHalfSpace => g • x) '' S = S := hg.2
      rw [← he]
      exact ⟨_, hx0, rfl⟩
    · exact hpowle
  have hsimple : Fuchsian.IsSimple H a := by
    refine ⟨haH, (realSLMobius_hyperbolic_iff A hA).mpr ht, ?_⟩
    intro g hg
    by_cases he : (fun x : UpperHalfSpace => g • x) '' S = S
    · exact Or.inl he
    · right
      apply Set.disjoint_left.mpr
      rintro _ ⟨x, hx, rfl⟩ hgx
      have hgm : g ∈ Fuchsian.axisSetStabilizer H a := hpowle (hpoint g hg x hx hgx)
      exact he hgm.2
  exact ⟨A, hA, ht, hAΓ, hcov, hsimple, hgen⟩

/-- Injectivity of the original period-circle map makes its actual full-period
matrix generate the entire stabilizer of its genuine canonical strip. -/
theorem OriginalClosedGeodesic.exists_canonical_collar_stabilizer_of_circle_injective
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ∃ (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (_hA : realSLMobius A ≠ 1)
      (_ht : 4 < (Matrix.trace A.val) ^ 2), A ∈ Γ ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      Fuchsian.IsSimple (Γ.map realSLMobius) (realSLMobius A) ∧
      mobiusSetStabilizer (Γ.map realSLMobius) (Fuchsian.nativeCanonicalSphere A) =
        Subgroup.zpowers (realSLMobius A) := by
  obtain ⟨A, hA, ht, hAΓ, hcov, hs, hgen⟩ :=
    q.exists_simple_axis_of_circle_injective hp hcircle
  refine ⟨A, hA, ht, hAΓ, hcov, hs, ?_⟩
  calc
    mobiusSetStabilizer (Γ.map realSLMobius) (Fuchsian.nativeCanonicalSphere A) =
        Fuchsian.axisSetStabilizer (Γ.map realSLMobius) (realSLMobius A) := by
      ext g
      change (g ∈ Γ.map realSLMobius ∧
        g.val '' Fuchsian.nativeCanonicalSphere A = Fuchsian.nativeCanonicalSphere A) ↔
        (g ∈ Γ.map realSLMobius ∧
          (fun x : UpperHalfSpace => g • x) '' mobiusGeodesicAxis (realSLMobius A) =
            mobiusGeodesicAxis (realSLMobius A))
      apply and_congr_right
      intro hg
      obtain ⟨B, _hBΓ, rfl⟩ := Subgroup.mem_map.mp hg
      exact (Fuchsian.nativeCanonicalSphere_image_eq_iff_axis A B hs.2.1).trans
        (hyperbolic_axis_translate_eq_iff B A hA ht).symm
    _ = Subgroup.zpowers (realSLMobius A) := hgen

/-- Inside the actual canonical strip of an original single-traversal closed
geodesic, the given covering fibers are exactly its full-period integer orbits. -/
theorem OriginalClosedGeodesic.exists_canonical_collar_fibers_of_circle_injective
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ∃ (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (_hA : realSLMobius A ≠ 1)
      (_ht : 4 < (Matrix.trace A.val) ^ 2), A ∈ Γ ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      Fuchsian.IsSimple (Γ.map realSLMobius) (realSLMobius A) ∧
      ∀ z ∈ hCanonicalRegion A, ∀ w ∈ hCanonicalRegion A,
        M.halfPlaneCover z = M.halfPlaneCover w ↔ ∃ n : ℤ, w = A ^ n • z := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  obtain ⟨A, hA, ht, hAΓ, hcov, hs, hstab⟩ :=
    q.exists_canonical_collar_stabilizer_of_circle_injective hp hcircle
  let P := Fuchsian.sourceHalfPlaneFuchsianGroup (LiZhongQC.utm_x2_isFuchsian hp)
  have hG : IsEllipticFree (Γ.map realSLMobius) := by
    intro f hf
    obtain ⟨E, hEΓ, hEf⟩ := Subgroup.mem_map.mp f.property
    have hEll : MobiusElliptic (realSLMobius E) := by
      rw [hEf]
      exact hf
    have htr := (realSLMobius_elliptic_iff E hEll.1).mp hEll
    have hsmall : |E 0 0 + E 1 1| < 2 := by
      apply abs_lt_of_sq_lt_sq ?_ (by norm_num)
      simpa only [Matrix.trace_fin_two, show (2 : ℝ) ^ 2 = 4 by norm_num] using htr
    obtain ⟨τ, hτ⟩ := LiZhongQC.s27g_elliptic_fixed hsmall
    rcases LiZhongQC.s27g_actsFreely hp E hEΓ τ hτ with he | he
    · rw [he] at htr
      norm_num [Matrix.trace_fin_two] at htr
    · rw [he] at htr
      norm_num [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_fin_two] at htr
  have hstable := Fuchsian.nativeCanonicalSphere_simple_stable P hG A hs
  refine ⟨A, hA, ht, hAΓ, hcov, hs, ?_⟩
  intro z hz w hw
  constructor
  · intro hzw
    obtain ⟨C, hCΓ, hCzw⟩ := (hp.2.2.2 z w).mp hzw
    have hCH : realSLMobius C ∈ Γ.map realSLMobius :=
      Subgroup.mem_map.mpr ⟨C, hCΓ, rfl⟩
    have hCstab : realSLMobius C ∈
        mobiusSetStabilizer (Γ.map realSLMobius) (Fuchsian.nativeCanonicalSphere A) := by
      apply mobiusStableSet_mem_stabilizer_of_intersection hstable _ hCH
      refine ⟨Mobius.halfPlaneBoundaryPoint w, ?_, ⟨w, hw, rfl⟩⟩
      refine ⟨Mobius.halfPlaneBoundaryPoint z, ⟨z, hz, rfl⟩, ?_⟩
      exact (realSLMobius_action C z).trans (congrArg Mobius.halfPlaneBoundaryPoint hCzw)
    rw [hstab] at hCstab
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hCstab
    refine ⟨n, ?_⟩
    apply Mobius.halfPlaneBoundaryPoint_injective
    calc
      Mobius.halfPlaneBoundaryPoint w = Mobius.halfPlaneBoundaryPoint (C • z) :=
        congrArg Mobius.halfPlaneBoundaryPoint hCzw.symm
      _ = (realSLMobius C).val (Mobius.halfPlaneBoundaryPoint z) :=
        (realSLMobius_action C z).symm
      _ = (realSLMobius (A ^ n)).val (Mobius.halfPlaneBoundaryPoint z) := by
        rw [map_zpow, hn]
      _ = Mobius.halfPlaneBoundaryPoint (A ^ n • z) := realSLMobius_action (A ^ n) z
  · rintro ⟨n, rfl⟩
    exact (LiZhongQC.s30a_p_smul hp (Γ.zpow_mem hAΓ n) z).symm

end LowDimensionalTopology.Geometry.Surfaces
