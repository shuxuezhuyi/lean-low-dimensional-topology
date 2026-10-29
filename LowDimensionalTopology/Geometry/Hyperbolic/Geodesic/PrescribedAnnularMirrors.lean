module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.AnnularThreeCircleSeed
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.NativeLineDisjointOfInversiveProduct
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- Three prescribed native mirror distances, retaining strict annular placement. -/
theorem exists_prescribed_annular_three_mirrors (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ E r x : ℝ, ∃ hE : 0 < E, ∃ hr : 0 < r,
      1 < E ∧ 1 + r < x ∧ x + r < E ∧
      let C1 := HalfPlaneLine.circle 0 1 (by norm_num)
      let C2 := HalfPlaneLine.circle 0 E hE
      let C3 := HalfPlaneLine.circle x r hr
      C1.HDisjoint C2 ∧ C1.HDisjoint C3 ∧ C2.HDisjoint C3 ∧
      C1.lineDist C2 = a ∧ C1.lineDist C3 = b ∧ C2.lineDist C3 = c := by
  have hwidth (L M : HalfPlaneLine) (u : ℝ) (hu : 0 < u)
      (hp : |L.normalPairing M| = Real.cosh u) :
      L.HDisjoint M ∧ L.lineDist M = u := by
    have hd : L.HDisjoint M :=
      L.hDisjoint_of_one_lt_abs_normalPairing M (by
        rw [hp]
        exact Real.one_lt_cosh.mpr hu.ne')
    refine ⟨hd, ?_⟩
    apply Real.cosh_strictMonoOn.injOn (L.lineDist_nonneg M) hu.le
    calc
      Real.cosh (L.lineDist M) =
          Inversive.inversiveProduct
            L.extendedCircle.realModel M.extendedCircle.realModel :=
        (halfPlane_inversiveProduct_eq_cosh_lineDist L M hd).symm
      _ = |L.normalPairing M| := halfPlane_inversiveProduct_eq_normal_product L M
      _ = Real.cosh u := hp
  obtain ⟨E, r, x, hE, hr, hE1, hinner, houter, hp12, hp13, hp23⟩ :=
    exists_annular_three_circle_seed a b c ha hb hc
  let C1 := HalfPlaneLine.circle 0 1 (by norm_num)
  let C2 := HalfPlaneLine.circle 0 E hE
  let C3 := HalfPlaneLine.circle x r hr
  have h12 := hwidth C1 C2 a ha (by
    rw [show C1.normalPairing C2 = Real.cosh a from hp12,
      abs_of_pos (Real.cosh_pos a)])
  have h13 := hwidth C1 C3 b hb (by
    rw [show C1.normalPairing C3 = -Real.cosh b from hp13,
      abs_neg, abs_of_pos (Real.cosh_pos b)])
  have h23 := hwidth C2 C3 c hc (by
    rw [show C2.normalPairing C3 = Real.cosh c from hp23,
      abs_of_pos (Real.cosh_pos c)])
  exact ⟨E, r, x, hE, hr, hE1, hinner, houter,
    h12.1, h13.1, h23.1, h12.2, h13.2, h23.2⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
