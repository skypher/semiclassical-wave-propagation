import Qschubert.PGLAction
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.Polynomial.Roots

/-!
# Every Fuchsian group has a fundamental domain

Spine stage S3 (`lean/BLUEPRINT.md`). For `g ∈ PGL(2, ℝ)`, `g ≠ 1`, the fixed set of `g` in `ℍ` is
null for `dx dy / y²` (at most two points if `det g > 0`; empty, a circle or a vertical line if
`det g < 0`). For `Γ ≤ PGL(2, ℝ)` acting properly discontinuously, the points of `ℍ` that are least
in their orbit for the lexicographic order of `(d(i, z), Re z, Im z)` form a measurable fundamental
domain: each orbit has a least point (finitely many orbit points lie in each ball), and two
translates meet only in fixed sets.
-/

namespace Qschubert

open UpperHalfPlane MeasureTheory Metric Complex
open scoped MatrixGroups ENNReal Pointwise

/-- A set of `ℍ` whose image in `ℂ` lies in a Lebesgue-null set is null for `dx dy / y²`. -/
lemma volume_preimage_coe_null {T : Set ℂ} (hT : volume T = 0) :
    volume ((UpperHalfPlane.coe) ⁻¹' T : Set ℍ) = 0 := by
  rw [volume_def]
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [measurableEmbedding_coe.comap_apply]
  exact measure_mono_null (Set.image_preimage_subset _ _) hT

/-- A vertical line in `ℂ` is Lebesgue-null. -/
lemma volume_re_eq (x₀ : ℝ) : volume {w : ℂ | w.re = x₀} = 0 := by
  have h : {w : ℂ | w.re = x₀} = measurableEquivRealProd ⁻¹' ({x₀} ×ˢ Set.univ) := by
    ext w; simp [measurableEquivRealProd_apply]
  rw [h, volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_singleton x₀ |>.prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

lemma scalar_mem_center_of {g : GL (Fin 2) ℝ} (h10 : g 1 0 = 0) (h01 : g 0 1 = 0)
    (h11 : g 1 1 = g 0 0) : g ∈ Subgroup.center (GL (Fin 2) ℝ) := by
  have hdet0 : g.det.val ≠ 0 := g.det.ne_zero
  have ha : g 0 0 ≠ 0 := by
    intro ha
    apply hdet0
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, ha, h10]; ring
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.mk0 (g 0 0) ha, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h10, h01, h11]

/-- For `g ∈ GL(2, ℝ)` outside the center (that is, `g ≠ 1` in `PGL(2, ℝ)`), the fixed set of `g`
in `ℍ` is null. -/
theorem volume_fixedPoints (g : GL (Fin 2) ℝ) (hg : g ∉ Subgroup.center (GL (Fin 2) ℝ)) :
    volume {z : ℍ | g • z = z} = 0 := by
  have hdet : g.det.val = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hdet0 : g.det.val ≠ 0 := g.det.ne_zero
  by_cases hpos : 0 < g.det.val
  · set p : Polynomial ℂ := Polynomial.C ((g 1 0 : ℝ) : ℂ) * Polynomial.X ^ 2
      + Polynomial.C (((g 1 1 : ℝ) : ℂ) - ((g 0 0 : ℝ) : ℂ)) * Polynomial.X
      - Polynomial.C ((g 0 1 : ℝ) : ℂ) with hp_def
    have hp : p ≠ 0 := by
      intro hp0
      apply hg
      have h2 := congrArg (Polynomial.coeff · 2) hp0
      have h1 := congrArg (Polynomial.coeff · 1) hp0
      have h0 := congrArg (Polynomial.coeff · 0) hp0
      simp [p, Polynomial.coeff_X, Polynomial.coeff_C] at h2 h1 h0
      exact scalar_mem_center_of h2 h0 (by exact_mod_cast sub_eq_zero.1 h1)
    refine measure_mono_null ?_ (volume_preimage_coe_null (T := (p.roots.toFinset : Set ℂ))
      (p.roots.toFinset.finite_toSet.measure_zero _))
    intro z hz
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp,
      Polynomial.IsRoot.def]
    have h := congrArg UpperHalfPlane.coe (show g • z = z from hz)
    rw [coe_smul_of_det_pos hpos, div_eq_iff (denom_ne_zero g z)] at h
    simp only [p, num, denom, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h ⊢
    linear_combination -h
  · have hσ : ∀ w : ℂ, σ g w = (starRingEnd ℂ) w := fun w => by
      rw [σ, ite_eq_right hpos]; rfl
    have eqs : ∀ z : ℍ, g • z = z → (g 0 0 + g 1 1) * z.im = 0 ∧
        g 1 0 * (z.re ^ 2 + z.im ^ 2) + g 1 1 * z.re = g 0 0 * z.re + g 0 1 := by
      intro z hz
      have h := congrArg UpperHalfPlane.coe hz
      rw [UpperHalfPlane.coe_smul, hσ] at h
      have h' := congrArg (starRingEnd ℂ) h
      rw [Complex.conj_conj, div_eq_iff (denom_ne_zero g z)] at h'
      have hre := congrArg Complex.re h'
      have him := congrArg Complex.im h'
      simp [num, denom, Complex.mul_re, Complex.mul_im] at hre him
      constructor
      · linear_combination him
      · linear_combination -hre
    by_cases had : g 0 0 + g 1 1 = 0
    · have hd : g 1 1 = -g 0 0 := by linarith
      by_cases hc : g 1 0 = 0
      · have ha : g 0 0 ≠ 0 := by
          intro ha; apply hdet0; rw [hdet, hc, hd, ha]; ring
        refine measure_mono_null ?_ (volume_preimage_coe_null (volume_re_eq (-(g 0 1) / (2 * g 0 0))))
        intro z hz
        obtain ⟨_, h2⟩ := eqs z hz
        rw [hc, hd] at h2
        show (z : ℂ).re = _
        rw [UpperHalfPlane.coe_re]
        field_simp
        linarith
      · refine measure_mono_null ?_ (volume_preimage_coe_null (Measure.addHaar_sphere volume
          (((g 0 0 / g 1 0 : ℝ)) : ℂ) (Real.sqrt (g 0 1 / g 1 0 + (g 0 0 / g 1 0) ^ 2))))
        intro z hz
        obtain ⟨_, h2⟩ := eqs z hz
        rw [hd] at h2
        show (z : ℂ) ∈ sphere _ _
        rw [mem_sphere, Complex.dist_eq_re_im]
        congr 1
        simp only [Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        field_simp
        linear_combination (g 1 0) * h2
    · refine measure_mono_null ?_ (measure_empty (μ := (volume : Measure ℍ)))
      intro z hz
      obtain ⟨h1, _⟩ := eqs z hz
      exact had ((mul_eq_zero.1 h1).resolve_right z.im_ne_zero)

/-- For `g ≠ 1` in `PGL(2, ℝ)`, the fixed set of `g` in `ℍ` is null. -/
theorem volume_fixedPoints_pgl {g : PGL(2, ℝ)} (hg : g ≠ 1) : volume {z : ℍ | g • z = z} = 0 := by
  obtain ⟨M, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  simp only [pglMk_smul]
  exact volume_fixedPoints M fun h => hg (Matrix.ProjGenLinGroup.mk_eq_one.2 h)

variable (Γ : Subgroup PGL(2, ℝ))

/-- A subgroup of `PGL(2, ℝ)` acting properly discontinuously on `ℍ` is countable. -/
theorem countable_of_properlyDiscontinuous [ProperlyDiscontinuousSMul Γ ℍ] : Countable Γ := by
  have hfin : ∀ n : ℕ, Set.Finite {γ : Γ | ((γ • ·) '' closedBall UpperHalfPlane.I n ∩ closedBall UpperHalfPlane.I n).Nonempty} :=
    fun n => ProperlyDiscontinuousSMul.finite_disjoint_inter_image
      (isCompact_closedBall UpperHalfPlane.I n) (isCompact_closedBall UpperHalfPlane.I n)
  have hcov : (Set.univ : Set Γ) ⊆
      ⋃ n : ℕ, {γ : Γ | ((γ • ·) '' closedBall UpperHalfPlane.I n ∩ closedBall UpperHalfPlane.I n).Nonempty} := by
    intro γ _
    obtain ⟨n, hn⟩ := exists_nat_ge (max (dist (γ • UpperHalfPlane.I) UpperHalfPlane.I) 0)
    refine Set.mem_iUnion.2 ⟨n, γ • UpperHalfPlane.I, ⟨UpperHalfPlane.I, mem_closedBall_self (Nat.cast_nonneg n), rfl⟩, ?_⟩
    exact mem_closedBall.2 ((le_max_left _ _).trans hn)
  exact Set.countable_univ_iff.1 ((Set.countable_iUnion fun n => (hfin n).countable).mono hcov)

/-- The key `(d(z, i), Re z, Im z)`, ordered lexicographically. -/
noncomputable def fdKey (z : ℍ) : ℝ ×ₗ (ℝ ×ₗ ℝ) := toLex (dist z UpperHalfPlane.I, toLex (z.re, z.im))

lemma fdKey_injective : Function.Injective fdKey := by
  intro z w h
  simp only [fdKey, toLex_inj, Prod.mk.injEq] at h
  exact UpperHalfPlane.ext (Complex.ext h.2.1 h.2.2)

/-- The points of `ℍ` least in their `Γ`-orbit for `fdKey`. -/
def fdSet : Set ℍ := {z | ∀ γ : Γ, fdKey z ≤ fdKey (γ • z)}

lemma measurableSet_fdKey_le (γ : Γ) : MeasurableSet {z : ℍ | fdKey z ≤ fdKey (γ • z)} := by
  have hc : Continuous fun z : ℍ => γ • z := continuous_const_smul γ
  have e : {z : ℍ | fdKey z ≤ fdKey (γ • z)} =
      {z | dist z UpperHalfPlane.I < dist (γ • z) UpperHalfPlane.I} ∪ ({z | dist z UpperHalfPlane.I = dist (γ • z) UpperHalfPlane.I} ∩
        ({z | z.re < (γ • z).re} ∪ ({z | z.re = (γ • z).re} ∩ {z | z.im ≤ (γ • z).im}))) := by
    ext z
    simp only [fdKey, Prod.Lex.toLex_le_toLex]
    exact Iff.rfl
  have hd : Measurable fun z : ℍ => dist z UpperHalfPlane.I := (continuous_id.dist continuous_const).measurable
  have hd' : Measurable fun z : ℍ => dist (γ • z) UpperHalfPlane.I := (hc.dist continuous_const).measurable
  have hre : Measurable fun z : ℍ => z.re := continuous_re.measurable
  have hre' : Measurable fun z : ℍ => (γ • z).re := (continuous_re.comp hc).measurable
  have him : Measurable fun z : ℍ => z.im := continuous_im.measurable
  have him' : Measurable fun z : ℍ => (γ • z).im := (continuous_im.comp hc).measurable
  rw [e]
  exact (measurableSet_lt hd hd').union ((measurableSet_eq_fun hd hd').inter
    ((measurableSet_lt hre hre').union ((measurableSet_eq_fun hre hre').inter
      (measurableSet_le him him'))))

lemma measurableSet_fdSet [Countable Γ] : MeasurableSet (fdSet Γ) := by
  have e : fdSet Γ = ⋂ γ : Γ, {z : ℍ | fdKey z ≤ fdKey (γ • z)} := by
    ext z; simp [fdSet]
  rw [e]
  exact MeasurableSet.iInter fun γ => measurableSet_fdKey_le Γ γ

/-- Every orbit meets `fdSet`. -/
lemma exists_smul_mem_fdSet [ProperlyDiscontinuousSMul Γ ℍ] (x : ℍ) :
    ∃ γ : Γ, γ • x ∈ fdSet Γ := by
  set S : Set Γ := {γ | ((γ • ·) '' {x} ∩ closedBall UpperHalfPlane.I (dist x UpperHalfPlane.I)).Nonempty}
  have hS : S.Finite := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    isCompact_singleton (isCompact_closedBall UpperHalfPlane.I _)
  have hmem : ∀ γ : Γ, γ ∈ S ↔ dist (γ • x) UpperHalfPlane.I ≤ dist x UpperHalfPlane.I := by
    intro γ
    simp only [S, Set.mem_ofPred_eq, Set.image_singleton, Set.singleton_inter_nonempty,
      mem_closedBall]
  have h1 : (1 : Γ) ∈ S := (hmem 1).2 (by simp)
  obtain ⟨γ₀, hγ₀, hmin⟩ := Set.exists_min_image S (fun γ => fdKey (γ • x)) hS ⟨1, h1⟩
  refine ⟨γ₀, fun δ => ?_⟩
  rw [smul_smul]
  by_cases h : δ * γ₀ ∈ S
  · exact hmin _ h
  · have hlt : dist (γ₀ • x) UpperHalfPlane.I < dist ((δ * γ₀) • x) UpperHalfPlane.I :=
      lt_of_le_of_lt ((hmem γ₀).1 hγ₀) (not_le.1 fun h' => h ((hmem _).2 h'))
    simp only [fdKey]
    exact Prod.Lex.toLex_le_toLex.2 (Or.inl hlt)

/-- Two translates of `fdSet` meet only in a fixed set. -/
lemma smul_fdSet_inter_subset (g : Γ) :
    g • fdSet Γ ∩ fdSet Γ ⊆ {z : ℍ | (g : PGL(2, ℝ)) • z = z} := by
  rintro z ⟨hz1, hz2⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hz1
  have h1 : fdKey z ≤ fdKey (g⁻¹ • z) := hz2 g⁻¹
  have h2 : fdKey (g⁻¹ • z) ≤ fdKey z := by simpa using hz1 g
  have h : z = g⁻¹ • z := fdKey_injective (le_antisymm h1 h2)
  show (g : PGL(2, ℝ)) • z = z
  rw [← Subgroup.smul_def]
  calc g • z = g • (g⁻¹ • z) := by rw [← h]
    _ = z := smul_inv_smul g z

/-- Every subgroup of `PGL(2, ℝ)` acting properly discontinuously on `ℍ` (every Fuchsian group)
has a measurable fundamental domain. -/
theorem isFundamentalDomain_fdSet [ProperlyDiscontinuousSMul Γ ℍ] :
    IsFundamentalDomain Γ (fdSet Γ) volume := by
  have := countable_of_properlyDiscontinuous Γ
  refine IsFundamentalDomain.mk'' (measurableSet_fdSet Γ).nullMeasurableSet
    (Filter.Eventually.of_forall (exists_smul_mem_fdSet Γ)) ?_ ?_
  · intro g hg
    refine measure_mono_null (smul_fdSet_inter_subset Γ g) (volume_fixedPoints_pgl ?_)
    exact fun h => hg (Subtype.ext h)
  · intro g
    exact (measurePreserving_smul g volume).quasiMeasurePreserving

theorem hasFundamentalDomain [ProperlyDiscontinuousSMul Γ ℍ] : HasFundamentalDomain Γ ℍ volume :=
  ⟨⟨fdSet Γ, isFundamentalDomain_fdSet Γ⟩⟩

end Qschubert
