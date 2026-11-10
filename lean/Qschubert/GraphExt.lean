import Qschubert.VAdjPath
import Qschubert.EllipticId
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# `Δ(s)` on the closure of `-Δ` on test functions, and Duhamel there

On test functions `X²F = y²∂ₓ²F` (`xxTest_eq`), `(Y² - Y)F = y²∂_y²F` (`yyTest_eq`), and by the
elliptic estimate `‖X²F‖, ‖(Y² - Y)F‖ ≤ ‖F‖ + ‖ΔF‖` (`norm_xxTest_le`, `norm_yyTest_le`). So both,
and `Δ(s) = e^{-2s}X² + (Y² - Y)`, are bounded in the graph norm of `negLap` and extend to the
closure of its graph (`psiX`, `psiY`, `lapTbar`). Both sides of the backward Duhamel formula are
continuous in the graph norm, so it holds on that closure (`dispVadj_sub_eq_integral_closure`):
for `u` in the domain of the closure `Ā` of `-Δ` on test functions,
`V(t)* u - u = -(iħ/2) ∫₀ᵗ V(s)* Δ(s) u ds`.
This domain equals `Dom(negLapH)` exactly when `-Δ` is essentially self-adjoint on test
functions (not proved here; R66).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Physicslib4.Spectral.Unbounded
open scoped ContDiff ComplexConjugate InnerProductSpace

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- `X²F = y²∂ₓ²F`. -/
lemma xxTest_eq (F : testFn) : xxTest F = vfTest 1 (vfTest 1 F) := by
  apply Subtype.ext; funext w
  show xxFun F w = ((vfTest 1 (vfTest 1 F) : testFn) : ℂ → ℂ) w
  rw [vf_vf_apply, xxFun]
  simp only [Complex.one_im, Complex.ofReal_zero, zero_mul, zero_add]
  ring

/-- `(Y² - Y)F = y²∂_y²F`. -/
lemma yyTest_eq (F : testFn) :
    yyTest F = vfTest Complex.I (vfTest Complex.I F) - vfTest Complex.I F := by
  apply Subtype.ext; funext w
  show yyFun F w = ((vfTest Complex.I (vfTest Complex.I F) : testFn) : ℂ → ℂ) w
    - ((vfTest Complex.I F : testFn) : ℂ → ℂ) w
  rw [vf_vf_apply, vfTest_coe, yyFun]
  simp only [Complex.I_im, Complex.ofReal_one, one_mul]
  ring

lemma sq_le_of_elliptic {a b c f L : ℝ} (ha : 0 ≤ a) (hf : 0 ≤ f) (hL : 0 ≤ L) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (h : a ^ 2 + b ^ 2 + 2 * c ^ 2 ≤ L ^ 2 + 2 * (f * L)) : a ≤ f + L ∧ b ≤ f + L := by
  have hs : 0 ≤ f + L := add_nonneg hf hL
  have h2 : L ^ 2 + 2 * (f * L) ≤ (f + L) ^ 2 := by nlinarith
  constructor
  · exact (pow_le_pow_iff_left₀ ha hs two_ne_zero).1 (by nlinarith)
  · exact (pow_le_pow_iff_left₀ hb hs two_ne_zero).1 (by nlinarith)

lemma norm_xxTest_le (F : testFn) : ‖toL2 (xxTest F)‖ ≤ ‖toL2 F‖ + ‖toL2 (lapTest F)‖ := by
  have h := elliptic_estimate F
  rw [xxTest_eq]
  exact (sq_le_of_elliptic (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) h).1

lemma norm_yyTest_le (F : testFn) : ‖toL2 (yyTest F)‖ ≤ ‖toL2 F‖ + ‖toL2 (lapTest F)‖ := by
  have h := elliptic_estimate F
  rw [yyTest_eq, map_sub]
  exact (sq_le_of_elliptic (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) h).2

lemma xxTest_add (F G : testFn) : xxTest (F + G) = xxTest F + xxTest G := by
  rw [xxTest_eq, xxTest_eq, xxTest_eq, map_add, map_add]

lemma xxTest_smul (c : ℂ) (F : testFn) : xxTest (c • F) = c • xxTest F := by
  rw [xxTest_eq, xxTest_eq, map_smul, map_smul]

lemma yyTest_add (F G : testFn) : yyTest (F + G) = yyTest F + yyTest G := by
  rw [yyTest_eq, yyTest_eq, yyTest_eq, map_add, map_add]
  abel

lemma yyTest_smul (c : ℂ) (F : testFn) : yyTest (c • F) = c • yyTest F := by
  rw [yyTest_eq, yyTest_eq, map_smul, map_smul, smul_sub]

/-! ### The graph of `negLap`, its closure, and the extended `X²`, `Y² - Y`, `Δ(s)` -/

lemma mem_dom_of_graph (p : negLap.graph) : (p : L2H × L2H).1 ∈ negLap.domain :=
  LinearPMap.mem_domain_of_mem_graph (show ((p : L2H × L2H).1, (p : L2H × L2H).2) ∈ negLap.graph from p.2)

/-- The test function of a graph point. -/
noncomputable def testOf (p : negLap.graph) : testFn :=
  toL2Equiv.symm ⟨(p : L2H × L2H).1, mem_dom_of_graph p⟩

lemma toL2Equiv_testOf (p : negLap.graph) :
    toL2Equiv (testOf p) = ⟨(p : L2H × L2H).1, mem_dom_of_graph p⟩ :=
  toL2Equiv.apply_symm_apply _

lemma toL2_testOf (p : negLap.graph) : toL2 (testOf p) = (p : L2H × L2H).1 := by
  rw [← coe_toL2Equiv, toL2Equiv_testOf]

lemma neg_toL2_lapTest_testOf (p : negLap.graph) :
    -toL2 (lapTest (testOf p)) = (p : L2H × L2H).2 := by
  rw [← negLap_toL2Equiv, toL2Equiv_testOf]
  exact ((LinearPMap.image_iff (mem_dom_of_graph p)).2
    (show ((p : L2H × L2H).1, (p : L2H × L2H).2) ∈ negLap.graph from p.2)).symm

lemma norm_lapTest_testOf (p : negLap.graph) :
    ‖toL2 (lapTest (testOf p))‖ = ‖(p : L2H × L2H).2‖ := by
  rw [← neg_toL2_lapTest_testOf, norm_neg]

lemma testOf_add (p q : negLap.graph) : testOf (p + q) = testOf p + testOf q := by
  unfold testOf
  rw [← map_add]
  rfl

lemma testOf_smul (c : ℂ) (p : negLap.graph) : testOf (c • p) = c • testOf p := by
  unfold testOf
  rw [← map_smul]
  rfl

lemma norm_fst_snd_le (p : negLap.graph) :
    ‖(p : L2H × L2H).1‖ + ‖(p : L2H × L2H).2‖ ≤ 2 * ‖p‖ := by
  have h1 : ‖(p : L2H × L2H).1‖ ≤ ‖p‖ := norm_fst_le _
  have h2 : ‖(p : L2H × L2H).2‖ ≤ ‖p‖ := norm_snd_le _
  linarith

/-- `X²` on the graph. -/
noncomputable def psiXLin : negLap.graph →ₗ[ℂ] L2H where
  toFun p := toL2 (xxTest (testOf p))
  map_add' p q := by rw [testOf_add, xxTest_add, map_add]
  map_smul' c p := by rw [testOf_smul, xxTest_smul, map_smul]; rfl

/-- `Y² - Y` on the graph. -/
noncomputable def psiYLin : negLap.graph →ₗ[ℂ] L2H where
  toFun p := toL2 (yyTest (testOf p))
  map_add' p q := by rw [testOf_add, yyTest_add, map_add]
  map_smul' c p := by rw [testOf_smul, yyTest_smul, map_smul]; rfl

lemma norm_psiXLin_le (p : negLap.graph) : ‖psiXLin p‖ ≤ 2 * ‖p‖ := by
  have h := norm_xxTest_le (testOf p)
  rw [toL2_testOf, norm_lapTest_testOf] at h
  exact h.trans (norm_fst_snd_le p)

lemma norm_psiYLin_le (p : negLap.graph) : ‖psiYLin p‖ ≤ 2 * ‖p‖ := by
  have h := norm_yyTest_le (testOf p)
  rw [toL2_testOf, norm_lapTest_testOf] at h
  exact h.trans (norm_fst_snd_le p)

/-- The closure of the graph of `negLap`. -/
noncomputable def graphBar : Submodule ℂ (L2H × L2H) := negLap.graph.topologicalClosure

/-- The inclusion of the graph into its closure. -/
noncomputable def graphIncl : negLap.graph →L[ℂ] graphBar :=
  ⟨Submodule.inclusion negLap.graph.le_topologicalClosure,
    continuous_inclusion negLap.graph.le_topologicalClosure⟩

lemma denseRange_graphIncl : DenseRange graphIncl := by
  show DenseRange (Set.inclusion (negLap.graph.le_topologicalClosure))
  rw [denseRange_inclusion_iff]
  show (negLap.graph.topologicalClosure : Set (L2H × L2H)) ⊆ closure (negLap.graph : Set (L2H × L2H))
  rw [Submodule.topologicalClosure_coe]
  exact negLap.graph.le_topologicalClosure

lemma norm_graphIncl (p : negLap.graph) : ‖graphIncl p‖ = ‖p‖ := rfl

/-- `X²` on the closure. -/
noncomputable def psiX : graphBar →L[ℂ] L2H := psiXLin.extendOfNorm graphIncl
/-- `Y² - Y` on the closure. -/
noncomputable def psiY : graphBar →L[ℂ] L2H := psiYLin.extendOfNorm graphIncl

lemma psiX_incl (p : negLap.graph) : psiX (graphIncl p) = psiXLin p :=
  LinearMap.extendOfNorm_eq denseRange_graphIncl ⟨2, fun q => by have h := norm_psiXLin_le q; exact h⟩ p

lemma psiY_incl (p : negLap.graph) : psiY (graphIncl p) = psiYLin p :=
  LinearMap.extendOfNorm_eq denseRange_graphIncl ⟨2, fun q => by have h := norm_psiYLin_le q; exact h⟩ p

/-- `Δ(s) = e^{-2s}X² + (Y² - Y)` on the closure of the graph. -/
noncomputable def lapTbar (s : ℝ) (p : graphBar) : L2H := ((Real.exp (-2 * s) : ℝ) : ℂ) • psiX p + psiY p

lemma lapTbar_incl (s : ℝ) (p : negLap.graph) : lapTbar s (graphIncl p) = lapTL2 s (testOf p) := by
  rw [lapTbar, psiX_incl, psiY_incl, lapTL2_eq]
  rfl

lemma continuous_dispVadj_apply (hb t : ℝ) : Continuous (dispVadj hb t) :=
  continuous_iff_continuousAt.2 fun x => tendsto_dispVadj tendsto_const_nhds (continuous_id.tendsto x)

lemma continuous_lapTbar_uncurry : Continuous fun q : graphBar × ℝ => lapTbar q.2 q.1 := by
  unfold lapTbar
  have hc : Continuous fun q : graphBar × ℝ => (((Real.exp (-2 * q.2)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_snd))
  exact (hc.smul (psiX.continuous.comp continuous_fst)).add (psiY.continuous.comp continuous_fst)

/-- **Backward Duhamel on the closure of the graph.** -/
theorem dispVadj_sub_eq_integral_bar {hb : ℝ} (hb0 : hb ≠ 0) (t : ℝ) (p : graphBar) :
    dispVadj hb t (p : L2H × L2H).1 - (p : L2H × L2H).1
      = -(Complex.I * (hb : ℂ) / 2) • ∫ s in (0 : ℝ)..t, dispVadj hb s (lapTbar s p) := by
  have hfst : Continuous fun p : graphBar => (p : L2H × L2H).1 := continuous_fst.comp continuous_subtype_val
  have hjoint : Continuous fun q : graphBar × ℝ => dispVadj hb q.2 (lapTbar q.2 q.1) :=
    continuous_iff_continuousAt.2 fun q =>
      tendsto_dispVadj (continuous_snd.tendsto q) (continuous_lapTbar_uncurry.tendsto q)
  have hR : Continuous fun p : graphBar => ∫ s in (0 : ℝ)..t, dispVadj hb s (lapTbar s p) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun p s => dispVadj hb s (lapTbar s p))
      hjoint 0 t
  refine DenseRange.induction_on denseRange_graphIncl p ?_ ?_
  · exact isClosed_eq (((continuous_dispVadj_apply hb t).comp hfst).sub hfst)
      (hR.const_smul (-(Complex.I * (hb : ℂ) / 2)))
  · intro q
    have h := dispVadj_sub_eq_integral hb0 (testOf q) t
    rw [toL2_testOf] at h
    simp only [lapTbar_incl]
    exact h

/-- The closure `Ā` of `-Δ` on test functions; its graph is `graphBar`. -/
lemma negLap_isClosable : negLap.IsClosable := isClosable_of_isSymmetric negLap_hasDenseDomain negLap_isSymmetric

lemma graphBar_eq : graphBar = negLap.closure.graph :=
  LinearPMap.IsClosable.graph_closure_eq_closure_graph negLap_isClosable

/-- The graph point of `u ∈ Dom(Ā)`. -/
noncomputable def barPt (u : negLap.closure.domain) : graphBar :=
  ⟨((u : L2H), negLap.closure u), by rw [graphBar_eq]; exact LinearPMap.mem_graph _ u⟩

/-- **Backward Duhamel on `Dom(Ā)`**: `V(t)* u - u = -(iħ/2) ∫₀ᵗ V(s)* Δ(s) u ds`, with
`Δ(s)u := lapTbar s (u, Āu)`. -/
theorem dispVadj_sub_eq_integral_closure {hb : ℝ} (hb0 : hb ≠ 0) (t : ℝ) (u : negLap.closure.domain) :
    dispVadj hb t (u : L2H) - (u : L2H)
      = -(Complex.I * (hb : ℂ) / 2) • ∫ s in (0 : ℝ)..t, dispVadj hb s (lapTbar s (barPt u)) :=
  dispVadj_sub_eq_integral_bar hb0 t (barPt u)

end Qschubert
