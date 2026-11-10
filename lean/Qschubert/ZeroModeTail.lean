import Qschubert.ZeroModePow
import Qschubert.ZeroModeWeight

/-!
# Preparations for the zero-mode multiplier identity

Stage Z of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`).

* `tail_exp_integrable`: a kernel with the tail `TailB g B` satisfies `∫ |g(r)| e^{|r|/2} dr < ∞` (sum over the shells
  `n ≤ |r| < n + 1`; the tail `e^{-T/2} (1 + T)^{-3/2}` gives the convergent series `Σ (1 + n)^{-3/2}`).
* `exists_psiF_bound`: a test function vanishes outside some set `{ψ ≤ a}`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane ContDiff Real

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- The shells `n ≤ |r| < n + 1` of the line. -/
def lineShell (n : ℕ) : Set ℝ := {r | ⌊|r|⌋₊ = n}

lemma measurableSet_lineShell (n : ℕ) : MeasurableSet (lineShell n) :=
  (Nat.measurable_floor.comp continuous_abs.measurable) (measurableSet_singleton n)

lemma tF_mul_exp (n : ℕ) :
    Real.exp (((n : ℝ) + 1) / 2) * tF n = Real.exp (1 / 2) / (1 + (n : ℝ)) ^ (3 / 2 : ℝ) := by
  unfold tF
  have h1 : (0 : ℝ) < 1 + n := by positivity
  have e : (1 + (n : ℝ)) * Real.sqrt (1 + n) = (1 + (n : ℝ)) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' h1.le (by norm_num)]
    norm_num
  rw [e, ← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring

lemma summable_shell_series (B : ℝ) :
    Summable fun n : ℕ => |B| * (Real.exp (1 / 2) / (1 + (n : ℝ)) ^ (3 / 2 : ℝ)) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
  have h2 : Summable fun n : ℕ => |B| * Real.exp (1 / 2) * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) := h.mul_left _
  refine h2.congr fun n => ?_
  rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), add_comm (n : ℝ) 1]
  ring

/-- **Exponential integrability from the tail.** -/
theorem tail_exp_integrable {g : ℝ → ℝ} {B : ℝ} (hg : Integrable g) (ht : TailB g B) :
    Integrable fun r => |g r| * Real.exp (|r| / 2) := by
  have hcont : Continuous fun r : ℝ => Real.exp (|r| / 2) := by fun_prop
  have hmeas : AEStronglyMeasurable (fun r => |g r| * Real.exp (|r| / 2)) volume :=
    hg.abs.1.mul hcont.aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun r => by positivity)]
  have hcover : (⋃ n, lineShell n) = univ := by
    ext r
    simp [lineShell]
  have hdisj : Pairwise (Function.onFun Disjoint lineShell) := fun i j hij => by
    rw [Function.onFun, Set.disjoint_left]
    intro r hi hj
    exact hij (hi.symm.trans hj)
  rw [← setLIntegral_univ, ← hcover, lintegral_iUnion measurableSet_lineShell hdisj]
  have hterm : ∀ n : ℕ, ∫⁻ r in lineShell n, ENNReal.ofReal (|g r| * Real.exp (|r| / 2))
      ≤ ENNReal.ofReal (|B| * (Real.exp (1 / 2) / (1 + (n : ℝ)) ^ (3 / 2 : ℝ))) := by
    intro n
    have hsub : lineShell n ⊆ {r : ℝ | (n : ℝ) ≤ |r|} := fun r hr =>
      ((Nat.floor_eq_iff (abs_nonneg r)).1 hr).1
    calc ∫⁻ r in lineShell n, ENNReal.ofReal (|g r| * Real.exp (|r| / 2))
        ≤ ∫⁻ r in lineShell n, ENNReal.ofReal (Real.exp (((n : ℝ) + 1) / 2)) * ENNReal.ofReal (|g r|) := by
          refine setLIntegral_mono' (measurableSet_lineShell n) fun r hr => ?_
          have h2 := ((Nat.floor_eq_iff (abs_nonneg r)).1 hr).2
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (abs_nonneg _))
      _ = ENNReal.ofReal (Real.exp (((n : ℝ) + 1) / 2)) * ∫⁻ r in lineShell n, ENNReal.ofReal (|g r|) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (((n : ℝ) + 1) / 2))
            * ∫⁻ r in {r : ℝ | (n : ℝ) ≤ |r|}, ENNReal.ofReal (|g r|) := by
          gcongr
      _ = ENNReal.ofReal (Real.exp (((n : ℝ) + 1) / 2))
            * ENNReal.ofReal (∫ r in {r : ℝ | (n : ℝ) ≤ |r|}, |g r|) := by
          rw [ofReal_integral_eq_lintegral_ofReal hg.abs.integrableOn (Eventually.of_forall fun r => abs_nonneg _)]
      _ ≤ ENNReal.ofReal (Real.exp (((n : ℝ) + 1) / 2)) * ENNReal.ofReal (|B| * tF n) := by
          gcongr
          exact (ht n (Nat.cast_nonneg n)).trans
            (mul_le_mul_of_nonneg_right (le_abs_self B) (tF_nonneg (Nat.cast_nonneg n)))
      _ = ENNReal.ofReal (|B| * (Real.exp (1 / 2) / (1 + (n : ℝ)) ^ (3 / 2 : ℝ))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_left_comm, tF_mul_exp]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (summable_shell_series B)]
  exact ENNReal.ofReal_lt_top

/-- `ψ = log cosh d(i, ·)` in terms of `gH`. -/
lemma psiF_eq_log_gH {z : ℂ} : psiF z = Real.log (gH z) := by
  have hg : hF z = (gH z)⁻¹ := by
    rw [hF, gH, mul_inv, inv_inv]
    ring
  rw [psiF, hg, Real.log_inv, neg_neg]

/-- A test function vanishes outside some set `{ψ ≤ a}`, `a ≥ 0`. -/
theorem exists_psiF_bound (h : testFn) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ z : UpperHalfPlane, (h : ℂ → ℂ) z ≠ 0 → psiF (z : ℂ) ≤ a := by
  have hc : ContinuousOn gH (tsupport (h : ℂ → ℂ)) := fun w hw =>
    (contDiffAt_gH (h.2.inside hw).ne').continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (h.2.compact.image_of_continuousOn hc).bddAbove
  refine ⟨Real.log (max M 1), Real.log_nonneg (le_max_right _ _), fun z hz => ?_⟩
  have hmem : (z : ℂ) ∈ tsupport (h : ℂ → ℂ) := subset_tsupport _ hz
  have h1 : gH (z : ℂ) ≤ M := hM ⟨z, hmem, rfl⟩
  rw [psiF_eq_log_gH]
  exact Real.log_le_log (gH_pos z.im_pos) (h1.trans (le_max_left _ _))

end Qschubert
