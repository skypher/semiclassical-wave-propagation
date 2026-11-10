import Qschubert.KLM2b
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Local holomorphic extensions give uniform derivative bounds; the analytic square of the distance

`bounds_of_local`: if on a compact set the real function `Φ` is locally the real part of a holomorphic function, then `|Φ^{(k)}| ≤ A k! R^{-k}` there.
`exists_S0`: an analytic germ `S₀` at `0` with `S₀(log cosh r) = r²`; it is the inverse of `s ↦ log cosh √s`, which is analytic at `0` with derivative `1/2`.
-/

namespace Qschubert

open Complex Filter Topology Set Metric
open scoped ContDiff Nat

/-- The real derivatives are the real parts of the complex ones. -/
lemma iter_re {Φ : ℝ → ℝ} {F : ℂ → ℂ} {x : ℝ} (hF : AnalyticAt ℂ F (x : ℂ)) (h : ∀ᶠ t in 𝓝 x, Φ t = (F (t : ℂ)).re) (k : ℕ) :
    ∀ᶠ t in 𝓝 x, iteratedDeriv k Φ t = (iteratedDeriv k F (t : ℂ)).re ∧ AnalyticAt ℂ (iteratedDeriv k F) (t : ℂ) := by
  have han : ∀ᶠ t : ℝ in 𝓝 x, AnalyticAt ℂ F (t : ℂ) :=
    (Complex.continuous_ofReal.tendsto x).eventually hF.eventually_analyticAt
  induction k with
  | zero =>
    filter_upwards [h, han] with t e1 e2
    simpa [iteratedDeriv_zero] using ⟨e1, e2⟩
  | succ k ih =>
    filter_upwards [ih.eventually_nhds] with t ht
    obtain ⟨e, a⟩ := ht.self_of_nhds
    have hder : HasDerivAt (fun r : ℝ => (iteratedDeriv k F (r : ℂ)).re) (deriv (iteratedDeriv k F) (t : ℂ)).re t :=
      (a.differentiableAt.hasDerivAt).real_of_complex
    have ev : iteratedDeriv k Φ =ᶠ[𝓝 t] fun r : ℝ => (iteratedDeriv k F (r : ℂ)).re := by
      filter_upwards [ht] with r hr using hr.1
    constructor
    · rw [iteratedDeriv_succ, iteratedDeriv_succ, ev.deriv_eq]
      exact hder.deriv
    · rw [iteratedDeriv_succ]
      exact a.deriv

lemma contDiffAt_of_local {Φ : ℝ → ℝ} {F : ℂ → ℂ} {x : ℝ} (hF : AnalyticAt ℂ F (x : ℂ)) (h : ∀ᶠ t in 𝓝 x, Φ t = (F (t : ℂ)).re) :
    ContDiffAt ℝ ∞ Φ x := by
  have h1 : ContDiffAt ℝ ∞ F (x : ℂ) := (hF.contDiffAt (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun t : ℝ => F (t : ℂ)) x :=
    ContDiffAt.comp x h1 Complex.ofRealCLM.contDiff.contDiffAt
  have h3 : ContDiffAt ℝ ∞ (fun t : ℝ => (F (t : ℂ)).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x h2
  exact h3.congr_of_eventuallyEq h

/-- A Cauchy bound at a real point from a ball where `Φ` is the real part of `F`. -/
lemma iter_le_of_ball {Φ : ℝ → ℝ} {F : ℂ → ℂ} {y R C : ℝ} (hR : 0 < R) (hF : DifferentiableOn ℂ F (closedBall (y : ℂ) R))
    (han : AnalyticAt ℂ F (y : ℂ)) (h : ∀ᶠ t in 𝓝 y, Φ t = (F (t : ℂ)).re) (hC : ∀ z ∈ sphere (y : ℂ) R, ‖F z‖ ≤ C) (k : ℕ) :
    |iteratedDeriv k Φ y| ≤ k ! * C / R ^ k := by
  have e := (iter_re han h k).self_of_nhds.1
  rw [e]
  have hd : DiffContOnCl ℂ F (ball (y : ℂ) R) := hF.diffContOnCl_ball subset_rfl
  exact (Complex.abs_re_le_norm _).trans (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR hd hC)

/-- **From local holomorphic extensions to uniform bounds on a compact set.** -/
theorem bounds_of_local {Φ : ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (h : ∀ x ∈ K, ∃ F : ℂ → ℂ, AnalyticAt ℂ F (x : ℂ) ∧ ∀ᶠ t in 𝓝 x, Φ t = (F (t : ℂ)).re) :
    ∃ A R : ℝ, 0 ≤ A ∧ 0 < R ∧ ∀ (k : ℕ), ∀ x ∈ K, |iteratedDeriv k Φ x| ≤ k ! * A / R ^ k := by
  have step : ∀ x ∈ K, ∃ ρ A : ℝ, 0 < ρ ∧ 0 ≤ A ∧ ∀ y : ℝ, |y - x| < ρ → ∀ k : ℕ, |iteratedDeriv k Φ y| ≤ k ! * A / ρ ^ k := by
    intro x hx
    obtain ⟨F, hF, hΦ⟩ := h x hx
    obtain ⟨r, hr, hd⟩ := Metric.eventually_nhds_iff_ball.1 hF.eventually_analyticAt
    obtain ⟨r', hr', hd'⟩ := Metric.eventually_nhds_iff_ball.1 hΦ
    set ρ := min r r' / 3 with hρ
    have hρ0 : 0 < ρ := by positivity
    have hle1 : 3 * ρ ≤ r := by rw [hρ]; linarith [min_le_left r r']
    have hle2 : 3 * ρ ≤ r' := by rw [hρ]; linarith [min_le_right r r']
    have hcomp : IsCompact (closedBall (x : ℂ) (2 * ρ)) := isCompact_closedBall _ _
    have hcont : ContinuousOn F (closedBall (x : ℂ) (2 * ρ)) := fun z hz =>
      (hd z (by rw [mem_ball]; rw [mem_closedBall] at hz; linarith)).continuousAt.continuousWithinAt
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
    refine ⟨ρ, max C 0, hρ0, le_max_right _ _, fun y hy k => ?_⟩
    have hdyx : dist (y : ℂ) (x : ℂ) = |y - x| := by
      rw [Complex.dist_of_im_eq (by simp)]; simp [Real.dist_eq]
    have hsub : closedBall (y : ℂ) ρ ⊆ ball (x : ℂ) r := fun z hz => by
      rw [mem_closedBall] at hz; rw [mem_ball]
      have := dist_triangle z (y : ℂ) (x : ℂ)
      rw [hdyx] at this
      linarith
    have hDO : DifferentiableOn ℂ F (closedBall (y : ℂ) ρ) := fun z hz => (hd z (hsub hz)).differentiableAt.differentiableWithinAt
    have hany : AnalyticAt ℂ F (y : ℂ) := hd _ (hsub (mem_closedBall_self hρ0.le))
    have hev : ∀ᶠ t in 𝓝 y, Φ t = (F (t : ℂ)).re := by
      have hyb : y ∈ ball x r' := by
        rw [mem_ball, Real.dist_eq]; linarith
      filter_upwards [isOpen_ball.mem_nhds hyb] with t ht using hd' t ht
    refine iter_le_of_ball hρ0 hDO hany hev (fun z hz => ?_) k
    have hz2 : z ∈ closedBall (x : ℂ) (2 * ρ) := by
      rw [mem_sphere] at hz; rw [mem_closedBall]
      have := dist_triangle z (y : ℂ) (x : ℂ)
      rw [hdyx] at this
      linarith
    exact (hC z hz2).trans (le_max_left _ _)
  choose! ρ A hρ hA hbd using step
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => ball x (ρ x)) fun x hx => ball_mem_nhds _ (hρ x hx)
  by_cases hne : t.Nonempty
  · have hRpos : 0 < t.inf' hne ρ := (Finset.lt_inf'_iff hne).2 fun x hx => hρ x (htK x hx)
    refine ⟨t.sup' hne A, t.inf' hne ρ, (hA _ (htK _ hne.choose_spec)).trans (Finset.le_sup' A hne.choose_spec), hRpos, fun k x hx => ?_⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hcov hx)
    have hxy : |x - i| < ρ i := by rwa [mem_ball, Real.dist_eq] at hxi
    refine (hbd i (htK i hi) x hxy k).trans ?_
    have hle : t.inf' hne ρ ≤ ρ i := Finset.inf'_le _ hi
    have hAi : A i ≤ t.sup' hne A := Finset.le_sup' A hi
    have hAi0 := hA i (htK i hi)
    have hA0 : 0 ≤ t.sup' hne A := hAi0.trans hAi
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hAi (by positivity)) (pow_pos hRpos k) (pow_le_pow_left₀ hRpos.le hle k)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    refine ⟨0, 1, le_rfl, one_pos, fun k x hx => ?_⟩
    simpa using hcov hx

/-! ### `cosh √s` is entire -/

/-- `Σ sⁿ/(2n)!`. -/
noncomputable def Cc (s : ℂ) : ℂ := ∑' n : ℕ, s ^ n / ((2 * n)! : ℂ)

/-- `Σ sⁿ/(2n+2)!`. -/
noncomputable def Ec (s : ℂ) : ℂ := ∑' n : ℕ, s ^ n / ((2 * n + 2)! : ℂ)

lemma summable_aux (R : ℝ) (hR : 0 ≤ R) (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) : Summable fun n : ℕ => R ^ n / ((m n)! : ℝ) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (Real.summable_pow_div_factorial R)
  have : ((n)! : ℝ) ≤ (m n)! := by exact_mod_cast Nat.factorial_le (hm n)
  have h0 : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  gcongr

lemma differentiable_of_series (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) : Differentiable ℂ fun s : ℂ => ∑' n : ℕ, s ^ n / ((m n)! : ℂ) := by
  intro z
  set R : ℝ := ‖z‖ + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hzb : z ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff, hR]; linarith
  have hsum := summable_aux R hR0 m hm
  have hd : DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, s ^ n / ((m n)! : ℂ)) (ball (0 : ℂ) R) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun n => ?_) isOpen_ball fun n w hw => ?_
    · exact ((differentiable_pow n).div_const _).differentiableOn
    · rw [norm_div, norm_pow, Complex.norm_natCast]
      have : ‖w‖ ≤ R := (mem_ball_zero_iff.1 hw).le
      gcongr
  exact (hd z hzb).differentiableAt (isOpen_ball.mem_nhds hzb)

lemma differentiable_Cc : Differentiable ℂ Cc := differentiable_of_series (fun n => 2 * n) fun n => by omega

lemma differentiable_Ec : Differentiable ℂ Ec := differentiable_of_series (fun n => 2 * n + 2) fun n => by omega

lemma summable_series (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) (s : ℂ) : Summable fun n : ℕ => s ^ n / ((m n)! : ℂ) := by
  have h := summable_aux ‖s‖ (norm_nonneg _) m hm
  refine Summable.of_norm (h.congr fun n => ?_)
  rw [norm_div, norm_pow, Complex.norm_natCast]

lemma Cc_eq (s : ℂ) : Cc s = 1 + s * Ec s := by
  have h1 := summable_series (fun n => 2 * n) (fun n => by omega) s
  unfold Cc Ec
  rw [h1.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  congr 1
  refine tsum_congr fun n => ?_
  rw [pow_succ, show 2 * (n + 1) = 2 * n + 2 by ring]
  ring

lemma Ec_zero : Ec 0 = 1 / 2 := by
  unfold Ec
  rw [tsum_eq_single 0 fun n hn => by simp [hn]]
  simp

lemma Cc_zero : Cc 0 = 1 := by rw [Cc_eq]; simp

lemma Cc_sq (r : ℝ) : Cc ((r : ℂ) ^ 2) = ((Real.cosh r : ℝ) : ℂ) := by
  have h := Complex.hasSum_cosh (r : ℂ)
  unfold Cc
  rw [Complex.ofReal_cosh, ← h.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [← pow_mul]

/-- `log Cc`. -/
noncomputable def fCc (s : ℂ) : ℂ := Complex.log (Cc s)

lemma hasDerivAt_Cc_zero : HasDerivAt Cc (1 / 2) 0 := by
  have h1 : HasDerivAt (fun s : ℂ => 1 + s * Ec s) (1 * Ec 0 + 0 * deriv Ec 0) 0 :=
    ((hasDerivAt_id (0 : ℂ)).mul (differentiable_Ec 0).hasDerivAt).const_add 1
  have e : Cc = fun s : ℂ => 1 + s * Ec s := funext Cc_eq
  rw [e]
  convert h1 using 1
  rw [Ec_zero]; ring

lemma analyticAt_fCc : AnalyticAt ℂ fCc 0 := by
  have h1 : AnalyticAt ℂ Cc 0 := differentiable_Cc.analyticAt 0
  have h2 : Cc 0 ∈ slitPlane := by rw [Cc_zero]; simp
  exact h1.clog h2

lemma fCc_zero : fCc 0 = 0 := by simp [fCc, Cc_zero]

lemma hasDerivAt_fCc : HasDerivAt fCc (1 / 2) 0 := by
  have h2 : Cc 0 ∈ slitPlane := by rw [Cc_zero]; simp
  have h := hasDerivAt_Cc_zero.clog h2
  have e : (1 / 2 : ℂ) = 1 / 2 / Cc 0 := by rw [Cc_zero]; norm_num
  rw [e]
  exact h

/-- **An analytic germ for `d²` as a function of `ψ = log cosh d`.** -/
theorem exists_S0 : ∃ S₀ : ℂ → ℂ, AnalyticAt ℂ S₀ 0 ∧ S₀ 0 = 0 ∧ ∀ᶠ r : ℝ in 𝓝 0, S₀ ((Real.log (Real.cosh r) : ℝ) : ℂ) = ((r ^ 2 : ℝ) : ℂ) := by
  have hne : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hcd : ContDiffAt ℂ ω fCc 0 := analyticAt_fCc.contDiffAt
  have hf' := hasDerivAt_fCc.hasFDerivAt_equiv hne
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hsymm := hcd.to_localInverse hf' hn
  set S₀ := hcd.localInverse hf' hn with hS₀
  have hstrict := hcd.hasStrictFDerivAt' hf' hn
  have hzero : S₀ 0 = 0 := by
    have := hcd.localInverse_apply_image hf' hn
    rwa [fCc_zero] at this
  refine ⟨S₀, ?_, hzero, ?_⟩
  · rw [fCc_zero] at hsymm
    exact hsymm.analyticAt
  · have hleft : ∀ᶠ s in 𝓝 (0 : ℂ), S₀ (fCc s) = s := hstrict.eventually_left_inverse
    have hc : Tendsto (fun r : ℝ => ((r : ℂ)) ^ 2) (𝓝 0) (𝓝 0) := by
      have : Continuous fun r : ℝ => ((r : ℂ)) ^ 2 := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [hc.eventually hleft] with r hr
    have e : fCc ((r : ℂ) ^ 2) = ((Real.log (Real.cosh r) : ℝ) : ℂ) := by
      rw [fCc, Cc_sq, Complex.ofReal_log (Real.cosh_pos r).le]
    rw [e] at hr
    rw [hr]; push_cast; rfl

end Qschubert
