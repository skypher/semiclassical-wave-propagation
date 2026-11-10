import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.ODE.Gronwall

/-!
# Evolution families of continuous bounded generators (Dyson series)

For a continuous `A : ℝ → 𝔸` with values in a complete normed algebra, the Dyson series
`X(t) = Σₙ Pₙ(t)`, `P₀ = 1`, `Pₙ₊₁(t) = ∫₀ᵗ A(s) Pₙ(s) ds`, converges for every `t`
(`‖Pₙ(t)‖ ≤ ‖1‖ (M|t|)ⁿ/n!`, `norm_dyson_le`), and solves `X' = A X`, `X(0) = 1`
(`hasDerivAt_dysonSum`, `dysonSum_zero`). This is the generic supplier for the mollified flow `V_ε`
of the proof of Theorem 1.3R (generator `(iħ/2)Δ_ε(t)`, `Δ_ε(t) = J_εΔ(t)J_ε` bounded) and for the
truncated propagators of Proposition A0.
-/

namespace Qschubert

open Filter Topology MeasureTheory intervalIntegral

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The Dyson terms `P₀ = 1`, `Pₙ₊₁(t) = ∫₀ᵗ A(s) Pₙ(s) ds`. -/
noncomputable def dyson (A : ℝ → 𝔸) : ℕ → ℝ → 𝔸
  | 0 => fun _ => 1
  | n + 1 => fun t => ∫ s in (0 : ℝ)..t, A s * dyson A n s

omit [CompleteSpace 𝔸] in
lemma dyson_succ (A : ℝ → 𝔸) (n : ℕ) (t : ℝ) :
    dyson A (n + 1) t = ∫ s in (0 : ℝ)..t, A s * dyson A n s := rfl

omit [CompleteSpace 𝔸] in
lemma continuous_dyson {A : ℝ → 𝔸} (hA : Continuous A) : ∀ n, Continuous (dyson A n)
  | 0 => continuous_const
  | n + 1 => by
    have h : Continuous fun s => A s * dyson A n s := hA.mul (continuous_dyson hA n)
    exact continuous_primitive (fun a b => h.intervalIntegrable a b) 0

lemma hasDerivAt_dyson_succ {A : ℝ → 𝔸} (hA : Continuous A) (n : ℕ) (t : ℝ) :
    HasDerivAt (dyson A (n + 1)) (A t * dyson A n t) t :=
  ((hA.mul (continuous_dyson hA n)).integral_hasStrictDerivAt 0 t).hasDerivAt

omit [CompleteSpace 𝔸] in
lemma dyson_succ_zero (A : ℝ → 𝔸) (n : ℕ) : dyson A (n + 1) 0 = 0 := by
  simp [dyson_succ]

omit [CompleteSpace 𝔸] in
/-- `‖∫₀ᵗ f‖ ≤ C |t|ⁿ⁺¹/(n+1)` when `‖f(s)‖ ≤ C |s|ⁿ` for `|s| ≤ |t|`. -/
lemma norm_integral_le_pow {f : ℝ → 𝔸} {C : ℝ} (n : ℕ) (t : ℝ)
    (hb : ∀ s, |s| ≤ |t| → ‖f s‖ ≤ C * |s| ^ n) :
    ‖∫ s in (0 : ℝ)..t, f s‖ ≤ C * |t| ^ (n + 1) / (n + 1) := by
  rcases le_total 0 t with ht | ht
  · have h := norm_integral_le_of_norm_le (μ := volume) ht (g := fun s => C * s ^ n)
      (Eventually.of_forall fun s hs => by
        have hs0 : 0 ≤ s := hs.1.le
        have := hb s (by rw [abs_of_nonneg hs0, abs_of_nonneg ht]; exact hs.2)
        rwa [abs_of_nonneg hs0] at this)
      ((continuous_const.mul (continuous_pow n)).intervalIntegrable 0 t)
    rw [intervalIntegral.integral_const_mul, integral_pow] at h
    rw [abs_of_nonneg ht]
    calc _ ≤ C * ((t ^ (n + 1) - 0 ^ (n + 1)) / (n + 1)) := h
      _ = C * t ^ (n + 1) / (n + 1) := by simp [mul_div_assoc]
  · rw [integral_symm, norm_neg]
    have h := norm_integral_le_of_norm_le (μ := volume) ht (g := fun s => C * (-s) ^ n)
      (Eventually.of_forall fun s hs => by
        have hs0 : s ≤ 0 := hs.2
        have := hb s (by rw [abs_of_nonpos hs0, abs_of_nonpos ht]; linarith [hs.1])
        rwa [abs_of_nonpos hs0] at this)
      ((continuous_const.mul ((continuous_neg).pow n)).intervalIntegrable t 0)
    have e : ∫ s in t..0, C * (-s) ^ n = C * (-t) ^ (n + 1) / (n + 1) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_neg (fun s => s ^ n), neg_zero, integral_pow]
      simp [mul_div_assoc]
    rw [e] at h
    rwa [abs_of_nonpos ht]

omit [CompleteSpace 𝔸] in
/-- `‖Pₙ(t)‖ ≤ ‖1‖ (M|t|)ⁿ/n!` while `‖A‖ ≤ M` on `[-|t|, |t|]`. -/
lemma norm_dyson_le {A : ℝ → 𝔸} (hA : Continuous A) {M : ℝ} (hM0 : 0 ≤ M) {R : ℝ}
    (hM : ∀ s, |s| ≤ R → ‖A s‖ ≤ M) :
    ∀ n t, |t| ≤ R → ‖dyson A n t‖ ≤ ‖(1 : 𝔸)‖ * (M * |t|) ^ n / n.factorial
  | 0, t, _ => by simp [dyson]
  | n + 1, t, ht => by
    rw [dyson_succ]
    have hb : ∀ s, |s| ≤ |t| → ‖A s * dyson A n s‖ ≤ (‖(1 : 𝔸)‖ * M ^ (n + 1) / n.factorial) * |s| ^ n := by
      intro s hs
      have hsR : |s| ≤ R := hs.trans ht
      calc ‖A s * dyson A n s‖ ≤ ‖A s‖ * ‖dyson A n s‖ := norm_mul_le _ _
        _ ≤ M * (‖(1 : 𝔸)‖ * (M * |s|) ^ n / n.factorial) :=
          mul_le_mul (hM s hsR) (norm_dyson_le hA hM0 hM n s hsR) (norm_nonneg _) hM0
        _ = (‖(1 : 𝔸)‖ * M ^ (n + 1) / n.factorial) * |s| ^ n := by rw [mul_pow]; ring
    refine (norm_integral_le_pow (f := fun s => A s * dyson A n s) n t hb).trans (le_of_eq ?_)
    rw [Nat.factorial_succ, mul_pow]
    push_cast
    field_simp

/-- The Dyson series `X(t) = Σₙ Pₙ(t)`. -/
noncomputable def dysonSum (A : ℝ → 𝔸) (t : ℝ) : 𝔸 := ∑' n, dyson A n t

lemma summable_pow_div_factorial_mul (c x : ℝ) :
    Summable fun n : ℕ => c * x ^ n / n.factorial := by
  simpa [mul_div_assoc] using (Real.summable_pow_div_factorial x).mul_left c

lemma summable_dyson {A : ℝ → 𝔸} (hA : Continuous A) (t : ℝ) : Summable fun n => dyson A n t := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -|t|) (b := |t|)).exists_bound_of_continuousOn hA.continuousOn
  have hM' : ∀ s, |s| ≤ |t| → ‖A s‖ ≤ max M 0 := fun s hs =>
    (hM s (abs_le.1 hs)).trans (le_max_left _ _)
  refine Summable.of_norm_bounded (summable_pow_div_factorial_mul ‖(1 : 𝔸)‖ (max M 0 * |t|)) ?_
  intro n
  simpa [mul_div_assoc] using norm_dyson_le hA (le_max_right _ _) hM' n t le_rfl

omit [CompleteSpace 𝔸] in
lemma dysonSum_zero (A : ℝ → 𝔸) : dysonSum A 0 = 1 := by
  rw [dysonSum, tsum_eq_single 0]
  · rfl
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact dyson_succ_zero A m

/-- **The Dyson series solves `X' = A X`.** -/
theorem hasDerivAt_dysonSum {A : ℝ → 𝔸} (hA : Continuous A) (t : ℝ) :
    HasDerivAt (dysonSum A) (A t * dysonSum A t) t := by
  set R : ℝ := |t| + 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hA.continuousOn
  set M' := max M 0
  have hM' : ∀ s, |s| ≤ R → ‖A s‖ ≤ M' := fun s hs => (hM s (abs_le.1 hs)).trans (le_max_left _ _)
  have hM0 : 0 ≤ M' := le_max_right _ _
  set g' : ℕ → ℝ → 𝔸 := fun n y => Nat.casesOn n 0 fun m => A y * dyson A m y with hg'
  set u : ℕ → ℝ := fun n => Nat.casesOn n 0 fun m => M' * (‖(1 : 𝔸)‖ * (M' * R) ^ m / m.factorial)
  have hu : Summable u := by
    rw [← summable_nat_add_iff 1]
    simpa [u, mul_div_assoc, mul_assoc] using
      (summable_pow_div_factorial_mul (M' * ‖(1 : 𝔸)‖) (M' * R))
  have hopen : IsOpen (Set.Ioo (-R) R) := isOpen_Ioo
  have ht : t ∈ Set.Ioo (-R) R := by
    constructor <;> [have := neg_abs_le t; have := le_abs_self t] <;> linarith
  have hderiv : ∀ n y, y ∈ Set.Ioo (-R) R → HasDerivAt (dyson A n) (g' n y) y := by
    intro n y _
    cases n with
    | zero => exact hasDerivAt_const y (1 : 𝔸)
    | succ m => exact hasDerivAt_dyson_succ hA m y
  have hbound : ∀ n y, y ∈ Set.Ioo (-R) R → ‖g' n y‖ ≤ u n := by
    intro n y hy
    have hyR : |y| ≤ R := abs_le.2 ⟨hy.1.le, hy.2.le⟩
    cases n with
    | zero => simp [g', u]
    | succ m =>
      show ‖A y * dyson A m y‖ ≤ M' * (‖(1 : 𝔸)‖ * (M' * R) ^ m / m.factorial)
      refine (norm_mul_le _ _).trans (mul_le_mul (hM' y hyR) ?_ (norm_nonneg _) hM0)
      refine (norm_dyson_le hA hM0 hM' m y hyR).trans ?_
      gcongr
  have h := hasDerivAt_tsum_of_isPreconnected hu hopen (isPreconnected_Ioo) hderiv hbound ht
    (summable_dyson hA t) ht
  have hs : Summable fun m => A t * dyson A m t := (summable_dyson hA t).mul_left (A t)
  have e : ∑' n, g' n t = A t * dysonSum A t := by
    have hs' : Summable fun n => g' n t := by
      rw [← summable_nat_add_iff 1]; exact hs
    rw [hs'.tsum_eq_zero_add]
    simp only [g']
    rw [dysonSum, (summable_dyson hA t).tsum_mul_left]
    exact zero_add _
  rw [← e]
  exact h

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The adjoint as a real-linear isometry of `E →L[ℂ] E`. -/
noncomputable def adjR : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E) :=
  LinearMap.mkContinuous
    { toFun := ContinuousLinearMap.adjoint
      map_add' := fun S T => map_add _ S T
      map_smul' := fun r T => by
        rw [← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]
        rfl } 1
    (fun T => by simp)

lemma adjR_apply (T : E →L[ℂ] E) : adjR T = ContinuousLinearMap.adjoint T := rfl

lemma adjoint_mul (S T : E →L[ℂ] E) :
    ContinuousLinearMap.adjoint (S * T) = ContinuousLinearMap.adjoint T * ContinuousLinearMap.adjoint S :=
  ContinuousLinearMap.adjoint_comp S T

variable {A : ℝ → E →L[ℂ] E}

lemma hasDerivAt_adjoint_dysonSum (hA : Continuous A) (t : ℝ) :
    HasDerivAt (fun r => ContinuousLinearMap.adjoint (dysonSum A r))
      (ContinuousLinearMap.adjoint (dysonSum A t) * ContinuousLinearMap.adjoint (A t)) t := by
  have h : HasDerivAt (fun r => adjR (dysonSum A r)) (adjR (A t * dysonSum A t)) t :=
    (adjR (E := E)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_dysonSum hA t)
  rw [adjR_apply (A t * dysonSum A t), adjoint_mul] at h
  exact h

/-- For skew-adjoint `A`, `X(t)* X(t) = 1`. -/
theorem adjoint_dysonSum_mul_self (hA : Continuous A)
    (hskew : ∀ t, ContinuousLinearMap.adjoint (A t) = -A t) (t : ℝ) :
    ContinuousLinearMap.adjoint (dysonSum A t) * dysonSum A t = 1 := by
  set f : ℝ → E →L[ℂ] E := fun r => ContinuousLinearMap.adjoint (dysonSum A r) * dysonSum A r
  have hd : ∀ r, HasDerivAt f 0 r := by
    intro r
    have h := (hasDerivAt_adjoint_dysonSum hA r).mul (hasDerivAt_dysonSum hA r)
    rw [hskew r] at h
    convert h using 1
    simp [mul_assoc]
  have hc := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) t 0
  simp only [f, dysonSum_zero, ContinuousLinearMap.adjoint_one, one_mul] at hc
  exact hc

/-- For skew-adjoint `A`, `X(t) X(t)* = 1` (Gronwall). -/
theorem dysonSum_mul_adjoint_self (hA : Continuous A)
    (hskew : ∀ t, ContinuousLinearMap.adjoint (A t) = -A t) (t : ℝ) :
    dysonSum A t * ContinuousLinearMap.adjoint (dysonSum A t) = 1 := by
  set D : ℝ → E →L[ℂ] E := fun r => dysonSum A r * ContinuousLinearMap.adjoint (dysonSum A r) - 1
  have hD : ∀ r, HasDerivAt D (A r * D r - D r * A r) r := by
    intro r
    have h := ((hasDerivAt_dysonSum hA r).mul (hasDerivAt_adjoint_dysonSum hA r)).sub_const 1
    rw [hskew r] at h
    convert h using 1
    simp only [D, sub_mul, mul_sub, mul_one, one_mul, mul_neg, mul_assoc]
    abel
  have hD0 : D 0 = 0 := by simp [D, dysonSum_zero, ContinuousLinearMap.adjoint_one]
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -|t|) (b := |t|)).exists_bound_of_continuousOn hA.continuousOn
  have hbd : ∀ r, |r| ≤ |t| → ‖A r * D r - D r * A r‖ ≤ (2 * max M 0) * ‖D r‖ := by
    intro r hr
    have hA' : ‖A r‖ ≤ max M 0 := (hM r (abs_le.1 hr)).trans (le_max_left _ _)
    calc ‖A r * D r - D r * A r‖ ≤ ‖A r * D r‖ + ‖D r * A r‖ := norm_sub_le _ _
      _ ≤ ‖A r‖ * ‖D r‖ + ‖D r‖ * ‖A r‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (2 * max M 0) * ‖D r‖ := by nlinarith [norm_nonneg (D r)]
  suffices D t = 0 by
    have := this
    simp only [D, sub_eq_zero] at this
    exact this
  rcases le_total 0 t with ht | ht
  · refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (a := 0) (b := t)
      (fun r _ => (hD r).continuousAt.continuousWithinAt) (fun r _ => (hD r).hasDerivWithinAt) hD0
      (fun r hr => hbd r ?_) t ⟨ht, le_rfl⟩
    rw [abs_of_nonneg hr.1, abs_of_nonneg ht]; exact hr.2.le
  · set D' : ℝ → E →L[ℂ] E := fun r => D (-r)
    have hD' : ∀ r, HasDerivAt D' (-(A (-r) * D (-r) - D (-r) * A (-r))) r := by
      intro r
      have := (hD (-r)).scomp r (hasDerivAt_neg r)
      simpa [D', Function.comp_def] using this
    have h := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (a := 0) (b := -t)
      (fun r _ => (hD' r).continuousAt.continuousWithinAt) (fun r _ => (hD' r).hasDerivWithinAt)
      (by simp [D', hD0])
      (fun r hr => by
        rw [norm_neg]
        refine hbd (-r) ?_
        rw [abs_neg, abs_of_nonneg hr.1, abs_of_nonpos ht]; exact hr.2.le) (-t) ⟨by linarith, le_rfl⟩
    simpa [D'] using h

/-- Backward Duhamel for the Dyson flow: `X(t)* a - a = ∫₀ᵗ X(s)* A(s)* a ds`; for skew-adjoint
`A` this is `-∫₀ᵗ X(s)* A(s) a ds`. -/
theorem adjoint_dysonSum_sub_eq_integral (hA : Continuous A) (a : E) (t : ℝ) :
    ContinuousLinearMap.adjoint (dysonSum A t) a - a
      = ∫ s in (0 : ℝ)..t, (ContinuousLinearMap.adjoint (dysonSum A s) * ContinuousLinearMap.adjoint (A s)) a := by
  have hd : ∀ s, HasDerivAt (fun r => ContinuousLinearMap.adjoint (dysonSum A r) a)
      ((ContinuousLinearMap.adjoint (dysonSum A s) * ContinuousLinearMap.adjoint (A s)) a) s :=
    fun s => ((ContinuousLinearMap.apply ℂ E a).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_adjoint_dysonSum hA s)
  have hcont : Continuous fun s =>
      (ContinuousLinearMap.adjoint (dysonSum A s) * ContinuousLinearMap.adjoint (A s)) a := by
    have h1 : Continuous fun s => ContinuousLinearMap.adjoint (dysonSum A s) :=
      continuous_iff_continuousAt.2 fun s => (hasDerivAt_adjoint_dysonSum hA s).continuousAt
    have h2 : Continuous fun s => ContinuousLinearMap.adjoint (A s) :=
      (adjR (E := E)).continuous.comp hA
    exact (h1.mul h2).clm_apply continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hcont.intervalIntegrable 0 t),
    dysonSum_zero, ContinuousLinearMap.adjoint_one]
  rfl

end Hilbert

end Qschubert
