import Qschubert.KLM2a

/-!
# Words of a function of `ψ̃ = log X₀`

For `Φ` smooth near `[0, ∞)` with `|Φ^{(k)}| ≤ A k! ρ^{-k}` on `[0, ∞)`, every word in `X`, `Y` of `Φ ∘ ψ̃` is bounded by `A (4 + 3/ρ)^j j!` (`wb_comp`).
With `Xψ̃ = ξ`, `Yψ̃ = υ - 1`: `Z_S Φ(ψ̃) = Σ_k Φ^{(k)}(ψ̃) Q_{S,k}(ξ, υ)` (`wordR_comp`), where `Q` is defined by the recursion `QQ`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set MvPolynomial
open scoped ENNReal ContDiff Nat

/-- `ψ̃ = -log h = log X₀`. -/
noncomputable def psiF (w : ℂ) : ℝ := -Real.log (hF w)

lemma psiF_nonneg {w : ℂ} (hw : 0 < w.im) : 0 ≤ psiF w := by
  have := Real.log_nonpos (hF_pos hw).le (hF_le_one hw)
  unfold psiF; linarith

lemma hasFDerivAt_psiF {w : ℂ} (hw : 0 < w.im) :
    HasFDerivAt psiF (-((hF w)⁻¹ • fderiv ℝ hF w)) w := by
  have hh : HasFDerivAt hF (fderiv ℝ hF w) w := ((contDiff_hF.differentiable (by simp)) w).hasFDerivAt
  exact (hh.log (hF_pos hw).ne').neg

lemma contDiffAt_psiF {w : ℂ} (hw : 0 < w.im) : ContDiffAt ℝ ∞ psiF w :=
  (contDiff_hF.contDiffAt.log (hF_pos hw).ne').neg

/-- The multiplier of a letter: `Xψ̃ = ξ`, `Yψ̃ = υ - 1`. -/
noncomputable def lz (z : Bool) : P2 := if z then X 0 else X 1 - 1

lemma ev_lz (z : Bool) (a b : ℝ) : ev (lz z) a b = if z then a else b - 1 := by
  cases z <;> simp [lz, ev]

lemma ev_mul (P Q : P2) (a b : ℝ) : ev (P * Q) a b = ev P a b * ev Q a b := by
  simp [ev]

lemma ev_add (P Q : P2) (a b : ℝ) : ev (P + Q) a b = ev P a b + ev Q a b := by
  simp [ev]

lemma ev_zero (a b : ℝ) : ev (0 : P2) a b = 0 := by simp [ev]

lemma ev_one (a b : ℝ) : ev (1 : P2) a b = 1 := by simp [ev]

lemma ev_DZ_zero (z : Bool) (P : P2) (a b : ℝ) :
    ev (DZ 0 z P) a b = if z then (b - a ^ 2) * ev (pderiv 0 P) a b - a * b * ev (pderiv 1 P) a b
      else (a - a * b) * ev (pderiv 0 P) a b + (2 * b - b ^ 2) * ev (pderiv 1 P) a b := by
  cases z
  · simp only [DZ, Bool.false_eq_true, ite_false]; rw [ev_DY]; ring
  · simp only [DZ, ite_true]; rw [ev_DX]; ring

/-- `Z ψ̃`. -/
lemma vfR_psiF (z : Bool) {w : ℂ} (hw : 0 < w.im) :
    w.im * (-((hF w)⁻¹ • fderiv ℝ hF w)) (letter z) = ev (lz z) (xiF w) (upF w) := by
  have hh := (hF_pos hw).ne'
  have e2 : ∀ v, w.im * fderiv ℝ hF w v = vfR v hF w := fun v => rfl
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [ev_lz]
  cases z
  · simp only [letter, Bool.false_eq_true, ite_false]
    have a := e2 Complex.I
    rw [vfR_hF_I] at a
    field_simp
    linear_combination -a
  · simp only [letter, ite_true]
    have a := e2 1
    rw [vfR_hF_one] at a
    field_simp
    linear_combination -a

/-- The coefficient polynomials. -/
noncomputable def QQ : List Bool → ℕ → P2
  | [], k => if k = 0 then 1 else 0
  | z :: S, 0 => DZ 0 z (QQ S 0)
  | z :: S, k + 1 => DZ 0 z (QQ S (k + 1)) + lz z * QQ S k

lemma DZ_zero' (z : Bool) : DZ 0 z (0 : P2) = 0 := DZ_zero 0 z

lemma QQ_vanish : ∀ (S : List Bool) (k : ℕ), S.length < k → QQ S k = 0
  | [], k, h => by
    have : k ≠ 0 := by simpa using (Nat.pos_iff_ne_zero.1 h)
    simp [QQ, this]
  | z :: S, 0, h => by simp at h
  | z :: S, k + 1, h => by
    have h' : S.length < k := by simpa using h
    have h1 := QQ_vanish S (k + 1) (by omega)
    have h2 := QQ_vanish S k h'
    simp [QQ, h1, h2, DZ_zero']

lemma cd_iter {Φ : ℝ → ℝ} {x : ℝ} (hΦ : ContDiffAt ℝ ∞ Φ x) : ∀ k : ℕ, ContDiffAt ℝ ∞ (iteratedDeriv k Φ) x
  | 0 => by simpa [iteratedDeriv_zero] using hΦ
  | k + 1 => by
    have h := cd_iter hΦ k
    have e : iteratedDeriv (k + 1) Φ = fun y => fderiv ℝ (iteratedDeriv k Φ) y 1 := by
      funext y; rw [iteratedDeriv_succ]; rfl
    rw [e]
    exact (h.fderiv_right (m := ∞) le_rfl).clm_apply contDiffAt_const

lemma hasDerivAt_iter {Φ : ℝ → ℝ} {x : ℝ} (hΦ : ContDiffAt ℝ ∞ Φ x) (k : ℕ) :
    HasDerivAt (iteratedDeriv k Φ) (iteratedDeriv (k + 1) Φ x) x := by
  have h := ((cd_iter hΦ k).differentiableAt (by simp)).hasDerivAt
  rwa [← iteratedDeriv_succ] at h

/-- One term under one letter. -/
lemma hasFDerivAt_term {Φ : ℝ → ℝ} (k : ℕ) (Q : P2) {w : ℂ} (hw : 0 < w.im) (hΦ : ContDiffAt ℝ ∞ Φ (psiF w)) :
    HasFDerivAt (fun u => iteratedDeriv k Φ (psiF u) * ev Q (xiF u) (upF u))
      (iteratedDeriv k Φ (psiF w) • (fderiv ℝ (fun u => ev Q (xiF u) (upF u)) w)
        + ev Q (xiF w) (upF w) • (iteratedDeriv (k + 1) Φ (psiF w) • (-((hF w)⁻¹ • fderiv ℝ hF w)))) w := by
  have h1 : HasFDerivAt (fun u => iteratedDeriv k Φ (psiF u))
      (iteratedDeriv (k + 1) Φ (psiF w) • (-((hF w)⁻¹ • fderiv ℝ hF w))) w :=
    (hasDerivAt_iter hΦ k).comp_hasFDerivAt w (hasFDerivAt_psiF hw)
  have h2 : HasFDerivAt (fun u => ev Q (xiF u) (upF u)) (fderiv ℝ (fun u => ev Q (xiF u) (upF u)) w) w :=
    (hasFDerivAt_ev Q w).differentiableAt.hasFDerivAt
  exact h1.fun_mul h2

/-- `Z(ev Q)`. -/
lemma letter_ev (z : Bool) (Q : P2) (w : ℂ) :
    w.im * fderiv ℝ (fun u => ev Q (xiF u) (upF u)) w (letter z) = ev (DZ 0 z Q) (xiF w) (upF w) := by
  have h := vfR_ev Q (letter z) w
  have h' : w.im * fderiv ℝ (fun u => ev Q (xiF u) (upF u)) w (letter z) = _ := h
  rw [h', ev_DZ_zero]
  cases z
  · simp only [letter, Bool.false_eq_true, ite_false]
    rw [vfR_xiF_I, vfR_upF_I]
    ring
  · simp only [letter, ite_true]
    rw [vfR_xiF_one, vfR_upF_one]
    ring

/-- **The word expansion.** -/
theorem wordR_comp {Φ : ℝ → ℝ} (hΦ : ∀ x, 0 ≤ x → ContDiffAt ℝ ∞ Φ x) (S : List Bool) {w : ℂ} (hw : 0 < w.im) :
    wordR S (fun u => Φ (psiF u)) w
      = ∑ k ∈ Finset.range (S.length + 1), iteratedDeriv k Φ (psiF w) * ev (QQ S k) (xiF w) (upF w) := by
  induction S generalizing w with
  | nil => simp [wordR, QQ, ev_one]
  | cons z S ih =>
    have hev : wordR S (fun u => Φ (psiF u)) =ᶠ[𝓝 w]
        fun u => ∑ k ∈ Finset.range (S.length + 1), iteratedDeriv k Φ (psiF u) * ev (QQ S k) (xiF u) (upF u) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw] with u hu
      exact ih hu
    have hG : HasFDerivAt (fun u => ∑ k ∈ Finset.range (S.length + 1), iteratedDeriv k Φ (psiF u) * ev (QQ S k) (xiF u) (upF u))
        (∑ k ∈ Finset.range (S.length + 1), (iteratedDeriv k Φ (psiF w) • (fderiv ℝ (fun u => ev (QQ S k) (xiF u) (upF u)) w)
          + ev (QQ S k) (xiF w) (upF w) • (iteratedDeriv (k + 1) Φ (psiF w) • (-((hF w)⁻¹ • fderiv ℝ hF w))))) w :=
      HasFDerivAt.fun_sum fun k _ => hasFDerivAt_term k (QQ S k) hw (hΦ _ (psiF_nonneg hw))
    show vfR (letter z) (wordR S (fun u => Φ (psiF u))) w = _
    rw [vfR_congr hev, vfR_of_hasFDerivAt hG]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    have hterm : ∀ k, w.im * (iteratedDeriv k Φ (psiF w) * fderiv ℝ (fun u => ev (QQ S k) (xiF u) (upF u)) w (letter z)
          + ev (QQ S k) (xiF w) (upF w) * (iteratedDeriv (k + 1) Φ (psiF w) * (-((hF w)⁻¹ • fderiv ℝ hF w)) (letter z)))
        = iteratedDeriv k Φ (psiF w) * ev (DZ 0 z (QQ S k)) (xiF w) (upF w)
          + iteratedDeriv (k + 1) Φ (psiF w) * (ev (lz z) (xiF w) (upF w) * ev (QQ S k) (xiF w) (upF w)) := fun k => by
      rw [← letter_ev z (QQ S k) w, ← vfR_psiF z hw]
      ring
    simp only [hterm]
    rw [Finset.sum_add_distrib]
    have hR : ∑ k ∈ Finset.range (S.length + 1 + 1), iteratedDeriv k Φ (psiF w) * ev (QQ (z :: S) k) (xiF w) (upF w)
        = ∑ k ∈ Finset.range (S.length + 1), iteratedDeriv (k + 1) Φ (psiF w) * ev (QQ (z :: S) (k + 1)) (xiF w) (upF w)
          + iteratedDeriv 0 Φ (psiF w) * ev (QQ (z :: S) 0) (xiF w) (upF w) := Finset.sum_range_succ' _ _
    show _ = ∑ k ∈ Finset.range (S.length + 1 + 1), iteratedDeriv k Φ (psiF w) * ev (QQ (z :: S) k) (xiF w) (upF w)
    rw [hR]
    simp only [QQ, ev_add, ev_mul, mul_add, Finset.sum_add_distrib]
    have hlast : ∑ k ∈ Finset.range (S.length + 1), iteratedDeriv k Φ (psiF w) * ev (DZ 0 z (QQ S k)) (xiF w) (upF w)
        = ∑ k ∈ Finset.range S.length, iteratedDeriv (k + 1) Φ (psiF w) * ev (DZ 0 z (QQ S (k + 1))) (xiF w) (upF w)
          + iteratedDeriv 0 Φ (psiF w) * ev (DZ 0 z (QQ S 0)) (xiF w) (upF w) := Finset.sum_range_succ' _ _
    have hlast2 : ∑ k ∈ Finset.range (S.length + 1), iteratedDeriv (k + 1) Φ (psiF w) * ev (DZ 0 z (QQ S (k + 1))) (xiF w) (upF w)
        = ∑ k ∈ Finset.range S.length, iteratedDeriv (k + 1) Φ (psiF w) * ev (DZ 0 z (QQ S (k + 1))) (xiF w) (upF w) := by
      rw [Finset.sum_range_succ, QQ_vanish S (S.length + 1) (by omega), DZ_zero', ev_zero, mul_zero, add_zero]
    rw [hlast, hlast2]
    ring

/-! ### The norm of the coefficients -/

lemma wN_X_mul (i : Fin 2) (P : P2) : wN (X i * P) ≤ (if i = 0 then 1 else 2) * wN P := by
  conv_lhs => rw [P.as_sum, Finset.mul_sum]
  refine (wN_sum_le _ _).trans ?_
  rw [wN, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [X_eq_monomial, monomial_mul, wN_monomial, one_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, if_true, Finsupp.add_apply, Finsupp.single_eq_same]
    rw [one_mul]
    have : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 1 = 0 := by simp
    rw [this, zero_add]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false, Finsupp.add_apply, Finsupp.single_eq_same]
    rw [add_comm, pow_succ]
    ring_nf
    exact le_rfl

lemma wN_lz_mul (z : Bool) (P : P2) : wN (lz z * P) ≤ 3 * wN P := by
  have h0 := wN_nonneg P
  cases z
  · simp only [lz, Bool.false_eq_true, ite_false]
    rw [sub_mul, one_mul]
    have h1 := wN_X_mul 1 P
    simp only [one_ne_zero, if_false] at h1
    linarith [wN_sub_le (X 1 * P) P]
  · simp only [lz, ite_true]
    have h1 := wN_X_mul 0 P
    simp only [if_true] at h1
    linarith

lemma degLe_X_mul (i : Fin 2) {P : P2} {d : ℕ} (hP : DegLe P d) : DegLe (X i * P) (d + 1) := by
  rw [P.as_sum, Finset.mul_sum]
  refine degLe_sum _ _ fun m hm => ?_
  rw [X_eq_monomial, monomial_mul]
  refine degLe_monomial ?_
  have h := hP m hm
  fin_cases i <;> simp <;> omega

lemma degLe_lz_mul (z : Bool) {P : P2} {d : ℕ} (hP : DegLe P d) : DegLe (lz z * P) (d + 1) := by
  cases z
  · simp only [lz, Bool.false_eq_true, ite_false]
    rw [sub_mul, one_mul]
    exact degLe_sub (degLe_X_mul 1 hP) (degLe_mono hP (by omega))
  · simp only [lz, ite_true]
    exact degLe_X_mul 0 hP

lemma degLe_zero' (d : ℕ) : DegLe (0 : P2) d := fun m hm => by simp at hm

lemma QQ_deg : ∀ (S : List Bool) (k : ℕ), DegLe (QQ S k) S.length
  | [], k => by
    by_cases hk : k = 0
    · subst hk
      intro m hm
      have : m = 0 := by
        have h := MvPolynomial.support_monomial_subset (show m ∈ (monomial 0 (1 : ℝ) : P2).support by simpa [QQ] using hm)
        simpa using h
      simp [this]
    · simp only [QQ, hk, if_false]
      exact degLe_zero' _
  | z :: S, 0 => by
    simpa [QQ] using (wN_DZ_le 0 z (QQ_deg S 0)).2
  | z :: S, k + 1 => by
    simp only [QQ, List.length_cons]
    exact degLe_add (wN_DZ_le 0 z (QQ_deg S (k + 1))).2 (degLe_lz_mul z (QQ_deg S k))

/-- The weighted sum of the coefficient norms. -/
noncomputable def aS (ρi : ℝ) (S : List Bool) : ℝ :=
  ∑ k ∈ Finset.range (S.length + 1), (k ! : ℝ) * ρi ^ k * wN (QQ S k)

lemma aS_nil (ρi : ℝ) : aS ρi [] = 1 := by
  simp [aS, QQ, wN, MvPolynomial.support_one]

lemma aS_nonneg {ρi : ℝ} (hρ : 0 ≤ ρi) (S : List Bool) : 0 ≤ aS ρi S :=
  Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (wN_nonneg _)

lemma aS_cons {ρi : ℝ} (hρ : 0 ≤ ρi) (z : Bool) (S : List Bool) :
    aS ρi (z :: S) ≤ (4 + 3 * ρi) * (S.length + 1) * aS ρi S := by
  set j := S.length with hj
  have hd : ∀ k, wN (DZ 0 z (QQ S k)) ≤ 4 * j * wN (QQ S k) := fun k => by
    have := (wN_DZ_le 0 z (QQ_deg S k)).1
    simpa using this
  have hs0 : 0 ≤ aS ρi S := aS_nonneg hρ S
  show ∑ k ∈ Finset.range (S.length + 1 + 1), (k ! : ℝ) * ρi ^ k * wN (QQ (z :: S) k) ≤ _
  rw [Finset.sum_range_succ']
  simp only [QQ]
  have h1 : ∑ k ∈ Finset.range (S.length + 1), ((k + 1)! : ℝ) * ρi ^ (k + 1) * wN (DZ 0 z (QQ S (k + 1)) + lz z * QQ S k)
      ≤ ∑ k ∈ Finset.range (S.length + 1), (((k + 1)! : ℝ) * ρi ^ (k + 1) * (4 * j * wN (QQ S (k + 1)))
        + ((k + 1)! : ℝ) * ρi ^ (k + 1) * (3 * wN (QQ S k))) := by
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (wN_add_le _ _).trans (add_le_add (hd _) (wN_lz_mul z _))
  have h2 : ∑ k ∈ Finset.range (S.length + 1), ((k + 1)! : ℝ) * ρi ^ (k + 1) * (3 * wN (QQ S k))
      ≤ 3 * ρi * (j + 1) * aS ρi S := by
    rw [aS, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' : (k : ℝ) + 1 ≤ j + 1 := by
      have : k ≤ j := by simpa [hj, Nat.lt_succ_iff] using hk
      have : (k : ℝ) ≤ j := by exact_mod_cast this
      linarith
    have e : ((k + 1)! : ℝ) = (k + 1) * k ! := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [e, pow_succ]
    have hw := wN_nonneg (QQ S k)
    have hf : (0 : ℝ) ≤ k ! := by positivity
    have hp : 0 ≤ ρi ^ k := by positivity
    have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    have key : ((k : ℝ) + 1) * (k ! * ρi ^ k * wN (QQ S k) * (3 * ρi)) ≤ (j + 1) * (k ! * ρi ^ k * wN (QQ S k) * (3 * ρi)) :=
      mul_le_mul_of_nonneg_right hk' (by positivity)
    nlinarith [key]
  have h3 : ∑ k ∈ Finset.range (S.length + 1), ((k + 1)! : ℝ) * ρi ^ (k + 1) * (4 * j * wN (QQ S (k + 1)))
        + (0 ! : ℝ) * ρi ^ 0 * wN (DZ 0 z (QQ S 0)) ≤ 4 * j * aS ρi S := by
    have e0 : (0 ! : ℝ) * ρi ^ 0 * wN (DZ 0 z (QQ S 0)) ≤ (0 ! : ℝ) * ρi ^ 0 * (4 * j * wN (QQ S 0)) :=
      mul_le_mul_of_nonneg_left (hd 0) (by positivity)
    have e1 : 4 * (j : ℝ) * aS ρi S = ∑ k ∈ Finset.range (S.length + 1), ((k + 1)! : ℝ) * ρi ^ (k + 1) * (4 * j * wN (QQ S (k + 1)))
        + (0 ! : ℝ) * ρi ^ 0 * (4 * j * wN (QQ S 0)) := by
      rw [aS, Finset.mul_sum, Finset.sum_range_succ', Finset.sum_range_succ _ S.length,
        QQ_vanish S (S.length + 1) (by omega), wN_zero]
      simp only [mul_zero, add_zero]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · ring
    rw [e1]
    linarith
  rw [Finset.sum_add_distrib] at h1
  have hc : 4 * (j : ℝ) * aS ρi S + 3 * ρi * (j + 1) * aS ρi S ≤ (4 + 3 * ρi) * (j + 1) * aS ρi S := by
    nlinarith
  linarith

lemma aS_le {ρi : ℝ} (hρ : 0 ≤ ρi) : ∀ S : List Bool, aS ρi S ≤ S.length ! * (4 + 3 * ρi) ^ S.length
  | [] => by simp [aS_nil]
  | z :: S => by
    have h1 := aS_cons hρ z S
    have h2 := aS_le hρ S
    have hc : 0 ≤ (4 + 3 * ρi) * (S.length + 1) := by positivity
    calc aS ρi (z :: S) ≤ (4 + 3 * ρi) * (S.length + 1) * aS ρi S := h1
      _ ≤ (4 + 3 * ρi) * (S.length + 1) * (S.length ! * (4 + 3 * ρi) ^ S.length) := mul_le_mul_of_nonneg_left h2 hc
      _ = (z :: S).length ! * (4 + 3 * ρi) ^ (z :: S).length := by
          simp only [List.length_cons, Nat.factorial_succ]
          push_cast
          ring

/-- **Word bounds for `Φ ∘ ψ̃`.** -/
theorem wb_comp {Φ : ℝ → ℝ} {A ρi : ℝ} (hρ : 0 ≤ ρi) (hA : 0 ≤ A) (hΦ : ∀ x, 0 ≤ x → ContDiffAt ℝ ∞ Φ x)
    (hb : ∀ (k : ℕ) (x : ℝ), 0 ≤ x → |iteratedDeriv k Φ x| ≤ A * k ! * ρi ^ k) :
    WB (fun u => Φ (psiF u)) A (4 + 3 * ρi) := by
  refine ⟨fun w hw => ?_, fun S w hw => ?_⟩
  · exact ContDiffAt.comp w (hΦ _ (psiF_nonneg hw)) (contDiffAt_psiF hw)
  · rw [wordR_comp hΦ S hw]
    have hx := psiF_nonneg hw
    have hξ := abs_xiF_le w
    have hυ : |upF w| ≤ 2 := by rw [abs_of_nonneg (upF_nonneg w)]; exact upF_le_two w
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ Finset.range (S.length + 1), |iteratedDeriv k Φ (psiF w) * ev (QQ S k) (xiF w) (upF w)|
        ≤ A * ((k ! : ℝ) * ρi ^ k * wN (QQ S k)) := fun k _ => by
      rw [abs_mul]
      calc _ ≤ (A * k ! * ρi ^ k) * wN (QQ S k) :=
            mul_le_mul (hb k _ hx) (abs_ev_le_wN _ hξ hυ) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    show A * aS ρi S ≤ _
    calc A * aS ρi S ≤ A * (S.length ! * (4 + 3 * ρi) ^ S.length) := mul_le_mul_of_nonneg_left (aS_le hρ S) hA
      _ = _ := by ring

end Qschubert
