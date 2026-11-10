import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Elementary inequalities used in the manuscript

* `factorial_le_stirling_upper`: `n! ≤ e √n (n/e)^n` for `n ≥ 1`.
* `cor15_core`: the computation in the proof of Corollary 1.5R (Appendix A; reused for the
  printed-class Corollary 1.5). For `0 < δ ≤ 1`, `0 < ε < 1` and an integer `K` with
  `(1-ε)/δ ≤ K ≤ (1-ε/2)/δ`: `δ^(K+1) K! ≤ e^{1/2} ε^{-1/2} e^{-(1-ε)/δ}`. Here `δ = δ_K`.
* `pow_le_factorial_two_mul`: `(N+2)^(2N+4) ≤ 34^(N+1) (2N)!`, the factorial step of
  Corollary 1.6R and of the printed-class Corollary 1.6 (the manuscript writes `C^(N+1)`).
* `deltaK_le_one`, `cor15_of_bound`: the proof of Corollary 1.5R from the form of the bound of
  Theorem 1.4R (`δ_K ≤ 1` on its window, then `cor15_core`).
* `cor16_of_bounds`: the proof of the pointwise Corollary 1.6 from the local Sobolev bound and the
  `L²` bounds at `N` and `N + 2`.
* `filter_absorb_poly`, `filter_absorb_gauss`, `filter_absorb_floor`: the absorption steps of
  the filter-split lemma of Appendix H, part (iv), case `M ≥ 2`, with `c₀ = (2 e √C₁)⁻¹`.
-/

namespace Qschubert

open Real Nat

/-- Upper Stirling bound `n! ≤ e √n (n/e)^n` for `n ≥ 1` (from the monotonicity of
`stirlingSeq` and its value `e/√2` at `1`). -/
theorem factorial_le_stirling_upper {n : ℕ} (hn : 1 ≤ n) :
    (n ! : ℝ) ≤ exp 1 * √(n : ℝ) * ((n : ℝ) / exp 1) ^ n := by
  have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le (n - 1))
  simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add, Nat.sub_add_cancel hn,
    Stirling.stirlingSeq_one] at hanti
  unfold Stirling.stirlingSeq at hanti
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < √(2 * (n : ℝ)) * ((n : ℝ) / exp 1) ^ n := by positivity
  rw [div_le_iff₀ hpos] at hanti
  calc (n ! : ℝ) ≤ exp 1 / √2 * (√(2 * (n : ℝ)) * ((n : ℝ) / exp 1) ^ n) := hanti
    _ = exp 1 * √(n : ℝ) * ((n : ℝ) / exp 1) ^ n := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have : (√2 : ℝ) ≠ 0 := by positivity
      field_simp

/-- `√x e^{-xε/2} ≤ e^{-1/2} ε^{-1/2}` for `x ≥ 0`, `ε > 0`. -/
lemma sqrt_mul_exp_le {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    √x * exp (-(x * ε / 2)) ≤ exp (-(1 / 2)) / √ε := by
  have hA : 0 ≤ √x * exp (-(x * ε / 2)) := by positivity
  have hB : 0 ≤ exp (-(1 / 2)) / √ε := by positivity
  rw [← pow_le_pow_iff_left₀ hA hB (two_ne_zero)]
  have hsq1 : (√x * exp (-(x * ε / 2))) ^ 2 = x * exp (-(x * ε)) := by
    rw [mul_pow, Real.sq_sqrt hx, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hsq2 : (exp (-(1 / 2)) / √ε) ^ 2 = exp (-1) / ε := by
    rw [div_pow, Real.sq_sqrt hε.le, ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [hsq1, hsq2, le_div_iff₀ hε]
  -- `u e^{-u} ≤ e^{-1}` with `u = xε`, from `u ≤ e^{u-1}`.
  have hu : x * ε ≤ exp (x * ε - 1) := by linarith [Real.add_one_le_exp (x * ε - 1)]
  calc x * exp (-(x * ε)) * ε = (x * ε) * exp (-(x * ε)) := by ring
    _ ≤ exp (x * ε - 1) * exp (-(x * ε)) := by gcongr
    _ = exp (-1) := by rw [← Real.exp_add]; ring_nf

/-- The computation in the proof of Corollary 1.5R: for `0 < δ ≤ 1`,
`0 < ε < 1` and `(1-ε)/δ ≤ K ≤ (1-ε/2)/δ`,
`δ^(K+1) K! ≤ e^{1/2} ε^{-1/2} e^{-(1-ε)/δ}`. -/
theorem cor15_core {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε < 1) {K : ℕ}
    (hK1 : (1 - ε) / δ ≤ K) (hK2 : (K : ℝ) ≤ (1 - ε / 2) / δ) :
    δ ^ (K + 1) * (K ! : ℝ) ≤ exp (1 / 2) / √ε * exp (-((1 - ε) / δ)) := by
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (div_pos (by linarith) hδ) hK1
  have hK1' : 1 ≤ K := by exact_mod_cast hKpos
  set k : ℝ := (K : ℝ) with hk
  have hst := factorial_le_stirling_upper hK1'
  -- `(k/e)^K = k^K e^{-k}`
  have hpow : (k / exp 1) ^ K = k ^ K * exp (-k) := by
    rw [div_pow, Real.exp_one_pow, Real.exp_neg, div_eq_mul_inv]
  -- `(kδ)^K ≤ e^{-kε/2}`
  have hkδ : k * δ ≤ 1 - ε / 2 := by rwa [le_div_iff₀ hδ] at hK2
  have hkδexp : (k * δ) ^ K ≤ exp (-(k * ε / 2)) := by
    have h1 : k * δ ≤ exp (-(ε / 2)) := by linarith [Real.add_one_le_exp (-(ε / 2))]
    calc (k * δ) ^ K ≤ exp (-(ε / 2)) ^ K := by gcongr
      _ = exp (-(k * ε / 2)) := by rw [← Real.exp_nat_mul]; congr 1; rw [hk]; ring
  have hexpK : exp (-k) ≤ exp (-((1 - ε) / δ)) := by
    apply Real.exp_le_exp.mpr; linarith
  have hsq := sqrt_mul_exp_le (x := k) hKpos.le hε
  calc δ ^ (K + 1) * (K ! : ℝ)
      ≤ δ ^ (K + 1) * (exp 1 * √k * (k / exp 1) ^ K) := by gcongr
    _ = δ * (exp 1 * exp (-k) * √k * (k * δ) ^ K) := by rw [hpow, mul_pow, pow_succ]; ring
    _ ≤ 1 * (exp 1 * exp (-k) * √k * exp (-(k * ε / 2))) := by gcongr
    _ = exp 1 * exp (-k) * (√k * exp (-(k * ε / 2))) := by ring
    _ ≤ exp 1 * exp (-k) * (exp (-(1 / 2)) / √ε) := by gcongr
    _ = exp (1 / 2) / √ε * exp (-k) := by
      rw [show exp (1 / 2) = exp 1 * exp (-(1 / 2)) by rw [← Real.exp_add]; norm_num]; ring
    _ ≤ exp (1 / 2) / √ε * exp (-((1 - ε) / δ)) := by gcongr

/-- `(N+3)^(2N+4) ≤ e² (N+2)^(2N+4)`. -/
lemma succ_pow_le_exp_two (N : ℕ) :
    ((N : ℝ) + 3) ^ (2 * N + 4) ≤ exp 2 * ((N : ℝ) + 2) ^ (2 * N + 4) := by
  have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hsplit : (N : ℝ) + 3 = ((N : ℝ) + 2) * (1 + 1 / ((N : ℝ) + 2)) := by
    field_simp; ring
  have h1 : 1 + 1 / ((N : ℝ) + 2) ≤ exp (1 / ((N : ℝ) + 2)) := by
    linarith [Real.add_one_le_exp (1 / ((N : ℝ) + 2))]
  have h2 : (1 + 1 / ((N : ℝ) + 2)) ^ (2 * N + 4) ≤ exp 2 := by
    calc (1 + 1 / ((N : ℝ) + 2)) ^ (2 * N + 4) ≤ exp (1 / ((N : ℝ) + 2)) ^ (2 * N + 4) := by
          gcongr
      _ = exp 2 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp; ring
  rw [hsplit, mul_pow, mul_comm]
  gcongr

/-- The factorial step of Corollary 1.6R and of the printed-class Corollary 1.6:
`(N+2)^(2N+4) ≤ 34^(N+1) (2N)!`. -/
theorem pow_le_factorial_two_mul (N : ℕ) : (N + 2) ^ (2 * N + 4) ≤ 34 ^ (N + 1) * (2 * N)! := by
  have key : ∀ N : ℕ, ((N : ℝ) + 2) ^ (2 * N + 4) ≤ 34 ^ (N + 1) * ((2 * N)! : ℝ) := by
    intro N
    induction N with
    | zero => norm_num
    | succ n ih =>
      have he : exp 2 ≤ 7.39 := by
        have h := Real.exp_one_lt_d9
        have : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
        rw [this]
        nlinarith [Real.exp_pos 1]
      have hfac : ((2 * (n + 1))! : ℝ) = (2 * (n : ℝ) + 2) * (2 * n + 1) * ((2 * n)! : ℝ) := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast; ring
      have hstep := succ_pow_le_exp_two n
      have hcast : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
      rw [hcast, hfac, show 2 * (n + 1) + 4 = (2 * n + 4) + 2 by ring, pow_add]
      have hA : 0 ≤ ((n : ℝ) + 2) ^ (2 * n + 4) := by positivity
      have hF : (0 : ℝ) ≤ ((2 * n)! : ℝ) := by positivity
      have hquad : ((n : ℝ) + 3) ^ 2 * exp 2 ≤ 34 * ((2 * (n : ℝ) + 2) * (2 * n + 1)) := by
        have hn0 : (0 : ℝ) ≤ n := by positivity
        have hsq : (0 : ℝ) ≤ ((n : ℝ) + 3) ^ 2 := by positivity
        nlinarith
      calc ((n : ℝ) + 3) ^ (2 * n + 4) * ((n : ℝ) + 3) ^ 2
          ≤ (exp 2 * ((n : ℝ) + 2) ^ (2 * n + 4)) * ((n : ℝ) + 3) ^ 2 := by gcongr
        _ = (((n : ℝ) + 3) ^ 2 * exp 2) * ((n : ℝ) + 2) ^ (2 * n + 4) := by ring
        _ ≤ (34 * ((2 * (n : ℝ) + 2) * (2 * n + 1))) * (34 ^ (n + 1) * ((2 * n)! : ℝ)) := by
          gcongr
        _ = 34 ^ (n + 1 + 1) * ((2 * (n : ℝ) + 2) * (2 * n + 1) * ((2 * n)! : ℝ)) := by ring
  have := key N
  exact_mod_cast this

/-- Filter split (iv), polynomial part: if `M ≤ c₀ α/ε` with `c₀ = (2 e √C₁)⁻¹`, then
`C₁^M ε^(2M) (2M)! α^(-2M) ≤ e^{-2M}`. -/
theorem filter_absorb_poly {C₁ α ε : ℝ} (hC : 0 < C₁) (hα : 0 < α) (hε : 0 < ε) {M : ℕ}
    (hM : (M : ℝ) ≤ α / (2 * exp 1 * √C₁ * ε)) :
    C₁ ^ M * ε ^ (2 * M) * ((2 * M)! : ℝ) / α ^ (2 * M) ≤ exp (-(2 * (M : ℝ))) := by
  have he : 0 < exp 1 := exp_pos 1
  have hsC : 0 < √C₁ := Real.sqrt_pos.mpr hC
  have hfac : ((2 * M)! : ℝ) ≤ ((2 * M : ℕ) : ℝ) ^ (2 * M) := by
    exact_mod_cast Nat.factorial_le_pow (2 * M)
  have hM' : (M : ℝ) * (2 * exp 1 * √C₁ * ε) ≤ α := (le_div_iff₀ (by positivity)).mp hM
  have hb : 2 * √C₁ * M * ε / α ≤ exp (-1) := by
    rw [div_le_iff₀ hα, Real.exp_neg, inv_mul_eq_div, le_div_iff₀ he]
    nlinarith [hM']
  have hb0 : 0 ≤ 2 * √C₁ * M * ε / α := by positivity
  calc C₁ ^ M * ε ^ (2 * M) * ((2 * M)! : ℝ) / α ^ (2 * M)
      ≤ C₁ ^ M * ε ^ (2 * M) * ((2 * M : ℕ) : ℝ) ^ (2 * M) / α ^ (2 * M) := by gcongr
    _ = (2 * √C₁ * M * ε / α) ^ (2 * M) := by
      rw [div_pow, mul_pow, mul_pow, mul_pow, pow_mul √C₁, Real.sq_sqrt hC.le]
      push_cast; ring
    _ ≤ exp (-1) ^ (2 * M) := by gcongr
    _ = exp (-(2 * (M : ℝ))) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf

/-- Filter split (iv), Gaussian part: under the same hypothesis,
`C₁^M (2M)! α^(-2M) ≤ ε^(-2M) e^{-2M} ≤ ε^(-2M)`. -/
theorem filter_absorb_gauss {C₁ α ε : ℝ} (hC : 0 < C₁) (hα : 0 < α) (hε : 0 < ε) {M : ℕ}
    (hM : (M : ℝ) ≤ α / (2 * exp 1 * √C₁ * ε)) :
    C₁ ^ M * ((2 * M)! : ℝ) / α ^ (2 * M) ≤ (ε ^ (2 * M))⁻¹ := by
  have h := filter_absorb_poly hC hα hε hM
  have hεM : 0 < ε ^ (2 * M) := by positivity
  have hle1 : exp (-(2 * (M : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : (0 : ℝ) ≤ M := by positivity
    linarith
  have h1 : C₁ ^ M * ε ^ (2 * M) * ((2 * M)! : ℝ) / α ^ (2 * M) ≤ 1 := h.trans hle1
  have e : C₁ ^ M * ((2 * M)! : ℝ) / α ^ (2 * M)
      = (C₁ ^ M * ε ^ (2 * M) * ((2 * M)! : ℝ) / α ^ (2 * M)) / ε ^ (2 * M) := by
    field_simp
  rw [e, div_le_iff₀ hεM, inv_mul_cancel₀ hεM.ne']
  exact h1

/-- Filter split (iv): if `c₀ α/ε < M + 1`, then `e^{-2M} ≤ e² e^{-2 c₀ α/ε}`. -/
theorem filter_absorb_floor {x : ℝ} {M : ℕ} (hx : x < M + 1) :
    exp (-(2 * (M : ℝ))) ≤ exp 2 * exp (-(2 * x)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- `δ_K := Cħt/α² ≤ 1` on the window of Theorem 1.4R (the last step of the proof of
Corollary 1.5R): from `t ≤ δ (α/ħ)^{1/2}`, `κħ ≤ α³` and `δ ≤ κ^{1/2}/max(1, C)`. -/
theorem deltaK_le_one {C κ δ ħ t α : ℝ} (hC : 0 < C) (hκ : 0 < κ) (hħ : 0 < ħ) (hα : 0 < α)
    (ht : 0 ≤ t) (htδ : t ≤ δ * √(α / ħ)) (hακ : κ * ħ ≤ α ^ 3) (hδ : δ ≤ √κ / max 1 C) :
    C * ħ * t / α ^ 2 ≤ 1 := by
  have hδ0 : 0 ≤ δ :=
    (mul_nonneg_iff_of_pos_right (Real.sqrt_pos.mpr (by positivity))).mp (ht.trans htδ)
  have hsκ : 0 < √κ := Real.sqrt_pos.mpr hκ
  -- `ħ t ≤ δ √(αħ)`
  have h1 : ħ * t ≤ δ * √(α * ħ) := by
    calc ħ * t ≤ ħ * (δ * √(α / ħ)) := by gcongr
      _ = δ * √(α * ħ) := by
        have : √(α * ħ) = ħ * √(α / ħ) := by
          rw [show α * ħ = ħ ^ 2 * (α / ħ) by field_simp, Real.sqrt_mul (by positivity),
            Real.sqrt_sq hħ.le]
        rw [this]; ring
  -- `√(αħ) / α² = √(ħ/α³) ≤ 1/√κ`
  have h2 : √(α * ħ) / α ^ 2 ≤ 1 / √κ := by
    have hq : ħ / α ^ 3 ≤ 1 / κ := by
      rw [div_le_div_iff₀ (by positivity) hκ]; linarith
    have hsq : √(α * ħ) / α ^ 2 = √(ħ / α ^ 3) := by
      rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      have hs : √(α * ħ) * √(α * ħ) = α * ħ := Real.mul_self_sqrt (by positivity)
      rw [show √(α * ħ) / α ^ 2 * (√(α * ħ) / α ^ 2) = (√(α * ħ) * √(α * ħ)) / (α ^ 2 * α ^ 2) by
        ring, hs]
      field_simp
    rw [hsq, show (1 : ℝ) / √κ = √(1 / κ) by rw [Real.sqrt_div' 1 hκ.le, Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hq
  have hmax : C / max 1 C ≤ 1 := by
    rw [div_le_one (lt_of_lt_of_le one_pos (le_max_left 1 C))]; exact le_max_right 1 C
  calc C * ħ * t / α ^ 2 = C * (ħ * t) / α ^ 2 := by ring
    _ ≤ C * (δ * √(α * ħ)) / α ^ 2 := by gcongr
    _ = C * δ * (√(α * ħ) / α ^ 2) := by ring
    _ ≤ C * δ * (1 / √κ) := by gcongr
    _ ≤ C * (√κ / max 1 C) * (1 / √κ) := by gcongr
    _ = C / max 1 C := by field_simp
    _ ≤ 1 := hmax

/-- The proof of Corollary 1.5R from the form of the bound of Theorem 1.4R: if
`E K ≤ A C^(K+1) K! (ħt/α²)^(K+1)` for every `K`, then on the window
`(1-ε)/δ_K ≤ K ≤ (1-ε/2)/δ_K`, `δ_K = Cħt/α² ≤ 1`,
`E K ≤ A e^{1/2} ε^{-1/2} e^{-(1-ε)α²/(Cħt)}`. In the manuscript
`A = C^N N^(2N) (αħ)^(-2N) ‖a‖`. -/
theorem cor15_of_bound {A C ħ t α ε : ℝ} (hA : 0 ≤ A) (hC : 0 < C) (hħ : 0 < ħ) (ht : 0 < t)
    (hα : 0 < α) (hδ1 : C * ħ * t / α ^ 2 ≤ 1) (hε : 0 < ε) (hε1 : ε < 1) {E : ℕ → ℝ}
    (hE : ∀ K, E K ≤ A * C ^ (K + 1) * (K ! : ℝ) * (ħ * t / α ^ 2) ^ (K + 1)) {K : ℕ}
    (hK1 : (1 - ε) / (C * ħ * t / α ^ 2) ≤ K) (hK2 : (K : ℝ) ≤ (1 - ε / 2) / (C * ħ * t / α ^ 2)) :
    E K ≤ A * (exp (1 / 2) / √ε) * exp (-((1 - ε) * α ^ 2 / (C * ħ * t))) := by
  have hδ : 0 < C * ħ * t / α ^ 2 := by positivity
  have core := cor15_core hδ hδ1 hε hε1 hK1 hK2
  have heq : C ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1) = (C * ħ * t / α ^ 2) ^ (K + 1) := by
    rw [← mul_pow]; congr 1; ring
  have hexp : (1 - ε) / (C * ħ * t / α ^ 2) = (1 - ε) * α ^ 2 / (C * ħ * t) := by
    field_simp
  calc E K ≤ A * C ^ (K + 1) * (K ! : ℝ) * (ħ * t / α ^ 2) ^ (K + 1) := hE K
    _ = A * ((C * ħ * t / α ^ 2) ^ (K + 1) * (K ! : ℝ)) := by rw [← heq]; ring
    _ ≤ A * (exp (1 / 2) / √ε * exp (-((1 - ε) / (C * ħ * t / α ^ 2)))) := by gcongr
    _ = A * (exp (1 / 2) / √ε) * exp (-((1 - ε) * α ^ 2 / (C * ħ * t))) := by rw [hexp]; ring

/-- The proof of the pointwise Corollary 1.6 (printed class, and Corollary 1.6R): from the local
Sobolev bound `S ≤ C_S √m (P + Q)`, the `L²` bounds at `N + 2` and at `N`
(`P ≤ C^(N+K+3) (N+2)^(2N+4) K! (αħ)^(-2N-4) τ^(K+1) A`,
`Q ≤ C^(N+K+1) N^(2N) K! (αħ)^(-2N) τ^(K+1) A`) and `0 < αħ ≤ 1`, `C ≥ 1`:
`S ≤ (2 C_S C²) √m (34 C)^(N+K+1) (2N)! K! (αħ)^(-2N-4) τ^(K+1) A`. -/
theorem cor16_of_bounds {S P Q CS C m αħ τ A : ℝ} {N K : ℕ} (hCS : 0 ≤ CS) (hC : 1 ≤ C)
    (hαħ0 : 0 < αħ) (hαħ : αħ ≤ 1) (hτ : 0 ≤ τ) (hA : 0 ≤ A)
    (hS : S ≤ CS * √m * (P + Q))
    (hP : P ≤ C ^ (N + K + 3) * ((N + 2 : ℕ) : ℝ) ^ (2 * N + 4) * (K ! : ℝ) * (αħ ^ (2 * N + 4))⁻¹
      * τ ^ (K + 1) * A)
    (hQ : Q ≤ C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K ! : ℝ) * (αħ ^ (2 * N))⁻¹ * τ ^ (K + 1) * A) :
    S ≤ (2 * CS * C ^ 2) * √m * (34 * C) ^ (N + K + 1) * ((2 * N)! : ℝ) * (K ! : ℝ)
      * (αħ ^ (2 * N + 4))⁻¹ * τ ^ (K + 1) * A := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hfac : (((N + 2 : ℕ) : ℝ)) ^ (2 * N + 4) ≤ 34 ^ (N + 1) * ((2 * N)! : ℝ) := by
    exact_mod_cast pow_le_factorial_two_mul N
  have hNN : (N : ℝ) ^ (2 * N) ≤ ((N + 2 : ℕ) : ℝ) ^ (2 * N + 4) := by
    calc (N : ℝ) ^ (2 * N) ≤ ((N + 2 : ℕ) : ℝ) ^ (2 * N) := by gcongr; linarith
      _ ≤ ((N + 2 : ℕ) : ℝ) ^ (2 * N + 4) := by
          apply pow_le_pow_right₀ (by push_cast; linarith) (by omega)
  have hαinv : (αħ ^ (2 * N))⁻¹ ≤ (αħ ^ (2 * N + 4))⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_of_le_one hαħ0.le hαħ (by omega)
  have hCpow : C ^ (N + K + 1) ≤ C ^ (N + K + 3) := pow_le_pow_right₀ hC (by omega)
  set R : ℝ := (K ! : ℝ) * (αħ ^ (2 * N + 4))⁻¹ * τ ^ (K + 1) * A with hR
  have hR0 : 0 ≤ R := by positivity
  have hP' : P ≤ C ^ (N + K + 3) * (34 ^ (N + 1) * ((2 * N)! : ℝ)) * R := by
    calc P ≤ C ^ (N + K + 3) * ((N + 2 : ℕ) : ℝ) ^ (2 * N + 4) * (K ! : ℝ)
          * (αħ ^ (2 * N + 4))⁻¹ * τ ^ (K + 1) * A := hP
      _ = C ^ (N + K + 3) * ((N + 2 : ℕ) : ℝ) ^ (2 * N + 4) * R := by rw [hR]; ring
      _ ≤ C ^ (N + K + 3) * (34 ^ (N + 1) * ((2 * N)! : ℝ)) * R := by gcongr
  have hQ' : Q ≤ C ^ (N + K + 3) * (34 ^ (N + 1) * ((2 * N)! : ℝ)) * R := by
    calc Q ≤ C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K ! : ℝ) * (αħ ^ (2 * N))⁻¹
          * τ ^ (K + 1) * A := hQ
      _ ≤ C ^ (N + K + 3) * ((N + 2 : ℕ) : ℝ) ^ (2 * N + 4) * (K ! : ℝ)
          * (αħ ^ (2 * N + 4))⁻¹ * τ ^ (K + 1) * A := by gcongr
      _ = C ^ (N + K + 3) * ((N + 2 : ℕ) : ℝ) ^ (2 * N + 4) * R := by rw [hR]; ring
      _ ≤ C ^ (N + K + 3) * (34 ^ (N + 1) * ((2 * N)! : ℝ)) * R := by gcongr
  have h34 : (34 : ℝ) ^ (N + 1) ≤ 34 ^ (N + K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  calc S ≤ CS * √m * (P + Q) := hS
    _ ≤ CS * √m * (2 * (C ^ (N + K + 3) * (34 ^ (N + 1) * ((2 * N)! : ℝ)) * R)) := by
        gcongr; linarith
    _ ≤ CS * √m * (2 * (C ^ (N + K + 3) * (34 ^ (N + K + 1) * ((2 * N)! : ℝ)) * R)) := by
        gcongr
    _ = (2 * CS * C ^ 2) * √m * (34 * C) ^ (N + K + 1) * ((2 * N)! : ℝ) * (K ! : ℝ)
      * (αħ ^ (2 * N + 4))⁻¹ * τ ^ (K + 1) * A := by
        rw [hR, mul_pow, show N + K + 3 = (N + K + 1) + 2 by omega, pow_add]; ring

end Qschubert
