import Qschubert.KLDDFinal

/-!
# Collecting the remainder bound (Lemma `lem:collect`)

The proofs of Theorem `thm:dd-appx` and Proposition `pc:core` end with the same arithmetic: a bound
`Φ ≤ B (F₀ + ħ t e^{γt} ε^{-3} σ^{-4} e^{-cξ} F₂)` for the integrand of the remainder over the simplex, with
`ε = (σħ)^{1/2}/2`, `ξ = (σ/ħ)^{1/2}` and `F_n = G^{N+K+n+1} (2N)! (n+2K+2)! σ^{-(n+2K+2)} (σħ)^{-2N} H`, gives, after
multiplication by `(ħ/2)^{K+1}` and the simplex volume `t^{K+1}/(K+1)!`, the bound `C^{N+K+1} N^{2N} K! (σħ)^{-2N}
(ħt/σ²)^{K+1} H` on the window `t ≤ δ ξ`, `δ ≤ 1`, `2γδ ≤ c`.

* `remF`: the numbers `F_n`.
* `collect_absorb`: the transport growth and the powers of `ε, σ` are absorbed by `e^{-cξ}`.
* `remF_zero_le`: `F₀ ≤ σ² F₂`.
* `collect_final`: the factorial and power count.
* `collect_remainder`: Lemma `lem:collect`.
-/

namespace Qschubert

/-- `F_n = G^{N+K+n+1} (2N)! (n+2K+2)! σ^{-(n+2K+2)} (σħ)^{-2N} H`. -/
noncomputable def remF (G σ ħ H : ℝ) (K N n : ℕ) : ℝ :=
  G ^ (N + K + n + 1) * ((2 * N).factorial : ℝ) * ((n + 2 * K + 2).factorial : ℝ) * (σ⁻¹) ^ (n + 2 * K + 2)
    * ((σ * ħ)⁻¹) ^ (2 * N) * H

lemma remF_nonneg {G σ ħ H : ℝ} {K N n : ℕ} (hG : 1 ≤ G) (hσ : 0 < σ) (hħ : 0 < ħ) (hH : 0 ≤ H) :
    0 ≤ remF G σ ħ H K N n := by
  unfold remF
  have : 0 ≤ G := by linarith
  positivity

/-- The absorption step: on the window `t ≤ δ ξ` with `δ ≤ 1` and `2γδ ≤ c`,
`ħ t e^{γt} ε^{-3} σ^{-4} e^{-cξ} ≤ 8 κ^{-4} 10! (2/c)^{10} σ²`. -/
lemma collect_absorb {κ γ c ħ σ δ t : ℝ} (hκ : 0 < κ) (hγ : 0 ≤ γ) (hc : 0 < c) (hħ : 0 < ħ) (hσ : 0 < σ)
    (hκσ : κ * ħ ≤ σ ^ 3) (hδ1 : δ ≤ 1) (hγδ : 2 * γ * δ ≤ c) (_ht : 0 ≤ t)
    (htδ : t ≤ δ * Real.sqrt (σ / ħ)) :
    ħ * t * Real.exp (γ * t) * ((Real.sqrt (σ * ħ) / 2)⁻¹) ^ 3 * (σ⁻¹) ^ 4 * Real.exp (-(c * Real.sqrt (σ / ħ)))
      ≤ (8 * (κ ^ 4)⁻¹ * ((Nat.factorial 10 : ℕ) : ℝ) * (2 / c) ^ 10) * σ ^ 2 := by
  have hħne : ħ ≠ 0 := hħ.ne'
  have hσne : σ ≠ 0 := hσ.ne'
  have hσħ : 0 < σ / ħ := div_pos hσ hħ
  set ξ := Real.sqrt (σ / ħ) with hξd
  have hξ0 : 0 < ξ := Real.sqrt_pos.2 hσħ
  have hξ2 : ξ ^ 2 = σ / ħ := Real.sq_sqrt hσħ.le
  have hħξ : ħ * ξ ^ 2 = σ := by rw [hξ2]; field_simp
  have hs1 : Real.sqrt (σ * ħ) * ξ = σ := by
    rw [hξd, ← Real.sqrt_mul (by positivity) (σ / ħ)]
    have e : σ * ħ * (σ / ħ) = σ ^ 2 := by field_simp
    rw [e]
    exact Real.sqrt_sq hσ.le
  have hs : Real.sqrt (σ * ħ) = σ / ξ := by
    rw [eq_div_iff hξ0.ne']
    exact hs1
  have e1 : (Real.sqrt (σ * ħ) / 2)⁻¹ = 2 * ξ * σ⁻¹ := by
    rw [hs]
    field_simp
  -- the window
  have htξ : t ≤ ξ := htδ.trans (mul_le_of_le_one_left hξ0.le hδ1)
  have hexp : Real.exp (γ * t) * Real.exp (-(c * ξ)) ≤ Real.exp (-(c * ξ / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : γ * t ≤ γ * (δ * ξ) := mul_le_mul_of_nonneg_left htδ hγ
    have h2 : 2 * γ * δ * ξ ≤ c * ξ := mul_le_mul_of_nonneg_right hγδ hξ0.le
    nlinarith
  -- `σ^{-8} ≤ ξ^8 κ^{-4}`
  have hk1 : κ ≤ σ ^ 2 * ξ ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hκσ (sq_nonneg ξ)
    have e : κ * ħ * ξ ^ 2 = κ * σ := by rw [mul_assoc, hħξ]
    rw [e] at h
    have h' : σ * κ ≤ σ * (σ ^ 2 * ξ ^ 2) := by
      calc σ * κ = κ * σ := by ring
        _ ≤ σ ^ 3 * ξ ^ 2 := h
        _ = σ * (σ ^ 2 * ξ ^ 2) := by ring
    exact le_of_mul_le_mul_left h' hσ
  have hk4 : κ ^ 4 ≤ (σ ^ 2 * ξ ^ 2) ^ 4 := pow_le_pow_left₀ hκ.le hk1 4
  have h8 : (σ⁻¹) ^ 8 * κ ^ 4 ≤ ξ ^ 8 := by
    calc (σ⁻¹) ^ 8 * κ ^ 4 ≤ (σ⁻¹) ^ 8 * (σ ^ 2 * ξ ^ 2) ^ 4 := by gcongr
      _ = ξ ^ 8 * (σ⁻¹ * σ) ^ 8 := by ring
      _ = ξ ^ 8 := by rw [inv_mul_cancel₀ hσne, one_pow, mul_one]
  have hs8 : (σ⁻¹) ^ 8 ≤ ξ ^ 8 * (κ ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact h8
  -- `ξ^{10} e^{-cξ/2} ≤ 10! (2/c)^{10}`
  have hfac : (0 : ℝ) < ((Nat.factorial 10 : ℕ) : ℝ) := by positivity
  have hx : 0 ≤ c * ξ / 2 := by positivity
  have hpe := Real.pow_div_factorial_le_exp (c * ξ / 2) hx 10
  have hpe' : (c * ξ / 2) ^ 10 ≤ ((Nat.factorial 10 : ℕ) : ℝ) * Real.exp (c * ξ / 2) := by
    rw [div_le_iff₀ hfac] at hpe
    linarith
  have hξ10 : ξ ^ 10 * Real.exp (-(c * ξ / 2)) ≤ ((Nat.factorial 10 : ℕ) : ℝ) * (2 / c) ^ 10 := by
    have e : ξ ^ 10 = (2 / c) ^ 10 * (c * ξ / 2) ^ 10 := by
      rw [← mul_pow]
      congr 1
      field_simp
    have hE : Real.exp (c * ξ / 2) * Real.exp (-(c * ξ / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ξ ^ 10 * Real.exp (-(c * ξ / 2)) = (2 / c) ^ 10 * ((c * ξ / 2) ^ 10 * Real.exp (-(c * ξ / 2))) := by
          rw [e]; ring
      _ ≤ (2 / c) ^ 10 * ((((Nat.factorial 10 : ℕ) : ℝ) * Real.exp (c * ξ / 2)) * Real.exp (-(c * ξ / 2))) := by
          gcongr
      _ = ((Nat.factorial 10 : ℕ) : ℝ) * (2 / c) ^ 10 := by
          rw [mul_assoc (((Nat.factorial 10 : ℕ) : ℝ)), hE]; ring
  have hσ26 : σ ^ 2 * (σ⁻¹) ^ 8 = (σ⁻¹) ^ 6 := by
    have h2 : σ ^ 2 * (σ⁻¹) ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hσne, one_pow]
    calc σ ^ 2 * (σ⁻¹) ^ 8 = (σ⁻¹) ^ 6 * (σ ^ 2 * (σ⁻¹) ^ 2) := by ring
      _ = (σ⁻¹) ^ 6 := by rw [h2, mul_one]
  rw [e1]
  calc ħ * t * Real.exp (γ * t) * (2 * ξ * σ⁻¹) ^ 3 * (σ⁻¹) ^ 4 * Real.exp (-(c * ξ))
      = (ħ * t) * (Real.exp (γ * t) * Real.exp (-(c * ξ))) * (8 * ξ ^ 3 * (σ⁻¹) ^ 7) := by ring
    _ ≤ (ħ * ξ) * Real.exp (-(c * ξ / 2)) * (8 * ξ ^ 3 * (σ⁻¹) ^ 7) := by
        gcongr
    _ = 8 * (ħ * ξ ^ 2) * ξ ^ 2 * (σ⁻¹) ^ 7 * Real.exp (-(c * ξ / 2)) := by ring
    _ = 8 * ξ ^ 2 * (σ⁻¹) ^ 6 * Real.exp (-(c * ξ / 2)) * (σ * σ⁻¹) := by rw [hħξ]; ring
    _ = 8 * ξ ^ 2 * (σ⁻¹) ^ 6 * Real.exp (-(c * ξ / 2)) := by rw [mul_inv_cancel₀ hσne, mul_one]
    _ = 8 * σ ^ 2 * (ξ ^ 2 * (σ⁻¹) ^ 8) * Real.exp (-(c * ξ / 2)) := by rw [← hσ26]; ring
    _ ≤ 8 * σ ^ 2 * (ξ ^ 2 * (ξ ^ 8 * (κ ^ 4)⁻¹)) * Real.exp (-(c * ξ / 2)) := by gcongr
    _ = 8 * σ ^ 2 * (κ ^ 4)⁻¹ * (ξ ^ 10 * Real.exp (-(c * ξ / 2))) := by ring
    _ ≤ 8 * σ ^ 2 * (κ ^ 4)⁻¹ * (((Nat.factorial 10 : ℕ) : ℝ) * (2 / c) ^ 10) := by gcongr
    _ = (8 * (κ ^ 4)⁻¹ * ((Nat.factorial 10 : ℕ) : ℝ) * (2 / c) ^ 10) * σ ^ 2 := by ring

/-- `F₀ ≤ σ² F₂`. -/
lemma remF_zero_le {G σ ħ H : ℝ} {K N : ℕ} (hG : 1 ≤ G) (hσ : 0 < σ) (hħ : 0 < ħ) (hH : 0 ≤ H) :
    remF G σ ħ H K N 0 ≤ σ ^ 2 * remF G σ ħ H K N 2 := by
  unfold remF
  have hG0 : 0 ≤ G := by linarith
  have h1 : G ^ (N + K + 0 + 1) ≤ G ^ (N + K + 2 + 1) := pow_le_pow_right₀ hG (by omega)
  have h2 : ((0 + 2 * K + 2).factorial : ℝ) ≤ ((2 + 2 * K + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hσ2 : σ ^ 2 * (σ⁻¹) ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hσ.ne', one_pow]
  have e : σ ^ 2 * (σ⁻¹) ^ (2 + 2 * K + 2) = (σ⁻¹) ^ (0 + 2 * K + 2) := by
    rw [show 2 + 2 * K + 2 = (0 + 2 * K + 2) + 2 by omega, pow_add]
    calc σ ^ 2 * ((σ⁻¹) ^ (0 + 2 * K + 2) * (σ⁻¹) ^ 2) = (σ⁻¹) ^ (0 + 2 * K + 2) * (σ ^ 2 * (σ⁻¹) ^ 2) := by ring
      _ = _ := by rw [hσ2, mul_one]
  calc G ^ (N + K + 0 + 1) * ((2 * N).factorial : ℝ) * ((0 + 2 * K + 2).factorial : ℝ) * (σ⁻¹) ^ (0 + 2 * K + 2)
        * ((σ * ħ)⁻¹) ^ (2 * N) * H
      ≤ G ^ (N + K + 2 + 1) * ((2 * N).factorial : ℝ) * ((2 + 2 * K + 2).factorial : ℝ) * (σ⁻¹) ^ (0 + 2 * K + 2)
        * ((σ * ħ)⁻¹) ^ (2 * N) * H := by gcongr
    _ = σ ^ 2 * (G ^ (N + K + 2 + 1) * ((2 * N).factorial : ℝ) * ((2 + 2 * K + 2).factorial : ℝ)
        * (σ⁻¹) ^ (2 + 2 * K + 2) * ((σ * ħ)⁻¹) ^ (2 * N) * H) := by rw [← e]; ring

/-- The final count: `(ħ/2)^{K+1} t^{K+1}/(K+1)! · B' σ² F₂ ≤ ddBound (64 max(1, 4B') G³) σ ħ t K N · H`. -/
lemma collect_final {G B' σ ħ t H : ℝ} {K N : ℕ} (hG : 1 ≤ G) (hB' : 0 ≤ B') (hσ : 0 < σ) (hħ : 0 < ħ)
    (ht : 0 ≤ t) (hH : 0 ≤ H) :
    (ħ / 2) ^ (K + 1) * (t ^ (K + 1) / ((K + 1).factorial : ℝ)) * (B' * (σ ^ 2 * remF G σ ħ H K N 2))
      ≤ ddBound (64 * max 1 (4 * B') * G ^ 3) σ ħ t K N * H := by
  set m := N + K + 1 with hm
  have hm1 : m ≠ 0 := by omega
  set D := max 1 (4 * B') with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  have hG0 : 0 ≤ G := by linarith
  set T := (ħ * t / σ ^ 2) ^ (K + 1) with hT
  have hT0 : 0 ≤ T := by positivity
  set X := ((σ * ħ)⁻¹) ^ (2 * N) with hX
  have hX0 : 0 ≤ X := by positivity
  have hFk : (0 : ℝ) < ((K + 1).factorial : ℝ) := by positivity
  have hσne : σ ≠ 0 := hσ.ne'
  -- the powers of σ, ħ, t
  have hσp : σ ^ 2 * (σ⁻¹) ^ (2 + 2 * K + 2) = (σ⁻¹) ^ (2 * (K + 1)) := by
    have hσ2 : σ ^ 2 * (σ⁻¹) ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hσne, one_pow]
    rw [show 2 + 2 * K + 2 = 2 * (K + 1) + 2 by omega, pow_add]
    calc σ ^ 2 * ((σ⁻¹) ^ (2 * (K + 1)) * (σ⁻¹) ^ 2) = (σ⁻¹) ^ (2 * (K + 1)) * (σ ^ 2 * (σ⁻¹) ^ 2) := by ring
      _ = _ := by rw [hσ2, mul_one]
  have eT : (ħ / 2) ^ (K + 1) * ((σ⁻¹) ^ (2 * (K + 1)) * t ^ (K + 1)) = (1 / 2) ^ (K + 1) * T := by
    rw [hT, pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]
    congr 1
    field_simp
  have hfact : ((2 + 2 * K + 2).factorial : ℝ) / ((K + 1).factorial : ℝ) ≤ 4 * 32 ^ (K + 1) * (K.factorial : ℝ) := by
    rw [div_le_iff₀ hFk, show 2 + 2 * K + 2 = 2 + 2 * (K + 1) by omega]
    refine (fact_ratio_le K).trans (le_of_eq ?_)
    ring
  have h2N := two_mul_fact_le N
  have hcore : (1 / 2 : ℝ) ^ (K + 1) * (B' * G ^ (N + K + 2 + 1) * ((2 * N).factorial : ℝ)
        * (((2 + 2 * K + 2).factorial : ℝ) / ((K + 1).factorial : ℝ)))
      ≤ (64 * D * G ^ 3) ^ m * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) := by
    have hNN : (0 : ℝ) ≤ (N : ℝ) ^ (2 * N) := by positivity
    have hKf : (0 : ℝ) ≤ (K.factorial : ℝ) := by positivity
    have hh : (1 / 2 : ℝ) ^ (K + 1) * 32 ^ (K + 1) = 16 ^ (K + 1) := by
      rw [← mul_pow]; norm_num
    have a1 : 4 * B' ≤ D ^ m := (le_max_right _ _).trans (le_self_pow₀ hD1 hm1)
    have a2 : G ^ (N + K + 2 + 1) ≤ (G ^ 3) ^ m := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hG (by omega)
    have a3 : (4 : ℝ) ^ N * 16 ^ (K + 1) ≤ 64 ^ m := by
      have : (64 : ℝ) ^ m = 64 ^ N * 64 ^ (K + 1) := by rw [hm, add_assoc, pow_add]
      rw [this]
      have b1 : (4 : ℝ) ^ N ≤ 64 ^ N := pow_le_pow_left₀ (by norm_num) (by norm_num) N
      have b2 : (16 : ℝ) ^ (K + 1) ≤ 64 ^ (K + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      exact mul_le_mul b1 b2 (by positivity) (by positivity)
    have hB0 : 0 ≤ B' * G ^ (N + K + 2 + 1) := by positivity
    calc (1 / 2 : ℝ) ^ (K + 1) * (B' * G ^ (N + K + 2 + 1) * ((2 * N).factorial : ℝ)
          * (((2 + 2 * K + 2).factorial : ℝ) / ((K + 1).factorial : ℝ)))
        ≤ (1 / 2 : ℝ) ^ (K + 1) * (B' * G ^ (N + K + 2 + 1) * (4 ^ N * (N : ℝ) ^ (2 * N))
          * (4 * 32 ^ (K + 1) * (K.factorial : ℝ))) := by gcongr
      _ = (4 * B') * G ^ (N + K + 2 + 1) * ((4 : ℝ) ^ N * ((1 / 2 : ℝ) ^ (K + 1) * 32 ^ (K + 1)))
          * ((N : ℝ) ^ (2 * N) * (K.factorial : ℝ)) := by ring
      _ = (4 * B') * G ^ (N + K + 2 + 1) * ((4 : ℝ) ^ N * 16 ^ (K + 1)) * ((N : ℝ) ^ (2 * N) * (K.factorial : ℝ)) := by
          rw [hh]
      _ ≤ D ^ m * (G ^ 3) ^ m * (64 : ℝ) ^ m * ((N : ℝ) ^ (2 * N) * (K.factorial : ℝ)) := by
          gcongr
      _ = (64 * D * G ^ 3) ^ m * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) := by
          rw [mul_pow, mul_pow]; ring
  have eL : (ħ / 2) ^ (K + 1) * (t ^ (K + 1) / ((K + 1).factorial : ℝ)) * (B' * (σ ^ 2 * remF G σ ħ H K N 2))
      = ((ħ / 2) ^ (K + 1) * ((σ⁻¹) ^ (2 * (K + 1)) * t ^ (K + 1))) * X * H
        * (B' * G ^ (N + K + 2 + 1) * ((2 * N).factorial : ℝ) * (((2 + 2 * K + 2).factorial : ℝ) / ((K + 1).factorial : ℝ))) := by
    unfold remF
    rw [← hσp, ← hX]
    ring
  rw [eL, eT]
  unfold ddBound
  rw [← hm, ← hX, ← hT]
  have hp : 0 ≤ T * X * H := by positivity
  calc (1 / 2) ^ (K + 1) * T * X * H * (B' * G ^ (N + K + 2 + 1) * ((2 * N).factorial : ℝ)
        * (((2 + 2 * K + 2).factorial : ℝ) / ((K + 1).factorial : ℝ)))
      = (T * X * H) * ((1 / 2) ^ (K + 1) * (B' * G ^ (N + K + 2 + 1) * ((2 * N).factorial : ℝ)
        * (((2 + 2 * K + 2).factorial : ℝ) / ((K + 1).factorial : ℝ)))) := by ring
    _ ≤ (T * X * H) * ((64 * D * G ^ 3) ^ m * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ)) := by gcongr
    _ = _ := by ring

/-- **Lemma `lem:collect`** (collecting the remainder bound). Let `κ > 0`, `γ ≥ 0`, `c > 0`, `G ≥ 1`, `B ≥ 0`. There is
`C > 0`, depending only on these, such that for `0 < ħ ≤ 1`, `0 < σ ≤ 1` with `σ³ ≥ κħ`, `0 < δ ≤ 1` with `2γδ ≤ c`,
`0 ≤ t ≤ δ (σ/ħ)^{1/2}`, `K, N` and `H ≥ 0`, every number `Φ` with
`Φ ≤ B (F₀ + ħ t e^{γt} ε^{-3} σ^{-4} e^{-cξ} F₂)`, `ε = (σħ)^{1/2}/2`, `ξ = (σ/ħ)^{1/2}`, satisfies
`(ħ/2)^{K+1} t^{K+1}/(K+1)! · Φ ≤ C^{N+K+1} N^{2N} K! (σħ)^{-2N} (ħt/σ²)^{K+1} H`. -/
def Stmt_collect_remainder : Prop :=
  ∀ (κ γ c G B : ℝ), 0 < κ → 0 ≤ γ → 0 < c → 1 ≤ G → 0 ≤ B →
  ∃ C : ℝ, 0 < C ∧ ∀ (ħ σ δ t H Φ : ℝ) (K N : ℕ),
    0 < ħ → ħ ≤ 1 → 0 < σ → σ ≤ 1 → κ * ħ ≤ σ ^ 3 → 0 < δ → δ ≤ 1 → 2 * γ * δ ≤ c →
    0 ≤ t → t ≤ δ * Real.sqrt (σ / ħ) → 0 ≤ H →
    Φ ≤ B * (remF G σ ħ H K N 0 + ħ * t * Real.exp (γ * t) * ((Real.sqrt (σ * ħ) / 2)⁻¹) ^ 3 * (σ⁻¹) ^ 4
          * Real.exp (-(c * Real.sqrt (σ / ħ))) * remF G σ ħ H K N 2) →
    (ħ / 2) ^ (K + 1) * (t ^ (K + 1) / ((K + 1).factorial : ℝ)) * Φ ≤ ddBound C σ ħ t K N * H

theorem collect_remainder : Stmt_collect_remainder := by
  intro κ γ c G B hκ hγ hc hG hB
  set CR : ℝ := 8 * (κ ^ 4)⁻¹ * ((Nat.factorial 10 : ℕ) : ℝ) * (2 / c) ^ 10 with hCR
  have hCR0 : 0 ≤ CR := by positivity
  have hG0 : 0 ≤ G := by linarith
  refine ⟨64 * max 1 (4 * (B * (1 + CR))) * G ^ 3,
    mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le one_pos (le_max_left _ _))) (by positivity), ?_⟩
  intro ħ σ δ t H Φ K N hħ _hħ1 hσ _hσ1 hκσ _hδ hδ1 hγδ ht htδ hH hΦ
  have hR := collect_absorb hκ hγ hc hħ hσ hκσ hδ1 hγδ ht htδ
  have hF2 : 0 ≤ remF G σ ħ H K N 2 := remF_nonneg hG hσ hħ hH
  have hF0 := remF_zero_le (K := K) (N := N) hG hσ hħ hH
  have hΦ' : Φ ≤ (B * (1 + CR)) * (σ ^ 2 * remF G σ ħ H K N 2) := by
    refine hΦ.trans ?_
    calc B * (remF G σ ħ H K N 0 + ħ * t * Real.exp (γ * t) * ((Real.sqrt (σ * ħ) / 2)⁻¹) ^ 3 * (σ⁻¹) ^ 4
          * Real.exp (-(c * Real.sqrt (σ / ħ))) * remF G σ ħ H K N 2)
        ≤ B * (σ ^ 2 * remF G σ ħ H K N 2 + (CR * σ ^ 2) * remF G σ ħ H K N 2) := by gcongr
      _ = (B * (1 + CR)) * (σ ^ 2 * remF G σ ħ H K N 2) := by ring
  have hpre : 0 ≤ (ħ / 2) ^ (K + 1) * (t ^ (K + 1) / ((K + 1).factorial : ℝ)) := by positivity
  calc (ħ / 2) ^ (K + 1) * (t ^ (K + 1) / ((K + 1).factorial : ℝ)) * Φ
      ≤ (ħ / 2) ^ (K + 1) * (t ^ (K + 1) / ((K + 1).factorial : ℝ)) * ((B * (1 + CR)) * (σ ^ 2 * remF G σ ħ H K N 2)) :=
        mul_le_mul_of_nonneg_left hΦ' hpre
    _ ≤ ddBound (64 * max 1 (4 * (B * (1 + CR))) * G ^ 3) σ ħ t K N * H :=
        collect_final hG (by positivity) hσ hħ ht hH

end Qschubert
