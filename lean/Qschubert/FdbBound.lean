import Qschubert.FdbWord
import Qschubert.LemmaTGeom
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The Faà di Bruno bound (`lem:fdb`)

**Lemma FDB.** For `β ≥ 0` there is `B_β` such that for every word `Z_S` of length `j` in
`X = y∂ₓ`, `Y = y∂_y` and every `z ∈ ℍ`:

  `|X₀^β Z_S X₀^{-β}|(z) ≤ B_β j! ρ_β^{-j}`,  `ρ_β = ¼ log(3/2)`  (`fdb`),

with `X₀ = cosh d(i, ·)` (`hF_eq_inv_coshD`).

Proof (different from the paper's generating-function argument, same statement): by `wordR_hpow`,
`X₀^β Z_S X₀^{-β} = P_S(ξ, υ)` with `|ξ| ≤ 1`, `0 ≤ υ ≤ 2`. For the weighted coefficient norm
`‖P‖ = Σ |c_m| 2^{m_υ}` one has `|P(ξ, υ)| ≤ ‖P‖` (`abs_ev_le_wN`), and each letter multiplies it by at
most `4d + 3β` on polynomials of degree `≤ d` while raising the degree by one (`wN_DZ_le`). Hence
`|P_S(ξ, υ)| ≤ ∏_{i<j} (4i + 3β) ≤ 4^j j! (j + k)^k` (`k = ⌈3β/4⌉`), and `(4ρ_β)^j (j + k)^k` is bounded
since `4ρ_β = log(3/2) < 1`.
-/

namespace Qschubert

open MvPolynomial Finset Filter Topology
open scoped BigOperators

/-! ### The weighted norm -/

/-- `‖P‖ = Σ |c_m| 2^{m₁}`. -/
noncomputable def wN (P : P2) : ℝ := ∑ m ∈ P.support, |P.coeff m| * 2 ^ (m 1)

lemma wN_eq_sum_of_subset (P : P2) {s : Finset (Fin 2 →₀ ℕ)} (hs : P.support ⊆ s) :
    wN P = ∑ m ∈ s, |P.coeff m| * 2 ^ (m 1) := by
  unfold wN
  refine Finset.sum_subset hs (fun m _ hm => ?_)
  rw [MvPolynomial.notMem_support_iff.1 hm, abs_zero, zero_mul]

lemma wN_nonneg (P : P2) : 0 ≤ wN P := Finset.sum_nonneg fun _ _ => by positivity

lemma wN_zero : wN 0 = 0 := by simp [wN]

lemma wN_add_le (P Q : P2) : wN (P + Q) ≤ wN P + wN Q := by
  classical
  have hs : (P + Q).support ⊆ P.support ∪ Q.support := MvPolynomial.support_add
  rw [wN_eq_sum_of_subset _ hs, wN_eq_sum_of_subset P Finset.subset_union_left,
    wN_eq_sum_of_subset Q Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [MvPolynomial.coeff_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)

lemma support_neg' (P : P2) : (-P).support = P.support := by
  ext m; simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_neg]

lemma wN_neg (P : P2) : wN (-P) = wN P := by
  rw [wN, support_neg']
  simp [MvPolynomial.coeff_neg, abs_neg, wN]

lemma wN_sub_le (P Q : P2) : wN (P - Q) ≤ wN P + wN Q := by
  rw [sub_eq_add_neg]
  exact (wN_add_le _ _).trans (by rw [wN_neg])

lemma wN_monomial (m : Fin 2 →₀ ℕ) (c : ℝ) : wN (monomial m c) = |c| * 2 ^ (m 1) := by
  classical
  by_cases hc : c = 0
  · simp [hc, wN]
  · rw [wN, MvPolynomial.support_monomial, if_neg hc, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]

lemma wN_sum_le {ι : Type*} (s : Finset ι) (f : ι → P2) :
    wN (∑ i ∈ s, f i) ≤ ∑ i ∈ s, wN (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wN_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (wN_add_le _ _).trans (add_le_add le_rfl ih)

/-- `|P(a, b)| ≤ ‖P‖` for `|a| ≤ 1`, `|b| ≤ 2`. -/
lemma abs_ev_le_wN (P : P2) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 2) : |ev P a b| ≤ wN P := by
  rw [ev, MvPolynomial.eval_eq']
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [Fin.prod_univ_two, abs_mul, abs_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_pow]
  have h1 : |a| ^ (m 0) ≤ 1 := pow_le_one₀ (abs_nonneg a) ha
  have h2 : |b| ^ (m 1) ≤ 2 ^ (m 1) := pow_le_pow_left₀ (abs_nonneg b) hb _
  calc |P.coeff m| * (|a| ^ (m 0) * |b| ^ (m 1)) ≤ |P.coeff m| * (1 * 2 ^ (m 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) zero_le_one) (abs_nonneg _)
    _ = |P.coeff m| * 2 ^ (m 1) := by ring

/-! ### Degrees -/

/-- All monomials of `P` have total degree `≤ d`. -/
def DegLe (P : P2) (d : ℕ) : Prop := ∀ m ∈ P.support, m 0 + m 1 ≤ d

lemma degLe_add {P Q : P2} {d : ℕ} (hP : DegLe P d) (hQ : DegLe Q d) : DegLe (P + Q) d := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  · exact hP m h
  · exact hQ m h

lemma degLe_neg {P : P2} {d : ℕ} (hP : DegLe P d) : DegLe (-P) d := by
  intro m hm; rw [support_neg'] at hm; exact hP m hm

lemma degLe_sub {P Q : P2} {d : ℕ} (hP : DegLe P d) (hQ : DegLe Q d) : DegLe (P - Q) d := by
  rw [sub_eq_add_neg]; exact degLe_add hP (degLe_neg hQ)

lemma degLe_monomial {n : Fin 2 →₀ ℕ} {a : ℝ} {d : ℕ} (h : n 0 + n 1 ≤ d) : DegLe (monomial n a) d := by
  classical
  intro m hm
  have := MvPolynomial.support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]; exact h

lemma degLe_monomial' {n : Fin 2 →₀ ℕ} {a : ℝ} {d : ℕ} (h : a ≠ 0 → n 0 + n 1 ≤ d) :
    DegLe (monomial n a) d := by
  by_cases ha : a = 0
  · intro m hm; simp [ha] at hm
  · exact degLe_monomial (h ha)

lemma degLe_sum {ι : Type*} (s : Finset ι) (f : ι → P2) {d : ℕ} (h : ∀ i ∈ s, DegLe (f i) d) :
    DegLe (∑ i ∈ s, f i) d := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m hm; simp at hm
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact degLe_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma degLe_mono {P : P2} {d e : ℕ} (hP : DegLe P d) (hde : d ≤ e) : DegLe P e :=
  fun m hm => (hP m hm).trans hde

/-! ### One letter on a monomial -/

lemma X_eq_monomial (i : Fin 2) : (X i : P2) = monomial (Finsupp.single i 1) 1 := rfl

lemma mono_mul (n n' : Fin 2 →₀ ℕ) (a a' : ℝ) :
    (monomial n a : P2) * monomial n' a' = monomial (n + n') (a * a') := monomial_mul

lemma pow_tsub_mul (k : ℕ) : (k : ℝ) * 2 ^ (1 + (k - 1)) = k * 2 ^ k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · rw [show 1 + (k - 1) = k by omega]

lemma pow_tsub_mul' (k : ℕ) : (k : ℝ) * 2 ^ (2 + (k - 1)) = 2 * (k * 2 ^ k) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · rw [show 2 + (k - 1) = k + 1 by omega, pow_succ]; ring

/-- `‖D_X(c ξ^a υ^b)‖ ≤ (3a + b + |β|)|c| 2^b`, and the degree rises by at most one. -/
lemma DX_monomial (β : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    wN (DX β (monomial m c)) ≤ (3 * m 0 + m 1 + |β|) * (|c| * 2 ^ (m 1))
      ∧ DegLe (DX β (monomial m c)) (m 0 + m 1 + 1) := by
  have e : DX β (monomial m c)
      = monomial (Finsupp.single 1 1 + (m - Finsupp.single 0 1)) (1 * (c * m 0))
        - monomial (2 • Finsupp.single 0 1 + (m - Finsupp.single 0 1)) (1 ^ 2 * (c * m 0))
        - monomial (Finsupp.single 0 1 + Finsupp.single 1 1 + (m - Finsupp.single 1 1)) (1 * 1 * (c * m 1))
        - monomial (0 + Finsupp.single 0 1 + m) (β * 1 * c) := by
    simp only [DX, pderiv_monomial, X_eq_monomial, MvPolynomial.monomial_pow, C_apply, sub_mul, mono_mul]
  refine ⟨?_, ?_⟩
  · rw [e]
    refine (wN_sub_le _ _).trans ?_
    refine (add_le_add (wN_sub_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (wN_sub_le _ _) le_rfl) le_rfl).trans ?_
    simp only [wN_monomial, Finsupp.add_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
      Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply, smul_eq_mul]
    norm_num
    have h3 := pow_tsub_mul (m 1)
    rw [show |c| * (m 1 : ℝ) * 2 ^ (1 + (m 1 - 1)) = |c| * ((m 1 : ℝ) * 2 ^ (1 + (m 1 - 1))) by ring, h3,
      pow_add]
    apply le_of_eq; ring
  · rw [e]
    refine degLe_sub (degLe_sub (degLe_sub (degLe_monomial' ?_) (degLe_monomial' ?_)) (degLe_monomial' ?_))
      (degLe_monomial' ?_) <;> intro h <;>
    simp only [Finsupp.add_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
      Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or,
      Nat.cast_eq_zero, one_pow, one_mul, mul_one] at h ⊢ <;> (try norm_num at h ⊢) <;> omega

/-- `‖D_Y(c ξ^a υ^b)‖ ≤ (3a + 4b + 3|β|)|c| 2^b`, and the degree rises by at most one. -/
lemma DY_monomial (β : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    wN (DY β (monomial m c)) ≤ (3 * m 0 + 4 * m 1 + 3 * |β|) * (|c| * 2 ^ (m 1))
      ∧ DegLe (DY β (monomial m c)) (m 0 + m 1 + 1) := by
  have e : DY β (monomial m c)
      = monomial (Finsupp.single 0 1 + (m - Finsupp.single 0 1)) (1 * (c * m 0))
        - monomial (Finsupp.single 0 1 + Finsupp.single 1 1 + (m - Finsupp.single 0 1)) (1 * 1 * (c * m 0))
        + monomial (0 + Finsupp.single 1 1 + (m - Finsupp.single 1 1)) (2 * 1 * (c * m 1))
        - monomial (2 • Finsupp.single 1 1 + (m - Finsupp.single 1 1)) (1 ^ 2 * (c * m 1))
        - monomial (0 + Finsupp.single 1 1 + m) (β * 1 * c)
        + monomial (0 + m) (β * c) := by
    simp only [DY, pderiv_monomial, X_eq_monomial, MvPolynomial.monomial_pow, C_apply, sub_mul,
      mul_sub, mono_mul]
    rw [show (1 : P2) = monomial 0 1 from rfl, mono_mul, mono_mul]
    ring_nf
  refine ⟨?_, ?_⟩
  · rw [e]
    refine (wN_add_le _ _).trans ?_
    refine (add_le_add (wN_sub_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (wN_sub_le _ _) le_rfl) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (wN_add_le _ _) le_rfl) le_rfl) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (add_le_add (wN_sub_le _ _) le_rfl) le_rfl) le_rfl)
      le_rfl).trans ?_
    simp only [wN_monomial, Finsupp.add_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
      Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply, smul_eq_mul]
    norm_num
    have h3 := pow_tsub_mul (m 1)
    have h4 := pow_tsub_mul' (m 1)
    rw [show 2 * (|c| * (m 1 : ℝ)) * 2 ^ (1 + (m 1 - 1)) = 2 * |c| * ((m 1 : ℝ) * 2 ^ (1 + (m 1 - 1))) by ring,
      h3, show |c| * (m 1 : ℝ) * 2 ^ (2 + (m 1 - 1)) = |c| * ((m 1 : ℝ) * 2 ^ (2 + (m 1 - 1))) by ring, h4,
      pow_add]
    apply le_of_eq; ring
  · rw [e]
    refine degLe_add (degLe_sub (degLe_sub (degLe_add (degLe_sub (degLe_monomial' ?_) (degLe_monomial' ?_))
      (degLe_monomial' ?_)) (degLe_monomial' ?_)) (degLe_monomial' ?_)) (degLe_monomial' ?_) <;> intro h <;>
    simp only [Finsupp.add_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
      Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or,
      Nat.cast_eq_zero, one_pow, one_mul, mul_one] at h ⊢ <;> (try norm_num at h ⊢) <;> omega

/-! ### One letter on a polynomial -/

lemma DZ_add (β : ℝ) (z : Bool) (P Q : P2) : DZ β z (P + Q) = DZ β z P + DZ β z Q := by
  cases z <;> simp only [DZ, DX, DY, map_add, Bool.false_eq_true, ite_false, ite_true] <;> ring

lemma DZ_zero (β : ℝ) (z : Bool) : DZ β z 0 = 0 := by
  cases z <;> simp [DZ, DX, DY]

lemma DZ_sum (β : ℝ) (z : Bool) {ι : Type*} (s : Finset ι) (f : ι → P2) :
    DZ β z (∑ i ∈ s, f i) = ∑ i ∈ s, DZ β z (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DZ_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DZ_add, ih]

lemma DZ_monomial (β : ℝ) (z : Bool) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    wN (DZ β z (monomial m c)) ≤ (4 * (m 0 + m 1) + 3 * |β|) * (|c| * 2 ^ (m 1))
      ∧ DegLe (DZ β z (monomial m c)) (m 0 + m 1 + 1) := by
  have hk : 0 ≤ |c| * 2 ^ (m 1) := by positivity
  have h0 : (0 : ℝ) ≤ m 0 := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ m 1 := Nat.cast_nonneg _
  cases z
  · obtain ⟨hw, hd⟩ := DY_monomial β m c
    refine ⟨hw.trans (mul_le_mul_of_nonneg_right (by linarith) hk), ?_⟩
    simpa [DZ] using hd
  · obtain ⟨hw, hd⟩ := DX_monomial β m c
    refine ⟨hw.trans (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg β]) hk), ?_⟩
    simpa [DZ] using hd

/-- **One letter**: `‖D_Z P‖ ≤ (4d + 3|β|)‖P‖` and `deg D_Z P ≤ d + 1` for `deg P ≤ d`. -/
theorem wN_DZ_le (β : ℝ) (z : Bool) {P : P2} {d : ℕ} (hP : DegLe P d) :
    wN (DZ β z P) ≤ (4 * d + 3 * |β|) * wN P ∧ DegLe (DZ β z P) (d + 1) := by
  rw [P.as_sum, DZ_sum]
  refine ⟨(wN_sum_le _ _).trans ?_, degLe_sum _ _ fun m hm =>
    degLe_mono (DZ_monomial β z m _).2 (by have := hP m hm; omega)⟩
  rw [wN, Finset.mul_sum]
  have hs : (∑ v ∈ P.support, monomial v (P.coeff v)).support ⊆ P.support := by
    rw [← P.as_sum]
  rw [← P.as_sum] at hs ⊢
  refine Finset.sum_le_sum fun m hm => ?_
  refine (DZ_monomial β z m _).1.trans ?_
  have hd : ((m 0 + m 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hP m hm
  push_cast at hd
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **All letters**: `‖P_S‖ ≤ ∏_{i<j} (4i + 3|β|)`, `deg P_S ≤ j`. -/
theorem wN_PS_le (β : ℝ) (S : List Bool) :
    wN (PS β S) ≤ ∏ i ∈ Finset.range S.length, (4 * (i : ℝ) + 3 * |β|) ∧ DegLe (PS β S) S.length := by
  induction S with
  | nil =>
    refine ⟨?_, ?_⟩
    · simp [PS, wN, MvPolynomial.support_one]
    · intro m hm
      have : m = 0 := by
        have h := MvPolynomial.support_monomial_subset (show m ∈ (monomial 0 (1 : ℝ) : P2).support from hm)
        simpa using h
      simp [this]
  | cons z S ih =>
    obtain ⟨hw, hd⟩ := ih
    obtain ⟨hw', hd'⟩ := wN_DZ_le β z hd
    refine ⟨?_, ?_⟩
    · simp only [PS, List.length_cons, Finset.prod_range_succ]
      calc wN (DZ β z (PS β S)) ≤ (4 * (S.length : ℝ) + 3 * |β|) * wN (PS β S) := hw'
        _ ≤ (4 * (S.length : ℝ) + 3 * |β|) * ∏ i ∈ Finset.range S.length, (4 * (i : ℝ) + 3 * |β|) :=
            mul_le_mul_of_nonneg_left hw (by positivity)
        _ = _ := by ring
    · simpa [PS] using hd'

/-! ### The factorial bound -/

lemma prod_le_factorial (c : ℝ) (hc : 0 ≤ c) (j : ℕ) :
    ∏ i ∈ Finset.range j, (4 * (i : ℝ) + c)
      ≤ 4 ^ j * j.factorial * ((j + ⌈c / 4⌉₊ : ℕ) : ℝ) ^ ⌈c / 4⌉₊ := by
  set k := ⌈c / 4⌉₊
  have hk : c ≤ 4 * k := by have := Nat.le_ceil (c / 4); linarith
  have h1 : ∏ i ∈ Finset.range j, (4 * (i : ℝ) + c) ≤ ∏ i ∈ Finset.range j, (4 * ((k + 1 + i : ℕ) : ℝ)) := by
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => ?_)
    push_cast; linarith
  refine h1.trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have h2 : ∏ i ∈ Finset.range j, ((k + 1 + i : ℕ) : ℝ) = ((k + 1).ascFactorial j : ℕ) := by
    rw [Nat.ascFactorial_eq_prod_range]; push_cast; rfl
  rw [h2, Nat.ascFactorial_eq_factorial_mul_choose]
  have h3 : (k + j).choose j = (k + j).choose k := by
    rw [Nat.choose_symm_of_eq_add]; ring
  rw [h3]
  have h4 : ((k + j).choose k : ℝ) ≤ ((j + k : ℕ) : ℝ) ^ k := by
    rw [show k + j = j + k by ring]; exact_mod_cast Nat.choose_le_pow (j + k) k
  push_cast
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left (by push_cast at h4; exact h4) (by positivity)

/-- `ρ_β = ¼ log(3/2)`. -/
noncomputable def rhoFdb : ℝ := Real.log (3 / 2) / 4

lemma rhoFdb_pos : 0 < rhoFdb := by
  unfold rhoFdb; have := Real.log_pos (show (1 : ℝ) < 3 / 2 by norm_num); positivity

lemma four_rho_lt_one : 4 * rhoFdb < 1 := by
  unfold rhoFdb
  have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num) (by norm_num)
  linarith

lemma exists_bound_poly_geom (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, ((j + k : ℕ) : ℝ) ^ k * (4 * rhoFdb) ^ j ≤ B := by
  have hr0 : 0 ≤ 4 * rhoFdb := by have := rhoFdb_pos; positivity
  have hr1 := four_rho_lt_one
  have ht : Tendsto (fun j : ℕ => ((j + k : ℕ) : ℝ) ^ k * (4 * rhoFdb) ^ j) atTop (𝓝 0) := by
    have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one k (show |4 * rhoFdb| < 1 by
      rw [abs_of_nonneg hr0]; exact hr1)
    have h' := h.comp (tendsto_add_atTop_nat k)
    have hpos : 0 < 4 * rhoFdb := by have := rhoFdb_pos; positivity
    have e : ∀ j : ℕ, ((j + k : ℕ) : ℝ) ^ k * (4 * rhoFdb) ^ j
        = ((4 * rhoFdb) ^ k)⁻¹ * (((j + k : ℕ) : ℝ) ^ k * (4 * rhoFdb) ^ (j + k)) := by
      intro j; rw [pow_add]; field_simp
    simp_rw [e]
    have := h'.const_mul ((4 * rhoFdb) ^ k)⁻¹
    simpa [Function.comp_def] using this
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun j => ?_⟩
  have := hC _ (Set.mem_range_self j)
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

/-! ### The lemma -/

lemma hF_eq_inv_coshD (z : UpperHalfPlane) : hF (z : ℂ) = (coshD UpperHalfPlane.I z)⁻¹ := by
  rw [coshD, UpperHalfPlane.cosh_dist']
  simp only [hF, normN, UpperHalfPlane.I_re, UpperHalfPlane.I_im, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  have hy := z.im_pos
  field_simp
  ring

/-- **Lemma FDB** (`lem:fdb`): `|X₀^β Z_S X₀^{-β}| ≤ B_β j! ρ_β^{-j}` on `ℍ`, `ρ_β = ¼ log(3/2)`,
for every word `S` of length `j` in `X = y∂ₓ`, `Y = y∂_y`, where `X₀^{-1} = hF = 1/cosh d(i, ·)`. -/
theorem fdb (β : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (S : List Bool) (w : ℂ), 0 < w.im →
    |hF w ^ (-β) * wordR S (fun u => hF u ^ β) w| ≤ B * S.length.factorial * rhoFdb⁻¹ ^ S.length := by
  obtain ⟨B₀, hB₀, hB⟩ := exists_bound_poly_geom ⌈3 * |β| / 4⌉₊
  refine ⟨B₀, hB₀, fun S w hw => ?_⟩
  set j := S.length
  have hh := hF_pos hw
  rw [wordR_hpow β S hw, ← mul_assoc, ← Real.rpow_add hh, neg_add_cancel, Real.rpow_zero, one_mul]
  have hev := abs_ev_le_wN (PS β S) (abs_xiF_le w)
    (by rw [abs_of_nonneg (upF_nonneg w)]; exact upF_le_two w)
  have hP := (wN_PS_le β S).1
  have hprod := prod_le_factorial (3 * |β|) (by positivity) j
  have hρ := rhoFdb_pos
  have key : (4 : ℝ) ^ j * ((j + ⌈3 * |β| / 4⌉₊ : ℕ) : ℝ) ^ ⌈3 * |β| / 4⌉₊ ≤ B₀ * rhoFdb⁻¹ ^ j := by
    have := hB j
    rw [mul_pow] at this
    have hρj : 0 < rhoFdb ^ j := pow_pos hρ j
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hρj]
    calc (4 : ℝ) ^ j * ((j + ⌈3 * |β| / 4⌉₊ : ℕ) : ℝ) ^ ⌈3 * |β| / 4⌉₊ * rhoFdb ^ j
        = ((j + ⌈3 * |β| / 4⌉₊ : ℕ) : ℝ) ^ ⌈3 * |β| / 4⌉₊ * (4 ^ j * rhoFdb ^ j) := by ring
      _ ≤ B₀ := this
  calc |ev (PS β S) (xiF w) (upF w)| ≤ wN (PS β S) := hev
    _ ≤ ∏ i ∈ Finset.range j, (4 * (i : ℝ) + 3 * |β|) := hP
    _ ≤ 4 ^ j * j.factorial * ((j + ⌈3 * |β| / 4⌉₊ : ℕ) : ℝ) ^ ⌈3 * |β| / 4⌉₊ := hprod
    _ = j.factorial * (4 ^ j * ((j + ⌈3 * |β| / 4⌉₊ : ℕ) : ℝ) ^ ⌈3 * |β| / 4⌉₊) := by ring
    _ ≤ j.factorial * (B₀ * rhoFdb⁻¹ ^ j) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = B₀ * j.factorial * rhoFdb⁻¹ ^ j := by ring

end Qschubert
