import Qschubert.SurfaceOps
import Qschubert.LambdaH
import Qschubert.Setting

/-!
# Frozen statements of the main theorems (spine stage S5): smooth-representative versions

Reviewed in R39 (PASS on quantifiers, bound, norm order and the placement of convergence; scope
fixes applied here). These are the SMOOTH-REPRESENTATIVE versions: the amplitude `a` is assumed `C^∞`
(`SmoothH a`), whereas the manuscript assumes only that the norm is finite. The lifting to the
norm-only statements is an open obligation (LIFT-1 in `lean/BLUEPRINT.md`): every finite-norm
amplitude has a `C^∞` representative, with the same norm, initial state and approximant. Other
recorded obligations: BND-1 (every `b ∈ ∂ℍ` is `g • ∞` with `g` fixing `x₀`, and the choice of `g`
changes `initState` and `approxSolB` by one common constant phase), DELTA-1 (the explicit caps on `δ`
in `pc:main` are not part of `Stmt_pcmain_smooth`), NONVAC-1 (nonzero amplitudes of finite norm),
T2-ABS (the absolute envelope `Σ_γ |u ∘ γ|` lies in `L²(M)`, stronger than `PerioConv`).
Conventions:

* `Γ ≤ PGL(2, ℝ)` with `ProperlyDiscontinuousSMul Γ ℍ` and `OrientationPreserving Γ` is a Fuchsian
  group; for the image of a discrete `Γ' ≤ SL(2, ℝ)` both hold (`Qschubert/Bridge.lean`, R40; an
  abstract-`PSL(2, ℝ)` starting point would need further quotient lemmas);
* the base point `x₀` is a parameter; a boundary point `b = g • ∞` is given by `g ∈ SL(2, ℝ)` fixing
  `x₀` (every `b` arises; `φ_b` is normalized up to a constant, which no error norm sees);
* amplitudes are `C^∞` functions on `ℍ` (LIFT-1 above);
* the conclusion includes the convergence of both periodizations (`PerioConv`: absolute convergence
  of the orbit sum a.e., and the sum in `L²(M)`), then bounds the error norm `‖Δ_M^N [U_M(t)(a e^{iφ_b/ħ})_Γ − u^{(K)}(t)_Γ]‖` in `ℝ≥0∞`.
-/

namespace Qschubert

open MeasureTheory Complex Physicslib4.Spectral.Unbounded
open scoped ENNReal MatrixGroups UpperHalfPlane

/-- `Γ ⊆ PSL(2, ℝ)`: every element is the class of a matrix of positive determinant. -/
def OrientationPreserving (Γ : Subgroup PGL(2, ℝ)) : Prop :=
  ∀ γ ∈ Γ, ∃ g : GL (Fin 2) ℝ, 0 < g.det.val ∧ Matrix.ProjGenLinGroup.mk g = γ

/-- `a` is `C^∞` on `ℍ` (order `(⊤ : ℕ∞)`, i.e. smooth; `⊤ : WithTop ℕ∞` would mean analytic). -/
def SmoothH (a : ℍ → ℂ) : Prop :=
  ∀ z : ℍ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extC a) (z : ℂ)

/-- `X₀ = cosh d(x₀, ·)`. -/
noncomputable def coshD (x₀ z : ℍ) : ℝ := Real.cosh (dist x₀ z)

/-- `⟨d⟩ = (1 + d(x₀, ·)²)^{1/2} - 1`. -/
noncomputable def angleDx (x₀ z : ℍ) : ℝ := Real.sqrt (1 + dist x₀ z ^ 2) - 1

open Classical in
/-- The swapped norm of Theorem 1.4R (appendix form): `‖e^{αΛ} X₀^β a‖`, `∞` if undefined. -/
noncomputable def swNormX (x₀ : ℍ) (α β : ℝ) (a : ℍ → ℂ) : ℝ≥0∞ :=
  if hw : MemLp (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ) then
    if h : hw.toLp _ ∈ (expLambda α).domain then ‖expLambda α ⟨hw.toLp _, h⟩‖ₑ else ∞
  else ∞

open Classical in
/-- The printed norm of `pc:main`: `‖e^{β⟨d⟩} e^{αΛ} a‖`, `∞` if undefined. -/
noncomputable def prNormX (x₀ : ℍ) (α β : ℝ) (a : ℍ → ℂ) : ℝ≥0∞ :=
  if ha : MemLp a 2 (volume : Measure ℍ) then
    if h : ha.toLp _ ∈ (expLambda α).domain then
      eLpNorm (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ)
        * (expLambda α ⟨ha.toLp _, h⟩ : Lp ℂ 2 (volume : Measure ℍ)) z) 2 (volume : Measure ℍ)
    else ∞
  else ∞

/-- Convergence of `u_Γ`: absolute convergence of `Σ_γ u(γ z)` for a.e. `z`, and the sum `u_Γ` lies in
`L²(M)`. This does not assert that the absolute envelope `Σ_γ |u ∘ γ|` lies in `L²(M)` or that partial
sums converge in `L²(M)` (T2-ABS, R39). -/
def PerioConv (Γ : Subgroup PGL(2, ℝ)) (u : ℍ → ℂ) : Prop :=
  (∀ᵐ z ∂(volume : Measure ℍ), Summable fun γ : Γ => ‖u (γ • z)‖)
    ∧ MemLp (perio Γ u) 2 (surfMeasure Γ)

/-- `C^{N+K+1} N^{2N} K! (αħ)^{-2N} (ħt/α²)^{K+1}` (with `N^{2N} = 1` at `N = 0`). -/
noncomputable def ddBound (C α ħ' t : ℝ) (K N : ℕ) : ℝ :=
  C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((α * ħ')⁻¹) ^ (2 * N)
    * (ħ' * t / α ^ 2) ^ (K + 1)

/-- `‖Δ_M^N [U_M(t) v_Γ − w_Γ]‖` in `ℝ≥0∞`, for periodizations known to converge. -/
noncomputable def approxErr (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (N : ℕ)
    (ħ' t : ℝ) {v w : ℍ → ℂ} (hv : PerioConv Γ v) (hw : PerioConv Γ w) : ℝ≥0∞ :=
  errNormM Γ N (propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _)

/-- **Theorem 1.4R** (`thm:dd-appx`, swapped class), smooth-representative version. -/
def Stmt_thm14R_smooth : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ α₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ α₀ → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → swNormX x₀ α β a < ∞ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
      approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormX x₀ α β a

/-- **Theorem `pc:main`** (printed class), smooth-representative version. "`α₀` small" is read as:
some `α₀* > 0` (depending on `Γ, x₀, β, κ`) such that the statement holds for every `α₀ ∈ (0, α₀*]`. -/
def Stmt_pcmain_smooth : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < Real.pi / 4 ∧ ∀ α₀ : ℝ, 0 < α₀ → α₀ ≤ α₀max →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ α₀ → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ∞ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
      approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * prNormX x₀ α β a

open Classical in
/-- The swapped norm of the main text (`sec:repair`): `‖e^{αΛ} e^{β⟨d⟩} a‖`, `∞` if undefined. -/
noncomputable def swNormD (x₀ : ℍ) (α β : ℝ) (a : ℍ → ℂ) : ℝ≥0∞ :=
  if hw : MemLp (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ) then
    if h : hw.toLp _ ∈ (expLambda α).domain then ‖expLambda α ⟨hw.toLp _, h⟩‖ₑ else ∞
  else ∞

/-- The Poincaré series bound of Lemma P1: `sup_z Σ_γ e^{-s d(x₀, γ z)}`, in `ℝ≥0∞`. -/
noncomputable def poincareSup (Γ : Subgroup PGL(2, ℝ)) (x₀ : ℍ) (s : ℝ) : ℝ≥0∞ :=
  ⨆ z : ℍ, ∑' γ : Γ, ENNReal.ofReal (Real.exp (-(s * dist x₀ (γ • z))))

/-- **Theorem 1.4R, main-text form** (`thm:dd14`, paper.tex l.420), smooth-representative version:
weight `e^{β⟨d⟩}`. The manuscript chooses `C, δ` before `Γ` and lets `C` depend on `Γ` only through
the Poincaré series bound of Lemma P1. Read (R44): an exponent `s > 1` depending on `β` only; `δ`
before the bound `P` and before `Γ`; `C` after `P`, uniform over Fuchsian `Γ` with
`poincareSup Γ x₀ s ≤ P`. -/
def Stmt_thm14Rmain_smooth : Prop :=
  ∀ β : ℝ, 1 / 2 < β → ∃ s : ℝ, 1 < s ∧
  ∀ (x₀ : ℍ) (κ α₀ : ℝ), 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ s ≤ ENNReal.ofReal P →
  ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ α₀ → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → swNormD x₀ α β a < ∞ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
      approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormD x₀ α β a

/-- **Theorem 1.3R** (`thm:main`, paper.tex l.352), smooth-representative version:
`‖U(t)[a e^{iφ_b/ħ}]_Γ - u^{(0)}(t)_Γ‖ ≤ C ħ t ‖a‖` for `0 ≤ t ≤ δ ħ^{-1/2}`, with `β > 1` and a fixed
`α ∈ (0, α₀]`, `α₀ < π/4`; the norm is `‖e^{αΛ} e^{β⟨d⟩} a‖`. The range of `ħ` is not stated in the
manuscript; it is read as `0 < ħ ≤ 1`. -/
def Stmt_thm13R_smooth : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β α₀ α : ℝ), 1 < β → 0 < α₀ → α₀ < Real.pi / 4 → 0 < α → α ≤ α₀ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (ħ' t : ℝ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ / Real.sqrt ħ' →
    SmoothH a → swNormD x₀ α β a < ∞ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g 0 ħ' t a)),
      ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ
        ≤ ENNReal.ofReal (C * ħ' * t) * swNormD x₀ α β a

/-- The injectivity radius of `M` is at least `r₀`: every `γ ≠ 1` moves every point by `≥ 2 r₀`. -/
def InjRadGe (Γ : Subgroup PGL(2, ℝ)) (r₀ : ℝ) : Prop :=
  ∀ γ : Γ, γ ≠ 1 → ∀ z : ℍ, 2 * r₀ ≤ dist z (γ • z)

/-- `m(z) = #{γ : d(z̃, γ z̃) < 2}` for `z ∈ M`, computed at a lift `z̃` (Lemma `pc:g43`). -/
noncomputable def multM (Γ : Subgroup PGL(2, ℝ)) (x : Surf Γ) : ℕ∞ := orbitMult Γ (Quotient.out x)

/-- The error vector `U_M(t) v_Γ - w_Γ ∈ L²(M)`. -/
noncomputable def errVec (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (ħ' t : ℝ)
    {v w : ℍ → ℂ} (hv : PerioConv Γ v) (hw : PerioConv Γ w) : Lp ℂ 2 (surfMeasure Γ) :=
  propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _

/-- The pointwise conclusion of Corollary 1.6: `E ∈ Dom(Δ_M^N)`, and `Δ_M^N E` has a continuous
representative `f` with `|f(z)| ≤ B(z)` at every `z ∈ M`. -/
def PointwiseBound (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (N : ℕ)
    (E : Lp ℂ 2 (surfMeasure Γ)) (B : Surf Γ → ℝ≥0∞) : Prop :=
  ∃ hdom : E ∈ (lapPowM Γ N).domain, ∃ f : Surf Γ → ℂ, Continuous f ∧
    f =ᵐ[surfMeasure Γ] ⇑(lapPowM Γ N ⟨E, hdom⟩) ∧ ∀ x, ‖f x‖ₑ ≤ B x

/-- `C^{N+K+1} (2N)! K! (αħ)^{-2N-4} (ħt/α²)^{K+1}`. -/
noncomputable def ptBound (C α ħ' t : ℝ) (K N : ℕ) : ℝ :=
  C ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * ((α * ħ')⁻¹) ^ (2 * N + 4)
    * (ħ' * t / α ^ 2) ^ (K + 1)

/-- **Corollary 1.6R** (`cor:dd16-appx`), swapped class on bounded geometry, smooth-representative
version. -/
def Stmt_cor16R_smooth : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ α₀ r₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) → 0 < r₀ →
    InjRadGe Γ r₀ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ α₀ → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → swNormX x₀ α β a < ∞ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
      PointwiseBound Γ N (errVec Γ ħ' t hv hw)
        (fun _ => ENNReal.ofReal (ptBound C α ħ' t K N) * swNormX x₀ α β a)

/-- **Corollary `pc:cor16bg`** (printed class, bounded geometry), smooth-representative version. -/
def Stmt_pccor16bg_smooth : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ r₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < r₀ → InjRadGe Γ r₀ →
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < Real.pi / 4 ∧ ∀ α₀ : ℝ, 0 < α₀ → α₀ ≤ α₀max →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ α₀ → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ∞ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
      PointwiseBound Γ N (errVec Γ ħ' t hv hw)
        (fun _ => ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a)

/-- **Corollary `pc:cor16`** (printed class, every Fuchsian quotient, with the cusp factor
`m(z)^{1/2}`), smooth-representative version. -/
def Stmt_pccor16_smooth : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < Real.pi / 4 ∧ ∀ α₀ : ℝ, 0 < α₀ → α₀ ≤ α₀max →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ α₀ → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ∞ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
      PointwiseBound Γ N (errVec Γ ħ' t hv hw)
        (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
          * ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a)

/-- `m` does not depend on the lift: `m(γ z) = m(z)`. -/
lemma orbitMult_smul (Γ : Subgroup PGL(2, ℝ)) (γ : Γ) (z : ℍ) :
    orbitMult Γ (γ • z) = orbitMult Γ z := by
  unfold orbitMult
  have e : {δ : Γ | dist (γ • z) (δ • γ • z) < 2}
      = (fun δ => γ * δ * γ⁻¹) '' {δ : Γ | dist z (δ • z) < 2} := by
    ext δ
    constructor
    · intro h
      refine ⟨γ⁻¹ * δ * γ, ?_, by group⟩
      show dist z ((γ⁻¹ * δ * γ) • z) < 2
      rw [mul_smul, mul_smul, ← dist_smul γ, smul_inv_smul]
      exact h
    · rintro ⟨δ', h, rfl⟩
      show dist (γ • z) ((γ * δ' * γ⁻¹) • γ • z) < 2
      rw [mul_smul, mul_smul, inv_smul_smul, dist_smul]
      exact h
  have hinj : Function.Injective (fun δ : Γ => γ * δ * γ⁻¹) := fun a b h => by
    simpa using h
  rw [e, hinj.injOn.encard_image]

/-- `multM` evaluated at the projection of `z` is `m(z)`. -/
lemma multM_mk (Γ : Subgroup PGL(2, ℝ)) (z : ℍ) : multM Γ (surfMk Γ z) = orbitMult Γ z := by
  unfold multM
  obtain ⟨γ, hγ⟩ : Quotient.out (surfMk Γ z) ∈ MulAction.orbit Γ z :=
    Quotient.mk_out (s := MulAction.orbitRel Γ ℍ) z
  rw [← hγ, orbitMult_smul]

end Qschubert
