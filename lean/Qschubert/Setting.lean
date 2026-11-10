import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The objects of the main theorems on `ℍ`

Manuscript `paper/paper.tex`, Section "Setting", and Schubert's arXiv:0705.0134v1, (2.1), (2.9),
(1.20) and the definitions of `P_k`, `a^{(K)}`, `u^{(K)}` before his Theorem 1.4.

In the normalization `b = ∞`: coordinates `z = x + i y`; vector fields `X = y ∂ₓ`, `Y = y ∂_y`;
the Laplacian `Δ = y² (∂ₓ² + ∂_y²)`; its transported form `Δ(t) = S(t)* Δ S(t) = e^{-2t} X² + Y² - Y`;
the transport `S(t) a (x, y) = e^{-t/2} a(x, e^t y)`; the phase `φ = -log y`; the Dyson terms
`P_k(t) = ∫_{t > s₁ > ⋯ > s_k > 0} Δ(s₁) ⋯ Δ(s_k) ds`; `a^{(K)}(t) = Σ_{k ≤ K} (iħ/2)^k P_k(t) a`;
and `u^{(K)}(t) = e^{-it/(2ħ)} (S(t) a^{(K)}(t)) e^{iφ/ħ}`.

A general boundary point `b = g • ∞`, `g ∈ SL(2, ℝ)`, is reached by transporting with `g`:
`φ_b = φ ∘ g⁻¹` and `u_b^{(K)}(t)[a] = u^{(K)}(t)[a ∘ g] ∘ g⁻¹`. Schubert's `φ_b` on the disc is
normalized by `φ_b(0) = 0`; the normalization changes `a e^{iφ_b/ħ}` and `u_b^{(K)}` by the
same constant phase and leaves every error norm unchanged.

Derivatives of `f : ℍ → ℂ` are taken of its extension `f ∘ ofComplex` to `ℂ` at points of `ℍ`,
an open subset, so they are the classical partial derivatives.
-/

namespace Qschubert

open UpperHalfPlane Complex
open scoped MatrixGroups

/-- `f ∘ ofComplex : ℂ → ℂ`, which agrees with `f` on `ℍ`. -/
noncomputable def extC (f : ℍ → ℂ) : ℂ → ℂ := fun w => f (ofComplex w)

/-- `∂ₓ f`. -/
noncomputable def dX (f : ℍ → ℂ) : ℍ → ℂ := fun z => fderiv ℝ (extC f) (z : ℂ) 1

/-- `∂_y f`. -/
noncomputable def dY (f : ℍ → ℂ) : ℍ → ℂ := fun z => fderiv ℝ (extC f) (z : ℂ) Complex.I

/-- The vector field `X = y ∂ₓ`. -/
noncomputable def vecX (f : ℍ → ℂ) : ℍ → ℂ := fun z => (z.im : ℂ) * dX f z

/-- The vector field `Y = y ∂_y`. -/
noncomputable def vecY (f : ℍ → ℂ) : ℍ → ℂ := fun z => (z.im : ℂ) * dY f z

/-- The Laplace–Beltrami operator `Δ = y² (∂ₓ² + ∂_y²)` of `y⁻² (dx² + dy²)`. -/
noncomputable def lapH (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z => (z.im : ℂ) ^ 2 * (dX (dX f) z + dY (dY f) z)

/-- `Δ(t) = e^{-2t} X² + Y² - Y` (Schubert (2.9)). -/
noncomputable def lapT (t : ℝ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z => (Real.exp (-2 * t) : ℂ) * vecX (vecX f) z + vecY (vecY f) z - vecY f z

/-- The point `x + i e^t y`. -/
noncomputable def dilate (t : ℝ) (z : ℍ) : ℍ :=
  ⟨⟨z.re, Real.exp t * z.im⟩, mul_pos (Real.exp_pos t) z.im_pos⟩

/-- The transport `S(t) a (x, y) = e^{-t/2} a(x, e^t y)`. -/
noncomputable def transportS (t : ℝ) (a : ℍ → ℂ) : ℍ → ℂ :=
  fun z => (Real.exp (-t / 2) : ℂ) * a (dilate t z)

/-- The phase `φ = φ_∞ = -log y`. -/
noncomputable def phaseInf (z : ℍ) : ℝ := -Real.log z.im

/-- The Dyson terms `P_k(t) a`, by `P_0(t) a = a` and `P_{k+1}(t) a = ∫₀ᵗ Δ(s) (P_k(s) a) ds`. -/
noncomputable def dysonP : ℕ → ℝ → (ℍ → ℂ) → (ℍ → ℂ)
  | 0, _, a => a
  | k + 1, t, a => fun z => ∫ s in (0 : ℝ)..t, lapT s (dysonP k s a) z

/-- `a^{(K)}(t) = Σ_{k ≤ K} (iħ/2)^k P_k(t) a`. -/
noncomputable def approxAmp (K : ℕ) (ħ t : ℝ) (a : ℍ → ℂ) : ℍ → ℂ :=
  fun z => ∑ k ∈ Finset.range (K + 1), (Complex.I * (ħ : ℂ) / 2) ^ k * dysonP k t a z

/-- `u^{(K)}(t) = e^{-it/(2ħ)} (S(t) a^{(K)}(t)) e^{iφ/ħ}` for `b = ∞`. -/
noncomputable def approxSol (K : ℕ) (ħ t : ℝ) (a : ℍ → ℂ) : ℍ → ℂ :=
  fun z => Complex.exp (-(Complex.I * (t : ℂ) / (2 * (ħ : ℂ)))) * transportS t (approxAmp K ħ t a) z
    * Complex.exp (Complex.I * (phaseInf z : ℂ) / (ħ : ℂ))

/-- The phase `φ_b = φ_∞ ∘ g⁻¹` for `b = g • ∞`. -/
noncomputable def phaseB (g : SL(2, ℝ)) (z : ℍ) : ℝ := phaseInf (g⁻¹ • z)

/-- The approximation `u_b^{(K)}(t)[a] = u^{(K)}(t)[a ∘ g] ∘ g⁻¹` for `b = g • ∞`. -/
noncomputable def approxSolB (g : SL(2, ℝ)) (K : ℕ) (ħ t : ℝ) (a : ℍ → ℂ) : ℍ → ℂ :=
  fun z => approxSol K ħ t (fun w => a (g • w)) (g⁻¹ • z)

/-- The initial state `a e^{iφ_b/ħ}`. -/
noncomputable def initState (g : SL(2, ℝ)) (ħ : ℝ) (a : ℍ → ℂ) : ℍ → ℂ :=
  fun z => a z * Complex.exp (Complex.I * (phaseB g z : ℂ) / (ħ : ℂ))

end Qschubert
