import Mathlib

/-!
# Odd support and the half-translation involution

This file formalizes the coefficient-level part of Section 3.1 of the manuscript.
A Fourier expansion is represented by an integer sequence `ℕ → ℤ`.

The involution induced by `τ ↦ τ + 1/2` acts on the `n`th coefficient by
`+1` when `n` is even and by `-1` when `n` is odd.  The main theorem proves
that odd Fourier support is exactly anti-invariance under this involution.
-/

namespace OddSupportFiltration

/-- An integral formal Fourier expansion, represented by its coefficient function. -/
abbrev ZSeries := ℕ → ℤ

/-- The coefficient-extraction operator corresponding to `U₂`. -/
def U2 (f : ZSeries) : ZSeries := fun n => f (n + n)

/-- A series is odd-supported when every even-index coefficient vanishes. -/
def OddSupported (f : ZSeries) : Prop :=
  ∀ n : ℕ, f (n + n) = 0

/-- The action on Fourier coefficients induced by `τ ↦ τ + 1/2`, hence `q ↦ -q`. -/
def halfTranslate (f : ZSeries) : ZSeries := fun n =>
  if Even n then f n else -f n

/-- The `j`th coefficient in the odd subsequence: the coefficient of `q^(2j+1)`. -/
def oddCoeff (f : ZSeries) (j : ℕ) : ℤ := f (j + j + 1)

/-- Vanishing of the first `s` coefficients in the odd subsequence. -/
def OddJetVanishes (s : ℕ) (f : ZSeries) : Prop :=
  ∀ j : ℕ, j < s → oddCoeff f j = 0

@[simp] theorem U2_apply (f : ZSeries) (n : ℕ) : U2 f n = f (n + n) := rfl

@[simp] theorem halfTranslate_apply_even (f : ZSeries) {n : ℕ} (hn : Even n) :
    halfTranslate f n = f n := by
  simp [halfTranslate, hn]

@[simp] theorem halfTranslate_apply_not_even (f : ZSeries) {n : ℕ} (hn : ¬ Even n) :
    halfTranslate f n = -f n := by
  simp [halfTranslate, hn]

/-- Odd support is equivalent to `U₂ f = 0`. -/
theorem oddSupported_iff_U2_eq_zero (f : ZSeries) :
    OddSupported f ↔ U2 f = 0 := by
  constructor
  · intro h
    funext n
    exact h n
  · intro h n
    exact congrFun h n

/-- The half-translation is an involution on coefficient sequences. -/
@[simp] theorem halfTranslate_involution (f : ZSeries) :
    halfTranslate (halfTranslate f) = f := by
  funext n
  by_cases hn : Even n
  · simp [halfTranslate, hn]
  · simp [halfTranslate, hn]

/--
Odd Fourier support is exactly anti-invariance under the half-translation.
This is the coefficient-level form of Proposition 3.2 in the manuscript.
-/
theorem oddSupported_iff_halfTranslate_eq_neg (f : ZSeries) :
    OddSupported f ↔ halfTranslate f = -f := by
  constructor
  · intro hf
    funext n
    by_cases hn : Even n
    · rcases hn with ⟨r, rfl⟩
      have heven : Even (r + r) := ⟨r, rfl⟩
      have hz : f (r + r) = 0 := hf r
      simp [halfTranslate, heven, hz]
    · simp [halfTranslate, hn]
  · intro h n
    have hcoeff := congrFun h (n + n)
    have heven : Even (n + n) := ⟨n, rfl⟩
    simp [halfTranslate, heven] at hcoeff
    omega

/-- Matching the first `s` odd coefficients is equivalent to vanishing of the odd jet of the difference. -/
theorem oddJetVanishes_sub_iff (s : ℕ) (f g : ZSeries) :
    OddJetVanishes s (f - g) ↔
      ∀ j : ℕ, j < s → oddCoeff f j = oddCoeff g j := by
  constructor
  · intro h j hj
    have hz := h j hj
    change f (j + j + 1) - g (j + j + 1) = 0 at hz
    exact sub_eq_zero.mp hz
  · intro h j hj
    change f (j + j + 1) - g (j + j + 1) = 0
    exact sub_eq_zero.mpr (h j hj)

end OddSupportFiltration
