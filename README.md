# Lean formalization: Integral Odd-Support Filtrations on Γ₀(4)

This project is the first formalization layer for the manuscript **“Integral
Odd-Support Filtrations on Γ₀(4)”**.

## What is formalized in the source

The current files formalize the parts of the argument that do not depend on a
full level-4 modular-forms implementation:

1. **Odd support as anti-invariance.** For integer Fourier sequences, vanishing
   at every even index is equivalent to anti-invariance under the coefficient
   action induced by `τ ↦ τ + 1/2` (`q ↦ -q`).

2. **Odd jets.** The first `s` odd coefficients are defined and matching jets are
   identified with vanishing of the corresponding jet of a difference.

3. **Unitriangular recovery.** If observations have the form

   `yᵢ = cᵢ + Σ_{j<i} aᵢⱼ cⱼ`,

   then a zero observation prefix forces the same coordinate prefix to vanish.

4. **Integral saturation.** Rational coordinates observed through a
   lower-unitriangular integer matrix are integral whenever the observations are
   integral.

5. **Integral divisibility preservation.** A lower-unitriangular integer change
   of coordinates preserves and reflects common divisibility.

6. **Abstract content theorem.** If every Fourier coefficient is an integer
   linear combination of residual coordinates and a selected finite block is
   lower-unitriangular, then an integer divides every Fourier coefficient iff it
   divides every residual coordinate. Over `ℤ`, this is the invariant content of
   the manuscript's gcd equality.

7. **Paper interface.** `OddJetBasisData` packages exactly the hypotheses needed
   to derive the odd-jet and content conclusions once the modular-form-specific
   input is supplied.

No `axiom`, `sorry`, or `admit` is used in the theorem files. This execution
environment did not contain Lean or Lake, so the project has **not yet been
kernel-checked here**. Run `lake build` before treating it as verified. The code
is structured to make compiler errors local and to expose every remaining
number-theoretic dependency.

## What is not yet formalized

A complete kernel-checked proof of the paper still requires:

- definitions of the explicit level-4 forms `B`, `C`, and `D`;
- the ring presentation `M_even(Γ₀(4); ℚ) = ℚ[B,D]`;
- the principal cusp-ideal statement `S_even = C · M_even`;
- the eta-quotient identities and cusp orders;
- the rational odd-support decomposition inside modular forms;
- the level-2 and level-4 Hecke matrices;
- Sturm-bound verification of the six exact factorizations.

These are isolated in `Gamma0FourFormalizationTargets`. They are not silently
assumed by the checked algebraic core.

## Why this split matters

The manuscript's conceptual risk lies in moving between geometric modular-form
statements and arithmetic lattice statements. This project makes that boundary
explicit:

- the modular-form geometry must supply the rational decomposition and the
  explicit q-expansion basis;
- the formalized unitriangular theorems then prove the arithmetic jet and content
  consequences.

Thus the code cannot validate the manuscript merely by restating its conclusion.
It identifies the exact number-theoretic obligations that remain.

## Build

Install Lean via `elan`, then run:

```bash
lake update
lake build
```

The project is pinned to Lean 4.32.2 and the matching mathlib tag.

## File map

- `OddSupportFiltration/Sequences.lean` — support, `U₂`, half-translation, odd jets.
- `OddSupportFiltration/TriangularJet.lean` — zero and divisibility recovery.
- `OddSupportFiltration/Saturation.lean` — rational-to-integral saturation.
- `OddSupportFiltration/ContentCertificate.lean` — global finite content certificate.
- `OddSupportFiltration/PaperInterface.lean` — interface to the manuscript.
- `FORMALIZATION_PLAN.md` — staged route to a complete modular-forms proof.
- `THEOREM_MAP.md` — exact status of every manuscript claim.
