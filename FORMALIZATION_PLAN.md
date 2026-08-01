# Formalization plan

## Phase 1 — arithmetic core

Status: implemented in this repository.

- coefficient sequences;
- odd support and half-translation anti-invariance;
- odd-jet vanishing;
- lower-unitriangular recovery;
- divisibility/content certificate.

## Phase 2 — formal q-series identities

Define the explicit coefficient series for `B`, `C`, and `D`, then prove:

- `B` contains only even powers of `q`;
- `C` and `D` contain only odd powers;
- `B(0) = 1`, `C(q) = q + O(q³)`, `D(q) = q + O(q³)`;
- `C = D(B² - 64D²)` as formal q-series to a certified Sturm bound.

This phase can initially avoid analytic modular forms and verify exact coefficient
identities in `PowerSeries ℤ`.

## Phase 3 — modularity and the ring presentation

Using mathlib's modular-form, congruence-subgroup, q-expansion, Eisenstein-series,
and Dedekind-eta infrastructure, define the analytic forms and prove:

- `A ∈ M₂(Γ₀(2))` and `B,D ∈ M₂(Γ₀(4))`;
- `C ∈ S₆(Γ₀(4))`;
- the cusp divisor of `C`;
- `M_even(Γ₀(4); ℚ) = ℚ[B,D]`;
- `S_even(Γ₀(4); ℚ) = C · ℚ[B,D]`.

The dimension formulas and q-expansion injectivity are the main library-facing
obligations.

## Phase 4 — instantiate the abstract odd-jet model

Construct `OddJetBasisData` in each weight branch from the monomial basis and
prove its `triangular` and `generated` fields. The checked theorems in this
repository then yield:

- integral saturation;
- the exact odd-jet filtration;
- matching-jet factorization;
- the content theorem.

## Phase 5 — Hecke applications

Formalize:

- `U₂`, `T₃`, degeneracy maps, and 2-depletion;
- the explicit matrices in weights 12, 16, and 20;
- characteristic polynomials and simple roots;
- the six coordinate factorizations;
- optimality of the six congruence moduli via the content certificate.

## Recommended publication claim

Until Phases 2–5 are complete and `lake build` succeeds without axioms, the Lean
work should be described as a **formalization of the algebraic core and a precise
formal dependency audit**, not as a complete formal verification of the paper.
