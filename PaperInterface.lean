import OddSupportFiltration.Saturation
import OddSupportFiltration.ContentCertificate

/-!
# Interface to the manuscript

This file records the exact boundary between the machine-checked algebraic core
and the modular-form-specific input that remains to be formalized in mathlib.

No theorem below assumes that the manuscript-specific facts are already available
in mathlib.  Instead, `OddJetBasisData` packages precisely the data used by the
paper's proofs after the rational decomposition has been established.
-/

namespace OddSupportFiltration

/--
Data supplied by one fixed weight branch of the manuscript.

* `rank` is the rank of the odd-support lattice.
* `basis j` is the `j`th proposed integral basis vector.
* `coordinates` is the residual coordinate vector of a form represented in this basis.
* `series` is its Fourier expansion.
* `triangular` says that the first `rank` odd coefficients are a lower-unitriangular
  transform of the coordinates.
* `generated` says that every Fourier coefficient is an integer linear combination
  of the coordinates.

For the manuscript, the basis vectors are
`CB(B²)^(d-j)(D²)^j` in weights divisible by four and
`C(B²)^(d-j)(D²)^j` in weights congruent to two modulo four.
-/
structure OddJetBasisData where
  rank : ℕ
  offset : ℕ
  basis : Fin rank → ZSeries
  coordinates : ℕ → ℤ
  series : ZSeries
  lower : ℕ → ℕ → ℤ
  triangular : ∀ i : ℕ, i < rank →
    series ((offset + i) + (offset + i) + 1) = lowerTransform lower coordinates i
  generated : GeneratedByPrefix rank coordinates series

/-- The abstract content theorem attached to one branch of manuscript data. -/
theorem OddJetBasisData.content_certificate (D : OddJetBasisData) (m : ℤ) :
    (∀ k : ℕ, m ∣ D.series k) ↔
      (∀ i : ℕ, i < D.rank → m ∣ D.coordinates i) := by
  exact global_dvd_iff_coordinate_dvd
    D.rank D.lower D.coordinates D.series
    (fun i => (D.offset + i) + (D.offset + i) + 1)
    D.triangular D.generated m

/-- A vanishing prefix of odd coefficients forces the same coordinate prefix to vanish. -/
theorem OddJetBasisData.zero_coordinates_of_zero_odd_jet
    (D : OddJetBasisData) (s : ℕ) (hs : s ≤ D.rank)
    (hjet : ∀ i : ℕ, i < s →
      D.series ((D.offset + i) + (D.offset + i) + 1) = 0) :
    ∀ i : ℕ, i < s → D.coordinates i = 0 := by
  apply coords_zero_of_lowerTransform_zero_prefix D.lower D.coordinates s
  intro i hi
  rw [← D.triangular i (lt_of_lt_of_le hi hs)]
  exact hjet i hi

/--
The modular-form-specific facts still required for a complete formalization of the
paper.  This declaration is documentation, not an axiom used by the checked core.
-/
structure Gamma0FourFormalizationTargets where
  /-- Formal definitions of the level-four forms `B`, `C`, and `D`. -/
  hasExplicitForms : Prop
  /-- `M_even(Γ₀(4); ℚ) = ℚ[B,D]`. -/
  hasRationalRingPresentation : Prop
  /-- `S_even(Γ₀(4); ℚ) = C · ℚ[B,D]`. -/
  hasPrincipalCuspIdeal : Prop
  /-- The parity statements for the `q`-expansions of `B`, `C`, and `D`. -/
  hasParityExpansions : Prop
  /-- The leading terms `e_j = q^(2j+1) + O(q^(2j+3))`. -/
  hasUnitriangularLeadingTerms : Prop
  /-- The six low-weight Hecke identities and their Sturm-bound certificates. -/
  hasHeckeComputations : Prop

end OddSupportFiltration
