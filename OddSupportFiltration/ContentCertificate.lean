import OddSupportFiltration.TriangularJet

/-!
# Finite content certificates

The manuscript's content theorem can be expressed without first choosing a
particular gcd normalization.  The strongest invariant statement is that an
integer divides every Fourier coefficient if and only if it divides every
residual coordinate.  Equality of the corresponding nonnegative gcds is an
immediate corollary in `ℤ`.
-/

namespace OddSupportFiltration

/-- Every coefficient of `H` is an integer linear combination of the first `n` coordinates. -/
def GeneratedByPrefix (n : ℕ) (c : ℕ → ℤ) (H : ZSeries) : Prop :=
  ∀ k : ℕ, ∃ w : Fin n → ℤ, H k = ∑ j : Fin n, w j * c j

/--
A finite lower-unitriangular block of selected Fourier coefficients, together with
integer generation of all coefficients, is a complete divisibility certificate.

This is the abstract arithmetic core of Theorem 5.1.
-/
theorem global_dvd_iff_coordinate_dvd
    (n : ℕ) (a : ℕ → ℕ → ℤ) (c : ℕ → ℤ) (H : ZSeries)
    (pick : ℕ → ℕ)
    (hselected : ∀ i : ℕ, i < n → H (pick i) = lowerTransform a c i)
    (hgenerated : GeneratedByPrefix n c H)
    (m : ℤ) :
    (∀ k : ℕ, m ∣ H k) ↔ (∀ i : ℕ, i < n → m ∣ c i) := by
  constructor
  · intro hall
    apply dvd_coords_of_dvd_lowerTransform_prefix a c m n
    intro i hi
    rw [← hselected i hi]
    exact hall (pick i)
  · intro hcoords k
    rcases hgenerated k with ⟨w, hw⟩
    rw [hw]
    apply Finset.dvd_sum
    intro j hj
    rcases hcoords j.1 j.2 with ⟨z, hz⟩
    refine ⟨w j * z, ?_⟩
    rw [hz]
    ring

/-- Two coefficient families have the same set of common integer divisors. -/
def SameCommonDivisors (H : ZSeries) (n : ℕ) (c : ℕ → ℤ) : Prop :=
  ∀ m : ℤ, (∀ k : ℕ, m ∣ H k) ↔ (∀ i : ℕ, i < n → m ∣ c i)

/-- The hypotheses of `global_dvd_iff_coordinate_dvd` yield equality of common-divisor data. -/
theorem sameCommonDivisors_of_certificate
    (n : ℕ) (a : ℕ → ℕ → ℤ) (c : ℕ → ℤ) (H : ZSeries)
    (pick : ℕ → ℕ)
    (hselected : ∀ i : ℕ, i < n → H (pick i) = lowerTransform a c i)
    (hgenerated : GeneratedByPrefix n c H) :
    SameCommonDivisors H n c := by
  intro m
  exact global_dvd_iff_coordinate_dvd n a c H pick hselected hgenerated m

end OddSupportFiltration
