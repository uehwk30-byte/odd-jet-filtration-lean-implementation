import OddSupportFiltration.TriangularJet

/-!
# Rational coordinates and integral saturation

This file formalizes the arithmetic step in Theorem 4.1.  If rational coordinates
are observed through a lower-unitriangular matrix with integer entries, and the
observed coefficients are integral, then the coordinates themselves are integral.
-/

namespace OddSupportFiltration

/-- A rational number is integral when it is the image of an integer. -/
def IsIntegralRat (x : ℚ) : Prop := ∃ z : ℤ, x = (z : ℚ)

namespace IsIntegralRat

@[simp] theorem zero : IsIntegralRat 0 := ⟨0, by simp⟩

 theorem add {x y : ℚ} (hx : IsIntegralRat x) (hy : IsIntegralRat y) :
    IsIntegralRat (x + y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a + b, by norm_num⟩

 theorem neg {x : ℚ} (hx : IsIntegralRat x) : IsIntegralRat (-x) := by
  rcases hx with ⟨a, rfl⟩
  exact ⟨-a, by norm_num⟩

 theorem sub {x y : ℚ} (hx : IsIntegralRat x) (hy : IsIntegralRat y) :
    IsIntegralRat (x - y) := by
  simpa [sub_eq_add_neg] using add hx (neg hy)

 theorem int_mul (a : ℤ) {x : ℚ} (hx : IsIntegralRat x) :
    IsIntegralRat ((a : ℚ) * x) := by
  rcases hx with ⟨b, rfl⟩
  exact ⟨a * b, by norm_num⟩

 theorem finset_sum {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, IsIntegralRat (f i)) :
    IsIntegralRat (∑ i in s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply add
      · exact h a (by simp)
      · exact ih (fun i hi => h i (by simp [hi]))

end IsIntegralRat

/-- A lower-unitriangular transform of rational coordinates with integer lower entries. -/
def lowerTransformQ (a : ℕ → ℕ → ℤ) (c : ℕ → ℚ) (i : ℕ) : ℚ :=
  c i + ∑ j in Finset.range i, (a i j : ℚ) * c j

/--
Integral lower-unitriangular observations force the corresponding rational
coordinates to be integral.  This is the formal saturation mechanism.
-/
theorem integral_coords_of_integral_lowerTransform_prefix
    (a : ℕ → ℕ → ℤ) (c : ℕ → ℚ) (n : ℕ)
    (h : ∀ i : ℕ, i < n → IsIntegralRat (lowerTransformQ a c i)) :
    ∀ i : ℕ, i < n → IsIntegralRat (c i) := by
  induction n with
  | zero =>
      intro i hi
      omega
  | succ n ih =>
      intro i hi
      by_cases hin : i < n
      · exact ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n))) i hin
      · have hieq : i = n := by omega
        subst i
        have hprev : ∀ j : ℕ, j < n → IsIntegralRat (c j) :=
          ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n)))
        have hsum : IsIntegralRat (∑ j in Finset.range n, (a n j : ℚ) * c j) := by
          apply IsIntegralRat.finset_sum
          intro j hj
          exact IsIntegralRat.int_mul (a n j) (hprev j (Finset.mem_range.mp hj))
        have hobs := h n (Nat.lt_succ_self n)
        have hdiff : c n = lowerTransformQ a c n -
            ∑ j in Finset.range n, (a n j : ℚ) * c j := by
          simp [lowerTransformQ]
        rw [hdiff]
        exact IsIntegralRat.sub hobs hsum

end OddSupportFiltration
