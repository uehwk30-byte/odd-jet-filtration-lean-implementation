import OddSupportFiltration.Sequences

/-!
# Unitriangular jet coordinates

This file isolates the algebraic engine used in the manuscript's saturation and
odd-jet filtration arguments.  A lower-unitriangular observation map has the form

`yᵢ = cᵢ + ∑_{j<i} aᵢⱼ cⱼ`.

The first theorem says that a vanishing prefix of observations forces the same
prefix of coordinates to vanish.  The second says that divisibility of a prefix
of observations by an integer is equivalent to divisibility of the corresponding
coordinate prefix.
-/

namespace OddSupportFiltration

/-- A generic lower-unitriangular transform of an integer coordinate sequence. -/
def lowerTransform (a : ℕ → ℕ → ℤ) (c : ℕ → ℤ) (i : ℕ) : ℤ :=
  c i + ∑ j in Finset.range i, a i j * c j

/-- A zero prefix of a lower-unitriangular transform forces the coordinate prefix to vanish. -/
theorem coords_zero_of_lowerTransform_zero_prefix
    (a : ℕ → ℕ → ℤ) (c : ℕ → ℤ) (n : ℕ)
    (h : ∀ i : ℕ, i < n → lowerTransform a c i = 0) :
    ∀ i : ℕ, i < n → c i = 0 := by
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
        have hprev : ∀ j : ℕ, j < n → c j = 0 :=
          ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n)))
        have hsum : (∑ j in Finset.range n, a n j * c j) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hjn : j < n := Finset.mem_range.mp hj
          simp [hprev j hjn]
        have hn := h n (Nat.lt_succ_self n)
        simp [lowerTransform, hsum] at hn
        exact hn

/--
Divisibility of the first `n` lower-unitriangular observations forces divisibility
of the first `n` coordinates.
-/
theorem dvd_coords_of_dvd_lowerTransform_prefix
    (a : ℕ → ℕ → ℤ) (c : ℕ → ℤ) (m : ℤ) (n : ℕ)
    (h : ∀ i : ℕ, i < n → m ∣ lowerTransform a c i) :
    ∀ i : ℕ, i < n → m ∣ c i := by
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
        have hprev : ∀ j : ℕ, j < n → m ∣ c j :=
          ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n)))
        have hsum : m ∣ ∑ j in Finset.range n, a n j * c j := by
          apply Finset.dvd_sum
          intro j hj
          rcases hprev j (Finset.mem_range.mp hj) with ⟨z, hz⟩
          refine ⟨a n j * z, ?_⟩
          rw [hz]
          ring
        rcases h n (Nat.lt_succ_self n) with ⟨x, hx⟩
        rcases hsum with ⟨y, hy⟩
        refine ⟨x - y, ?_⟩
        calc
          c n = lowerTransform a c n - ∑ j in Finset.range n, a n j * c j := by
            simp [lowerTransform]
          _ = m * x - m * y := by rw [hx, hy]
          _ = m * (x - y) := by ring

/-- Coordinate divisibility implies divisibility of every lower-unitriangular observation. -/
theorem dvd_lowerTransform_of_dvd_coords_prefix
    (a : ℕ → ℕ → ℤ) (c : ℕ → ℤ) (m : ℤ) (n : ℕ)
    (h : ∀ i : ℕ, i < n → m ∣ c i) :
    ∀ i : ℕ, i < n → m ∣ lowerTransform a c i := by
  intro i hi
  have hci : m ∣ c i := h i hi
  have hsum : m ∣ ∑ j in Finset.range i, a i j * c j := by
    apply Finset.dvd_sum
    intro j hj
    rcases h j (lt_trans (Finset.mem_range.mp hj) hi) with ⟨z, hz⟩
    refine ⟨a i j * z, ?_⟩
    rw [hz]
    ring
  rcases hci with ⟨x, hx⟩
  rcases hsum with ⟨y, hy⟩
  refine ⟨x + y, ?_⟩
  calc
    lowerTransform a c i = c i + ∑ j in Finset.range i, a i j * c j := rfl
    _ = m * x + m * y := by rw [hx, hy]
    _ = m * (x + y) := by ring

/-- Divisibility is preserved and reflected by a lower-unitriangular coordinate change. -/
theorem dvd_lowerTransform_prefix_iff
    (a : ℕ → ℕ → ℤ) (c : ℕ → ℤ) (m : ℤ) (n : ℕ) :
    (∀ i : ℕ, i < n → m ∣ lowerTransform a c i) ↔
      (∀ i : ℕ, i < n → m ∣ c i) := by
  constructor
  · exact dvd_coords_of_dvd_lowerTransform_prefix a c m n
  · exact dvd_lowerTransform_of_dvd_coords_prefix a c m n

end OddSupportFiltration
