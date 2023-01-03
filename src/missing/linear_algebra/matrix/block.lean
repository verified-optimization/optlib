import linear_algebra.matrix.block linear_algebra.matrix.nonsingular_inverse
  missing.data.fintype.basic

namespace matrix
open_locale matrix
open finset
universes v
variables {α β m n o : Type*} {m' n' : α → Type*}
variables {R : Type v} [comm_ring R] {M : matrix m m R} {b : m → α}


/-! ### Invertible -/
variables [decidable_eq m] [fintype m] [decidable_eq n] [fintype n]

lemma to_block_inverse_mul_to_block_eq_one_of_block_triangular [linear_order α]
  [invertible M] (hM : block_triangular M b) (k : α) :
  M⁻¹.to_block (λ i, b i < k) (λ i, b i < k) ⬝ M.to_block (λ i, b i < k) (λ i, b i < k) = 1 :=
begin
  let p := (λ i, b i < k),
  have h_sum : M⁻¹.to_block p p ⬝ M.to_block p p +
      M⁻¹.to_block p (λ i, ¬ p i) ⬝ M.to_block (λ i, ¬ p i) p = 1,
    by rw [←to_block_mul_eq_add, inv_mul_of_invertible M, to_block_one_self],
  have h_zero : M.to_block (λ i, ¬ p i) p = 0,
  { ext i j,
    simpa using hM (lt_of_lt_of_le j.2 (le_of_not_lt i.2)) },
  simpa [h_zero] using h_sum
end

/-- The inverse of an upper-left subblock of a block-triangular matrix `M` is the upper-left
subblock of `M⁻¹`. -/
lemma inv_to_block_of_block_triangular [linear_order α]
  [invertible M] (hM : block_triangular M b) (k : α) :
  (M.to_block (λ i, b i < k) (λ i, b i < k))⁻¹ = M⁻¹.to_block (λ i, b i < k) (λ i, b i < k) :=
inv_eq_left_inv (to_block_inverse_mul_to_block_eq_one_of_block_triangular hM k)

/-- An upper-left subblock of an invertible block-triangular matrix is invertible. -/
def invertible_to_block_of_block_triangular
  [linear_order α] [invertible M] (hM : block_triangular M b) (k : α) :
  invertible (M.to_block (λ i, b i < k) (λ i, b i < k)) :=
invertible_of_left_inverse _ ((⅟M).to_block (λ i, b i < k) (λ i, b i < k))
  (by simpa only [inv_of_eq_nonsing_inv]
    using to_block_inverse_mul_to_block_eq_one_of_block_triangular hM k)

lemma to_square_block_inv_mul_to_square_block_eq_one [linear_order α]
  [invertible M] (hM : block_triangular M b) (k : α) :
  M⁻¹.to_square_block b k ⬝ M.to_square_block b k = 1 :=
begin
  let p := (λ i, b i = k),
  have h_sum : M⁻¹.to_block p p ⬝ M.to_block p p +
      M⁻¹.to_block p (λ i, ¬ p i) ⬝ M.to_block (λ i, ¬ p i) p = 1,
    by rw [←to_block_mul_eq_add, inv_mul_of_invertible M, to_block_one_self],
  have h_zero :
    ∀ i j l, M⁻¹.to_block p (λ (i : m), ¬p i) i j * M.to_block (λ (i : m), ¬p i) p j l = 0,
  { intros i j l,
    by_cases hj : b j.1 ≤ k,
    { have hj := lt_of_le_of_ne hj j.2,
      have hM' := block_triangular_inv_of_block_triangular hM,
      apply mul_eq_zero_of_left,
      simpa using hM' (lt_of_lt_of_eq hj i.2.symm) },
    { have hj := lt_of_not_ge hj,
      apply mul_eq_zero_of_right,
      simpa using hM (lt_of_eq_of_lt l.2 hj) }},
  have h_zero' : M⁻¹.to_block p (λ (i : m), ¬p i) ⬝ M.to_block (λ (i : m), ¬p i) p = 0,
  { ext i l,
    apply sum_eq_zero (λ j hj, h_zero i j l) },
  simpa [h_zero'] using h_sum,
end

end matrix
