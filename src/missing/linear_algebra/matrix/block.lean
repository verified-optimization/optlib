import linear_algebra.matrix.block linear_algebra.matrix.nonsingular_inverse
  missing.linear_algebra.matrix.nonsingular_inverse
  missing.data.matrix.block
  missing.data.fintype.basic

namespace matrix
open_locale matrix
open finset
universes v
variables {α β m n o : Type*} {m' n' : α → Type*}
variables {R : Type v} [comm_ring R] {M : matrix m m R} {b : m → α}

section has_lt
variable [has_lt α]

lemma block_triangular_zero : block_triangular (0 : matrix m m R) b := λ i j h, rfl

protected lemma block_triangular.neg (hM : block_triangular M b) :
  block_triangular (- M) b :=
λ i j h, show - M i j = 0, by rw [hM h, neg_zero]

lemma block_triangular.add {M N : matrix m m R}
    (hM : block_triangular M b) (hN : block_triangular N b) :
  block_triangular (M + N) b :=
λ i j h, show M i j + N i j = 0, by rw [hM h, hN h, zero_add]

lemma block_triangular.sub {M N : matrix m m R}
    (hM : block_triangular M b) (hN : block_triangular N b) :
  block_triangular (M - N) b :=
λ i j h, show M i j - N i j = 0, by rw [hM h, hN h, zero_sub_zero]

end has_lt

section preorder
variables [preorder α]

lemma block_triangular_diagonal [decidable_eq m] (d : m → R) :
  block_triangular (diagonal d) b :=
λ i j h, diagonal_apply_ne' d (λ h', ne_of_lt h (congr_arg _ h'))

lemma block_triangular_block_diagonal' [decidable_eq α] (d : Π (i : α), matrix (m' i) (m' i) R) :
  block_triangular (block_diagonal' d) sigma.fst :=
begin
  rintros ⟨i, i'⟩ ⟨j, j'⟩ h,
  apply block_diagonal'_apply_ne d i' j' (λ h', ne_of_lt h h'.symm),
end

lemma block_triangular_block_diagonal [decidable_eq α] (d : α → matrix m m R) :
  block_triangular (block_diagonal d) prod.snd :=
begin
  rintros ⟨i, i'⟩ ⟨j, j'⟩ h,
  rw [block_diagonal'_eq_block_diagonal, block_triangular_block_diagonal'],
  exact h
end

end preorder

section linear_order
variables [linear_order α]

lemma block_triangular.mul [fintype m]
  {M N : matrix m m R} (hM : block_triangular M b) (hN : block_triangular N b):
  block_triangular (M * N) b :=
begin
  intros i j hij,
  apply finset.sum_eq_zero,
  intros k hk,
  by_cases hki : b k < b i,
  { simp_rw [hM hki, zero_mul], },
  { simp_rw [hN (lt_of_lt_of_le hij (le_of_not_lt hki)), mul_zero] },
end

end linear_order


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

/-- A lower-left subblock of the inverse of a block-triangular matrix is zero. This is a first step
towards `block_triangular_inv_of_block_triangular` below. -/
lemma to_block_inverse_eq_zero [linear_order α]
  [invertible M] (hM : block_triangular M b) (k : α) :
  M⁻¹.to_block (λ i, k ≤ b i) (λ i, b i < k) = 0 :=
begin
  have := mul_inv_of_invertible M,
  have h_iff : (λ i, k ≤ b i) = (λ i, ¬ b i < k),
  { ext i, simp },
  let p := (λ i, b i < k),
  let q := (λ i, ¬ b i < k),
  have h_sum : M⁻¹.to_block q p ⬝ M.to_block p p +
      M⁻¹.to_block q q ⬝ M.to_block q p = 0,
  { rw [←to_block_mul_eq_add, inv_mul_of_invertible M, to_block_one_disjoint],
    rintros i ⟨hq, hp⟩, exact hq hp },
  have h_zero : M.to_block q p = 0,
  { ext i j,
    simpa using hM (lt_of_lt_of_le j.2 (le_of_not_lt i.2)) },
  have h_mul_eq_zero : M⁻¹.to_block q p ⬝ M.to_block p p = 0,
    by simpa [h_zero] using h_sum,
  haveI : invertible (M.to_block p p) := invertible_to_block_of_block_triangular hM k,
  rw [h_iff, ← matrix.zero_mul (M.to_block p p)⁻¹, ← h_mul_eq_zero,
    mul_inv_cancel_right_of_invertible],
end

/-- The inverse of a block-triangular matrix is block-triangular. -/
lemma block_triangular_inv_of_block_triangular
    [invertible M] [linear_order α] (hM : block_triangular M b) :
  block_triangular M⁻¹ b :=
begin
  unfreezingI { induction hs : univ.image b using finset.strong_induction
    with s ih generalizing m },
  subst hs,
  by_cases h : univ.image b = ∅,
  { intros i j,
    rw [image_eq_empty, univ_eq_empty_iff] at h,
    exact false.elim (@is_empty.false _ h i) },
  { let k := (univ.image b).max' (nonempty_of_ne_empty h),
    let b' := λ i : {a // b a < k}, b ↑i,
    let A := M.to_block (λ i, b i < k) (λ j, b j < k),
    let B := M.to_block (λ i, b i < k) (λ j, b j ≤ k),
    let C := M.to_block (λ i, b i ≤ k) (λ j, b j < k),
    let D := M.to_block (λ i, b i ≤ k) (λ j, b j ≤ k),
    show M⁻¹.block_triangular b,
    { intros i j hij,
      by_cases hbi : b i = k,
      { have hi : k ≤ b i := le_of_eq hbi.symm,
        have hj : b j < k := hbi ▸ hij,
        have : M⁻¹.to_block (λ (i : m), k ≤ b i) (λ (i : m), b i < k) ⟨i, hi⟩ ⟨j, hj⟩ = 0 :=
          by simp only [to_block_inverse_eq_zero hM k, pi.zero_apply],
        simp [this.symm] },
      { haveI : invertible A,
        { apply invertible_to_block_of_block_triangular hM },
        have hA : A.block_triangular b',
        { intros i j, apply hM },
        have hb' : image b' univ ⊂ (image b univ),
        { convert image_subtype_univ_ssubset_image_univ k b _ (λ a, a < k) (lt_irrefl _),
          convert max'_mem _ _, },
        have hA : A⁻¹.block_triangular b',
          from ih (image b' univ) hb' hA rfl,
        have hi : b i < k,
          from lt_of_le_of_ne (le_max' (univ.image b) (b i) (mem_image_of_mem _ (mem_univ _))) hbi,
        have hj : b j < k, from lt_trans hij hi,
        have hij' : b' ⟨j, hj⟩ < b' ⟨i, hi⟩, by simp_rw [b', subtype.coe_mk, hij],
        have hA := hA hij',
        have h_A_inv: A⁻¹ = M⁻¹.to_block (λ (i : m), b i < k) (λ (i : m), b i < k),
        { simp_rw [A],
          exact inv_to_block_of_block_triangular hM k },
        rw h_A_inv at hA,
        simp [hA.symm] } } }
end

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
  simpa [h_zero'] using h_sum
end

end matrix
