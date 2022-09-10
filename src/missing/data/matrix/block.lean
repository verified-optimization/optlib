import data.matrix.block

namespace matrix
open_locale matrix
variables {l m α R : Type*}
variables [decidable_eq l] [decidable_eq m]

section has_zero
variables [has_zero α]

lemma to_block_diagonal_self (d : m → α) (p : m → Prop) :
  matrix.to_block (diagonal d) p p = diagonal (λ i : subtype p, d ↑i) :=
begin
  ext i j,
  by_cases i = j,
  { simp [h] },
  { simp [has_one.one, h, λ h', h $ subtype.ext h'], }
end

lemma to_block_diagonal_disjoint (d : m → α) {p q : m → Prop} (hpq : disjoint p q) :
  matrix.to_block (diagonal d) p q = 0 :=
begin
  ext ⟨i, hi⟩ ⟨j, hj⟩,
  have : i ≠ j, from λ heq, hpq i ⟨hi, heq.symm ▸ hj⟩,
  simp [diagonal_apply_ne d this]
end

end has_zero

section has_zero_has_one
variables [has_zero α] [has_one α]

lemma to_block_one_self (p : m → Prop) : matrix.to_block (1 : matrix m m α) p p = 1 :=
to_block_diagonal_self _ p

lemma to_block_one_disjoint {p q : m → Prop} (hpq : disjoint p q) :
  matrix.to_block (1 : matrix m m α) p q = 0 :=
to_block_diagonal_disjoint _ hpq

end has_zero_has_one


section
variables [comm_ring R]

lemma to_block_mul_eq_mul {m n k : Type*} [fintype n] (p : m → Prop) (q : k → Prop)
  (A : matrix m n R) (B : matrix n k R) :
  (A ⬝ B).to_block p q = A.to_block p ⊤ ⬝ B.to_block ⊤ q :=
begin
  ext i k,
  simp only [to_block_apply, mul_apply],
  rw finset.sum_subtype,
  simp [has_top.top, complete_lattice.top, bounded_order.top],
end

lemma to_block_mul_eq_add
  {m n k : Type*} [fintype n] (p : m → Prop) (q : n → Prop) [decidable_pred q] (r : k → Prop)
  (A : matrix m n R) (B : matrix n k R) :
  (A ⬝ B).to_block p r =
    A.to_block p q ⬝ B.to_block q r + A.to_block p (λ i, ¬ q i) ⬝ B.to_block (λ i, ¬ q i) r :=
begin
  classical,
  ext i k,
  simp only [to_block_apply, mul_apply, pi.add_apply],
  convert (fintype.sum_subtype_add_sum_subtype q (λ x, A ↑i x * B x ↑k)).symm
end

end

end matrix