import data.fintype.basic

namespace finset
variables {α β : Type*} [decidable_eq β]

lemma image_subtype_ne_univ_eq_image_erase [fintype α] (k : β) (b : α → β) :
  image (λ i : {a // b a ≠ k}, b ↑i) univ = (image b univ).erase k :=
begin
  apply subset_antisymm,
  { rw image_subset_iff,
    intros i _,
    apply mem_erase_of_ne_of_mem i.2 (mem_image_of_mem _ (mem_univ _)) },
  { intros i hi,
    rw mem_image,
    rcases mem_image.1 (erase_subset _ _ hi) with ⟨a, _, ha⟩,
    subst ha,
    exact ⟨⟨a, ne_of_mem_erase hi⟩, mem_univ _, rfl⟩ }
end

lemma image_subtype_univ_ssubset_image_univ [fintype α] (k : β) (b : α → β)
  (hk : k ∈ image b univ) (p : β → Prop) [decidable_pred p] (hp : ¬ p k) :
  image (λ i : {a // p (b a)}, b ↑i) univ ⊂ image b univ :=
begin
  split,
  { intros x hx,
    rcases mem_image.1 hx with ⟨y, _, hy⟩,
    exact hy ▸ mem_image_of_mem b (mem_univ y) },
  { intros h,
    rw mem_image at hk,
    rcases hk with ⟨k', _, hk'⟩, subst hk',
    have := h (mem_image_of_mem b (mem_univ k')),
    rw mem_image at this,
    rcases this with ⟨j, hj, hj'⟩,
    exact hp (hj' ▸ j.2) }
end

end finset