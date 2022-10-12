import data.list.basic

namespace list

variable {α : Type*}

def shiftl_fill (l : list α) (n : ℕ) (a : α) : list α :=
list.drop n l ++ list.repeat a (min n l.length)

@[simp] lemma shiftl_fill_zero (l : list α) (a : α) : l.shiftl_fill 0 a = l :=
by simp [shiftl_fill]

@[simp] lemma shiftl_fill_nil (n : ℕ) (a : α) : shiftl_fill [] n a = [] :=
by simp [shiftl_fill]

@[simp] lemma shiftl_fill_cons_succ (l : list α) (n : ℕ) (a b : α) :
  shiftl_fill (a::l) (n+1) b = shiftl_fill l n b ++ [b] :=
by simp [shiftl_fill, min_def]; split_ifs; simp [repeat_add]

@[simp] lemma shiftl_fill_concat : Π (l : list α) (n : ℕ) (a : α),
  shiftl_fill (l ++ [a]) n a = shiftl_fill l n a ++ [a]
| [] 0 _ := by simp
| [] (n+1) _ := by simp
| (b::l) 0 _ := by simp
| (b::l) (n+1) a :=
  by rw [cons_append, shiftl_fill_cons_succ, shiftl_fill_concat, shiftl_fill_cons_succ]

@[simp] lemma shiftl_fill_append_repeat : Π (l : list α) (n m : ℕ) (a : α),
  shiftl_fill (l ++ repeat a m) n a = shiftl_fill l n a ++ repeat a m
| _ _ 0 _ := by simp
| l n (m+1) a :=
  by rw [repeat_add, ← append_assoc, repeat_succ, repeat, shiftl_fill_concat,
    shiftl_fill_append_repeat, append_assoc]

lemma shiftl_fill_add : Π (l : list α) (n m : ℕ) (a : α),
  shiftl_fill l (n + m) a = shiftl_fill (shiftl_fill l n a) m a
| []     _ _     _ := by simp
| (b::l) 0 _     _ := by simp
| (b::l) _ 0     _ := by simp
| (b::l) (nat.succ n) m a :=
  by rw [nat.succ_add, shiftl_fill_cons_succ, shiftl_fill_cons_succ, shiftl_fill_add, shiftl_fill_concat]

def shiftr_fill (l : list α) (n : ℕ) (a : α) : list α :=
repeat a (min n l.length) ++ list.take (l.length - n) l

lemma reverse_shiftl_fill (l : list α) (n : ℕ) (a : α) :
  (shiftl_fill l n a).reverse = shiftr_fill l.reverse n a :=
begin
  simp only [shiftr_fill, shiftl_fill, reverse_take, reverse_append, reverse_repeat,
    length_reverse, tsub_le_self],
  by_cases h : n ≤ l.length,
  { rw [nat.sub_sub_self h] },
  { rw [nat.sub_eq_zero_of_le (le_of_not_ge h), nat.sub_zero, min_eq_right (le_of_not_ge h)],
    simp [drop_eq_nil_of_le (le_of_not_ge h)] }
end

lemma reverse_shiftr_fill (l : list α) (n : ℕ) (a : α) :
  (shiftr_fill l n a).reverse = shiftl_fill l.reverse n a :=
begin
  have := reverse_shiftl_fill l.reverse n a,
  rw reverse_reverse at this,
  rw [← this, reverse_reverse]
end

@[simp] lemma shiftr_fill_zero (l : list α) (a : α) : l.shiftr_fill 0 a = l :=
by simp [shiftr_fill]

@[simp] lemma shiftr_fill_nil (n : ℕ) (a : α) : shiftr_fill [] n a = [] :=
by simp [shiftr_fill]

@[simp] lemma shiftr_fill_concat_succ (l : list α) (n : ℕ) (a b : α) :
  shiftr_fill (l++[a]) (n+1) b = b :: shiftr_fill l n b :=
begin
  apply reverse_injective,
  rw [reverse_shiftr_fill, reverse_append, reverse_singleton, singleton_append,
    shiftl_fill_cons_succ, reverse_cons, reverse_shiftr_fill]
end

end list