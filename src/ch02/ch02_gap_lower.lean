-- Proves that there exists unbounded gaps between primes.

import data.nat.factors
import data.set.intervals.monoid

@[simp]
def prime_range : ℕ → list ℕ := list.filter nat.prime ∘ list.range

@[simp]
def prod_prime_range : ℕ → ℕ  := list.prod ∘ prime_range

namespace prime_range

lemma prod_ne_zero {k : ℕ} : prod_prime_range k ≠ 0 :=
  by simp [nat.not_prime_zero]

lemma prod_pos {k : ℕ} : 0 < list.prod (prime_range k) :=
  nat.pos_of_ne_zero prod_ne_zero

lemma prod_dvd_of_lt {k p : ℕ} (hp : nat.prime p) (hk : p < k) : p ∣ prod_prime_range k :=
begin
  simp,
  apply list.dvd_prod,
  simp,
  exact and.intro hk hp
end

-- Not needed for proof.
lemma prod_monotone {a b : ℕ} (h : a ≤ b) : prod_prime_range a ≤ prod_prime_range b :=
begin
  simp [prod_prime_range],
  replace h := nat.exists_eq_add_of_le' h,
  cases h with x hx,
  rw hx,
  simp [list.range_eq_range'],
  rw ← list.range'_append,
  simp,
  apply nat.le_mul_of_pos_right,
  simp,
  assume u _ _,
  exact nat.prime.pos,
end

-- Not needed for proof.
lemma one_lt_prod {k : ℕ} (hk : 2 < k) : 1 < prod_prime_range k :=
begin
  simp [prod_prime_range],
  apply list.one_lt_prod_of_one_lt,
    simp,
    assume p _,
    exact nat.prime.one_lt,
  simp [list.filter_eq_nil],
  existsi 2,
  exact and.intro hk nat.prime_two,
end

end prime_range

lemma gap_after_prod_prime_range (k u : ℕ) :
  u ∈ set.Icc 2 k.succ → ¬nat.prime (prod_prime_range k.succ.succ + u) :=
begin
  assume hu,
  rw nat.prime_def_lt',
  simp,
  assume _,
  have hp := nat.exists_prime_and_dvd (_ : u ≠ 1),
    cases hp with p hp,
    existsi p,
    constructor,
      exact nat.prime.two_le hp.left,
    have hu' := lt_of_lt_of_le (dec_trivial : 0 < 2) hu.left,
    have hp' := nat.le_of_dvd hu' hp.right,
    constructor,
      apply lt_of_le_of_lt hp',
      apply lt_add_of_pos_left,
      exact prime_range.prod_pos,
    apply nat.dvd_add _ hp.right,
    apply prime_range.prod_dvd_of_lt hp.left,
    rw nat.lt_succ_iff,
    exact le_trans hp' hu.right,
  apply ne_of_gt,
  exact nat.lt_of_succ_le hu.left,
end

theorem exists_gap (k : ℕ) :
  ∃ m, ∀ x, x ∈ set.Icc (m+1) (m+k) → ¬nat.prime x :=
begin
  generalize hn : prod_prime_range k.succ.succ = n,
  existsi n + 1,
  assume x hx,
  have h : ∀ p q, n + p + q = (p + q) + n := _, swap,
  { assume p q, rw add_assoc, rw add_comm, },
  rw [h, h] at hx,
  clear h,
  rw ← set.image_add_const_Icc at hx,
  rw set.mem_image at hx,
  cases hx with u hu,
  cases hu with hu hx,
  rw ← hx,
  rw ← hn,
  rw add_comm,
  apply gap_after_prod_prime_range,
  rw [nat.one_add, nat.one_add] at hu,
  exact hu,
end