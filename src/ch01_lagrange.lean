-- Proves infinitude of primes using group theory.

import data.nat.basic
import data.nat.prime
import data.zmod.basic
import field_theory.finite.basic  -- order_of_dvd_card_sub_one
import group_theory.order_of_element  -- order_of_eq_prime
import order.monotone.basic

-- Two important properties:
#check @zmod.order_of_dvd_card_sub_one
#check @order_of_eq_prime


def mersenne (n : ℕ) := 2 ^ n - 1  -- number_theory.lucas_lehmer

-- 2 ≠ 1 in F_q for q ≥ 2.
-- Useful for order_of_eq_prime.
lemma zmod_two_ne_one {q : ℕ} : 2 ≤ q → (2 : zmod q) ≠ 1 :=
begin
  intro hq,
  simp,
  have h_mod := @zmod.eq_iff_modeq_nat q 2 1,
  simp at h_mod,  -- Need to simp before rw (lifts constants to zmod q).
  rw h_mod,
  have hq := has_le.le.eq_or_lt hq,
  cases hq with hq hq,
    rw ← hq, dec_trivial,
  intro h,
  have h := nat.modeq.eq_of_lt_of_lt h hq _,
    -- 2 ≡ 0 [MOD q] with q = 2
    simp at h, exact h,
  -- 2 ≡ 2 [MOD q] with q > 2
  apply lt_trans _ hq,  -- 1 < 2 < q
  dec_trivial,
end

-- 2 ≠ 0 in F_q for q > 2.
-- Useful for zmod.order_of_dvd_card_sub_one.
lemma zmod_two_ne_zero {q : ℕ} : 2 < q → (2 : zmod q) ≠ 0 :=
begin
  intro h2,
  have h_mod := @zmod.eq_iff_modeq_nat q 2 0,
  simp at h_mod,  -- Need to simplify before rewrite (apply the casts).
  simp,
  rw h_mod,
  rw nat.modeq_zero_iff_dvd,
  intro h,
  have h := nat.le_of_dvd (dec_trivial) h,
  apply has_lt.lt.not_le h2 h,
end

-- 2 ^ q = 1 if q ∣ mersenne p.
-- Useful for order_of_eq_prime.
lemma zmod_two_pow_eq_one_of_mersenne {p q : ℕ} :
  q ∣ mersenne p → (2 : zmod q)^p = 1 :=
begin
  rw mersenne,
  intro h_dvd,
  rw ← nat.modeq_zero_iff_dvd at h_dvd,
  rw ← zmod.eq_iff_modeq_nat at h_dvd,
  simp at h_dvd,
  rw sub_eq_zero at h_dvd,
  exact h_dvd,
end

lemma mersenne_odd {n : ℕ} : 0 < n → ¬ 2 ∣ mersenne n :=
begin
  rw mersenne,
  cases n,
    simp,
  simp,
  rw pow_succ,
  have h : ∀ (k : ℕ), 1 ≤ k → (2 * k - 1) % 2 = 1 := _,
    apply h,
    apply nat.one_le_two_pow,
  intro k,
  cases k, simp,
  intro h, clear h,
  rw nat.mul_succ,
  simp,
  rw mul_comm,
  rw nat.mul_add_mod,
  simp,
end

lemma lt_of_dvd_sub_one {p q : ℕ} : 2 < q → p ∣ q - 1 → p < q :=
begin
  cases q, simp,  -- Consider (q.succ) - 1 = q.
  simp,
  intro hq,
  intro h_dvd,
  apply nat.lt_succ_of_le,
  apply nat.le_of_dvd _ h_dvd,
  have hq := nat.le_of_lt_succ hq,
  apply lt_of_le_of_lt' hq,
  dec_trivial,
end

-- For p prime, any prime factor q of (mersenne p) satisfies p < q.
theorem lt_of_dvd_mersenne {p q : ℕ} [hp : fact p.prime] [hq : fact q.prime] :
  q ∣ mersenne p → p < q :=
begin
  intro h_mersenne,
  have hq' : 2 < q := _,  -- 2 < q since q prime, q ∣ mersenne p, (mersenne p) is odd.
    -- Use (fact q.prime).
    have h_dvd : order_of (2 : zmod q) ∣ q - 1 := zmod.order_of_dvd_card_sub_one _,
      -- Use (fact p.prime).
      have h_eq : order_of (2 : zmod q) = p := order_of_eq_prime _ _,
          -- Show p < q since p ∣ (q - 1).
          rw h_eq at h_dvd,
          apply lt_of_dvd_sub_one hq' h_dvd,
        apply zmod_two_pow_eq_one_of_mersenne h_mersenne,
      apply zmod_two_ne_one (le_of_lt hq'),
    apply zmod_two_ne_zero hq',
  have h2 := nat.prime.two_le hq.out,
  rw le_iff_eq_or_lt at h2,
  cases h2,
    exfalso,
    revert h_mersenne,
    rw ← h2,
    apply mersenne_odd,
    apply lt_trans nat.zero_lt_one (nat.prime.one_lt hp.out),
  exact h2,
end


lemma two_lt_two_pow {n : ℕ} : 1 < n → 2 < 2^n :=
begin
  cases n, simp,
  cases n, simp,
  simp,
  rw pow_succ,
  simp,
  apply nat.one_lt_two_pow,
  simp,
end

lemma one_lt_mersenne {n : ℕ} : 1 < n → 1 < mersenne n :=
begin
  cases n, simp,
  cases n, simp,
  intro h, clear h,
  rw mersenne,
  apply nat.lt_of_succ_lt_succ,
  rw ← nat.add_one,
  rw ← nat.add_one,
  rw nat.sub_add_cancel _,
    apply two_lt_two_pow, simp,
  apply le_of_lt,
  apply nat.one_lt_two_pow,
  simp,
end

theorem infinite_primes (p : ℕ) :
  nat.prime p → ∃ (q : ℕ), nat.prime q ∧ p < q :=
begin
  intro hp,
  apply exists.intro (mersenne p).min_fac,
  have hq := @nat.min_fac_prime (mersenne p) _,
    apply and.intro hq,
    apply @lt_of_dvd_mersenne p (mersenne p).min_fac (fact.mk hp) (fact.mk hq),
    apply nat.min_fac_dvd,
  have h := one_lt_mersenne (nat.prime.one_lt hp),
  intro h', rw h' at h, simp at h, exact h,
end


-- Just for fun, try out the mapping from ℕ to primes.
def gen_prime : ℕ → ℕ
| 0 := 2
| (n+1) := (mersenne (gen_prime n)).min_fac

#eval gen_prime 3  -- 127
-- gen_prime 4 requires (2^127 - 1).min_fac

lemma one_lt_make_prime (n : ℕ) : 1 < gen_prime n :=
begin
  induction n with k hk,
    rw gen_prime, simp,
  rw gen_prime,
  apply nat.prime.one_lt,
  apply nat.min_fac_prime,
  have h := one_lt_mersenne hk,
  intro h',
  rw h' at h, simp at h, contradiction,
end

lemma make_prime_is_prime (n : ℕ) : (gen_prime n).prime :=
begin
  cases n, rw gen_prime, apply nat.prime_two,
  rw gen_prime,
  apply nat.min_fac_prime,
  have h := one_lt_mersenne (one_lt_make_prime n),
  intro h',
  rw h' at h, simp at h, contradiction,
end

lemma make_prime_lt_make_prime_succ (k : ℕ) : gen_prime k < gen_prime k.succ :=
begin
  have hp := make_prime_is_prime k,
  have hq := make_prime_is_prime k.succ,
  apply @lt_of_dvd_mersenne (gen_prime k) (gen_prime k.succ) (fact.mk hp) (fact.mk hq),
  rw gen_prime,
  apply nat.min_fac_dvd,
end

lemma make_prime_strict_mono {k n : ℕ} : k < n → gen_prime k < gen_prime n :=
  by apply strict_mono_nat_of_lt_succ make_prime_lt_make_prime_succ

-- Prove that gen_prime n generates a new prime number for any n.
theorem infinite_primes' (n : ℕ) :
  nat.prime (gen_prime n) ∧ ∀ (k : ℕ), k < n → gen_prime k < gen_prime n :=
begin
  apply and.intro (make_prime_is_prime _),
  intro k,
  exact make_prime_strict_mono,
end
