-- Uses Lagrange's theorem (order_of_dvd_card_sub_one).

import data.nat.basic
import data.nat.prime
import data.zmod.basic
import number_theory.lucas_lehmer  -- mersenne
import field_theory.finite.basic  -- order_of_dvd_card_sub_one


lemma order_eq_of_two_ne_one {p q : ℕ} [hp : fact (nat.prime p)] :
  (2 : zmod q) ≠ 1 → (2 : zmod q)^p = 1 → order_of (2 : zmod q) = p :=
begin
  intro h_ne,
  intro h,
  apply order_of_eq_prime h h_ne,
end

lemma mod_two_ne_one_of_prime {q : ℕ} : nat.prime q → (2 : zmod q) ≠ 1 :=
begin
  intro hq,
  have h_prime := nat.prime.two_le hq,
  have h_mod := @zmod.eq_iff_modeq_nat q 2 1,
  simp at h_mod,  -- Need to simplify before rewrite (apply the casts).
  simp,
  rw h_mod,
  cases has_le.le.eq_or_lt h_prime with hq' hq',
    rw ← hq',
    dec_trivial,
  intro h,
  have h := nat.modeq.eq_of_lt_of_lt h hq' _,
    simp at h, exact h,
  apply lt_trans _ hq',
  dec_trivial,
end

lemma mod_two_ne_zero_of_two_lt {q : ℕ} : 2 < q → (2 : zmod q) ≠ 0 :=
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

lemma two_pow_eq_one_of_dvd_mersenne {p q : ℕ} :
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

lemma two_pow_even {n : ℕ} : 0 < n → 2 ∣ 2 ^ n :=
begin
  cases n, simp,
  simp [pow_succ],
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

-- For p prime, any prime factor q of (mersenne p) satisfies p < q.
theorem lt_of_dvd_mersenne {p q : ℕ} [hp : fact (nat.prime p)] [hq : fact (nat.prime q)] :
  q ∣ mersenne p → p < q :=
begin
  intro h_mersenne,
  have hq' : 2 < q := _,
    have h_dvd := zmod.order_of_dvd_card_sub_one (mod_two_ne_zero_of_two_lt hq'),
    have h_eq : order_of (2 : zmod q) = p := order_eq_of_two_ne_one (mod_two_ne_one_of_prime hq.out) _,
      rw h_eq at h_dvd,
      have h_dvd := nat.le_of_dvd _ h_dvd,
        have h_dvd := nat.lt_succ_of_le h_dvd,
        rw ← nat.add_one at h_dvd,
        rw nat.sub_add_cancel _ at h_dvd,
          exact h_dvd,
        apply lt_trans _ hq', dec_trivial,
      rw nat.sub_one,
      have hq' := nat.pred_lt_pred _ hq', simp at hq',
        apply lt_trans _ hq',
        simp,
      simp,
    apply two_pow_eq_one_of_dvd_mersenne h_mersenne,
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

-- Prove that make_prime n generates a new prime number for any n.
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
