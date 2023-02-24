-- Euler's proof of the infinitude of primes.
-- Uses the product of all primes up to n.

import data.nat.basic
import data.nat.prime

def prod_primes : ℕ → ℕ
| 0 := 1
| (nat.succ n) := (if nat.prime n.succ then n.succ else 1) * prod_primes n

lemma dvd_prod {n p : ℕ} : p ≤ n → nat.prime p → p ∣ prod_primes n :=
begin
  induction n with k hk,
    simp,
    intro hp,
    rw hp,
    simp [nat.not_prime_zero],
  intro hn,
  generalize hm : prod_primes k.succ = m,
  rw prod_primes at hm, rw ite_mul at hm, rw ite_eq_iff at hm, simp at hm,
  cases nat.of_le_succ hn,
    cases hm,
      intro hp,
      rw ←hm.right,
      apply dvd_trans (hk h hp) (dvd_mul_left _ _),
    rw ←hm.right,
    apply hk h,
  rw ←h at hm,
  cases hm,
    intro hp,
    rw ←hm.right,
    apply dvd_mul_right,
  intro hp,
  exfalso, apply hm.left, assumption,
end

lemma not_dvd_succ_prod {n p : ℕ} : nat.prime p → p ≤ n → ¬ p ∣ (prod_primes n).succ :=
begin
  intro h_prime,
  intro hn,
  rw ←nat.not_dvd_iff_between_consec_multiples,
    have h := dvd_prod hn h_prime,
    rw dvd_iff_exists_eq_mul_left at h,
    cases h with c hc,
    apply exists.intro c,
    simp [mul_add],
    rw mul_comm at hc,
    rw hc,
    simp [nat.lt_succ_self, ←nat.add_one],
    apply lt_of_le_of_lt' (nat.prime.two_le h_prime), simp,
  apply lt_of_le_of_lt' (nat.prime.two_le h_prime), simp,
end

lemma zero_lt_prod {n : ℕ} : 0 < prod_primes n :=
begin
  induction n with k hk,
    rw prod_primes, simp,
  generalize hm : prod_primes k.succ = m,
  rw prod_primes at hm,
  rw ite_mul at hm,
  rw ite_eq_iff at hm,
  simp at hm,
  cases hm,
    rw ←hm.right,
    rw zero_lt_iff,
    simp,
    intro h,
    rw h at hk,
    simp at hk, contradiction,
  rw ←hm.right,
  assumption,
end

theorem infinite_primes (n : ℕ) : ∃ (p : ℕ), nat.prime p ∧ n < p :=
begin
  -- Let x be product of primes up to n.
  generalize hx : prod_primes n = x,
  have h_prime := @nat.min_fac_prime x.succ _,
    apply exists.intro x.succ.min_fac,
    cases decidable.em (x.succ.min_fac ≤ n),
      exfalso,
      apply not_dvd_succ_prod h_prime h,
      rw hx,
      apply nat.min_fac_dvd,
    apply and.intro, exact h_prime,
    rw not_le at h, exact h,
  simp,
  rw nat.succ_eq_add_one, simp,
  rw ←hx,
  rw ←le_zero_iff,
  apply has_lt.lt.not_le,
  apply zero_lt_prod,
end