-- Try giving a definition of primes.
-- Includes establishing decidability.
-- Prove infinitude of primes using factorial.

import data.nat.basic
import algebra  -- Makes simp more powerful.

def myprime (n : ℕ) := 1 < n ∧ ∀ (k : ℕ), 1 < k → k < n → ¬(k ∣ n)

@[simp]
lemma not_prime_zero : ¬ myprime 0 :=
begin
  rw myprime, simp,
end

@[simp]
lemma not_prime_one : ¬ myprime 1 :=
begin
  rw myprime, simp,
end

lemma prime_to_one_lt {n : ℕ} : myprime n → 1 < n :=
begin
  rw myprime,
  cases n, simp,
  cases n, simp,
  simp,
end

-- Couldn't find this in mathlib and it makes things simpler.
lemma nat_succ_le_iff (m n : ℕ) : m < n ↔ m.succ ≤ n :=
begin
  apply iff.intro,
    intro h,
    apply has_lt.lt.nat_succ_le,
    assumption,
  intro h,
  apply has_lt.lt.nat_succ_le,
  assumption,  -- Weird? Equal by definition?
end

@[simp]
lemma prime_two : myprime 2 :=
begin
  rw myprime,
  simp,
  intro k,
  rw nat_succ_le_iff,
  intro h1,
  -- rw nat.lt_iff_add_one_le at h1,  -- Easier way to do this?
  intro h2,
  exfalso,
  apply has_le.le.not_lt h1,
  exact h2,
end

lemma prime_three : myprime 3 :=
begin
  rw myprime, simp,
  intro k,
  rw nat_succ_le_iff,
  rw nat.lt_succ_iff,
  intro hk,
  rw has_le.le.ge_iff_eq hk,
  intro h,
  rw ← h,
  simp,
end

-- If a non-trivial divisor exists, n is not prime.
-- This is just De Morgan's law (direction that doesn't require excluded middle).
lemma exists_dvd_to_not_prime {n : ℕ}
: (∃ (k : ℕ), 1 < k ∧ k < n ∧ k ∣ n) → ¬myprime n :=
begin
  intro h,
  rw myprime,
  intro h_prime,
  cases h with w h,
  clarify,
end


-- Now try to prove decidability!
-- (find_max_factor_below n k) returns largest divisor m such that m < k.
-- (find_max_factor_below n n) gives the largest factor of n.
def find_max_factor_below : ℕ → ℕ → ℕ
| _ 0 := 0
| n (k+1) := (if k ∣ n then k else (find_max_factor_below n k))

-- (find_max_factor n) = 1 is equivalent to being prime.
def find_max_factor (n : ℕ) := find_max_factor_below n n

-- Use ite_eq_iff to prove things with ite (if-then-else).
-- Use generalize to transform propositions about ite statements.

lemma max_factor_below_eq_zero_iff {n k : ℕ} :
  find_max_factor_below n k = 0 ↔ k < 2 :=
begin
  apply iff.intro,
    cases k, simp,
    cases k, simp,
    rw nat.succ_lt_succ_iff, simp,
    induction k with j hj,
      rw find_max_factor_below, simp,
    rw find_max_factor_below,
    rw ite_eq_iff,
    simp,
    intro h',
    assumption,
  cases k,
    simp, rw find_max_factor_below,
  cases k,
    simp, rw find_max_factor_below, rw find_max_factor_below, simp,
  rw nat.succ_lt_succ_iff, simp,
end

lemma max_factor_below_dvd {n k : ℕ} :
  1 < k → find_max_factor_below n k ∣ n :=
begin
  generalize hm : find_max_factor_below n k = m,
  cases k, simp,  -- k = 0
  cases k, simp,  -- k = 1
  simp,
  induction k with j hj,
    rw ← hm, rw find_max_factor_below, simp,
  rw find_max_factor_below at hm,
  rw ite_eq_iff at hm,
  cases hm,
    rw ← hm.right,
    exact hm.left,
  apply hj,
  exact hm.right,
end

lemma max_factor_below_lt {n k : ℕ} :
  0 < k → find_max_factor_below n k < k :=
begin
  generalize hm : find_max_factor_below n k = m,
  cases k, simp,
  simp,
  revert hm,
  induction k,
    rw find_max_factor_below,
    rw ite_eq_iff,
    rw find_max_factor_below, simp,
    rw ← or_and_distrib_right, simp,
    rw @eq_comm _ m,
    simp,
  rw find_max_factor_below,
  rw ite_eq_iff,
  intro hm,
  cases hm,
    rw ← hm.right,
    apply nat.lt_succ_self,
  apply lt_trans _ (nat.lt_succ_self _),
  apply k_ih,
  exact hm.right,
end

lemma one_lt_iff {n : ℕ} : 1 < n ↔ ¬(n = 0 ∨ n = 1) :=
begin
  apply iff.intro,
    cases n, simp,
    cases n, simp,
    simp,
  cases n, simp,
  cases n, simp,
  simp,
end

lemma one_lt_max_factor_below_to_exists {n k : ℕ} :
  1 < find_max_factor_below n k → ∃ (d : ℕ), 1 < d ∧ d < k ∧ d ∣ n :=
begin
  cases k,
    rw find_max_factor_below, simp,
  cases k,
    rw find_max_factor_below, simp,
    rw find_max_factor_below, simp,
  intro h,
  apply exists.intro (find_max_factor_below n k.succ.succ),
  apply and.intro, assumption,
  apply and.intro,
    apply max_factor_below_lt, simp,
  apply max_factor_below_dvd, simp,
end

lemma one_lt_max_factor_to_not_prime {n : ℕ} :
  1 < find_max_factor n → ¬myprime n :=
begin
  rw find_max_factor,
  assume h,
  apply exists_dvd_to_not_prime,
  apply one_lt_max_factor_below_to_exists,
  assumption,
end

lemma max_factor_below_eq_one_to_not_dvd {n k : ℕ} :
  find_max_factor_below n k = 1 → ∀ (m : ℕ), 1 < m → m < k → ¬(m ∣ n) :=
begin
  cases k,  -- k = 0
    rw find_max_factor_below, simp,
  cases k,  -- k = 1
    rw find_max_factor_below, simp,
    rw find_max_factor_below, simp,
  induction k with j hj,
    rw find_max_factor_below, simp,
    intro m, intro hm, intro hm',
    exfalso,
    -- 1 < m ↔ 1.succ ≤ m
    rw ← nat.succ_le_iff at hm,
    -- 1 ≤ m ↔ ¬(m < 1)
    rw nat.lt_iff_le_not_le at hm',
    apply hm'.right,
    assumption,
  rw find_max_factor_below,
  rw ite_eq_iff,
  simp,
  intro h, intro h',
  intro m, intro hm,
  rw nat.lt_succ_iff_lt_or_eq,
  intro hm',
  cases hm',
    apply hj h' m hm hm',
  rw hm', assumption,
end

theorem max_factor_eq_one_to_prime {n : ℕ} : find_max_factor n = 1 → myprime n :=
begin
  rw find_max_factor,
  cases n,  -- n = 0
    rw find_max_factor_below, simp,
  cases n,  -- n = 1
    rw find_max_factor_below,
    rw find_max_factor_below,
    simp,
  intro h,
  rw myprime,
  apply and.intro, simp,
  apply max_factor_below_eq_one_to_not_dvd,
  assumption,
end

lemma prime_to_max_factor_below_eq_one {n : ℕ} :
  myprime n → ∀ k : ℕ, 1 < k → k ≤ n → find_max_factor_below n k = 1 :=
begin
  rw myprime,
  intro h,
  intro k,
  cases k, simp,
  cases k, simp,
  intro hk1,
  intro hkn,
  induction k,
    rw find_max_factor_below, simp,
  rw find_max_factor_below,
  rw ite_eq_iff,
  simp,
  apply and.intro,
    apply h.right,
      dec_trivial,
    apply has_le.le.trans_lt' hkn,
    apply nat.lt_succ_self,
  apply k_ih,
    dec_trivial,
  apply has_lt.lt.trans (nat.lt_succ_self _),
  assumption,
end

theorem prime_to_max_factor_eq_one {n : ℕ} : myprime n → find_max_factor n = 1 :=
begin
  rw find_max_factor,
  intro h,
  apply prime_to_max_factor_below_eq_one,
      assumption,
    exact h.left,
  simp,
end

theorem prime_iff_max_factor_eq_one {n : ℕ} : myprime n ↔ find_max_factor n = 1 :=
begin
  apply iff.intro,
    apply prime_to_max_factor_eq_one,
  apply max_factor_eq_one_to_prime,
end

instance myprime_decidable {n : ℕ} : decidable (myprime n) :=
  decidable_of_iff' _ prime_iff_max_factor_eq_one


-- Now show that any number is prime or has a prime factor.
-- Uses decidability of myprime.

lemma zero_lt_max_factor_iff {n : ℕ} : 1 < n ↔ 0 < find_max_factor n :=
begin
  rw zero_lt_iff, rw find_max_factor, simp,
  rw max_factor_below_eq_zero_iff, simp,
  trivial,
end

theorem not_prime_iff_one_lt_max_factor {n : ℕ} :
  1 < n → (¬myprime n ↔ 1 < find_max_factor n) :=
begin
  cases n, simp,
  cases n, simp,
  intro hn,
  apply iff.intro,
    rw prime_iff_max_factor_eq_one,
    intro h,
    rw one_lt_iff,
    intro h_or,
    cases h_or,
      rw zero_lt_max_factor_iff at hn,
      rw h_or at hn,
      simp at hn, trivial,
    trivial,
  intro h,
  rw myprime,
  apply exists_dvd_to_not_prime,
  -- generalize hx : find_max_factor n.succ.succ = x,
  apply exists.intro (find_max_factor n.succ.succ),
  apply and.intro, assumption,
  apply and.intro,
    rw find_max_factor,
    apply @max_factor_below_lt _ n.succ.succ _, simp,
  rw find_max_factor,
  apply @max_factor_below_dvd _ n.succ.succ _, simp,
end

-- Need to use generalize, clear and revert.
theorem prime_or_has_prime_factor (n : ℕ) :
  1 < n → (myprime n ∨ ∃ (p : ℕ), myprime p ∧ p ∣ n) :=
begin
  -- Introduce m = n.
  generalize hm_eq : n = m,
  rw eq_comm at hm_eq,
  intro hm,
  cases n, revert hm, rw hm_eq, simp,
  cases n, revert hm, rw hm_eq, simp,
  -- Replace m = n with m ≤ n.
  have hm_le := le_of_eq hm_eq,
  clear hm_eq,
  -- Include all m ≤ n in induction.
  revert m,
  induction n with k hk,
    intro m, intro hm, intro hn,
    cases nat.eq_or_lt_of_le hn,
      rw h, simp,
    exfalso,
    apply not_lt_of_ge _ h, simp,
    apply has_lt.lt.nat_succ_le, assumption,
  intro m, intro hm, intro hn,
  cases decidable.em (myprime m),
    apply or.inl, assumption,
  -- m is not prime; look at its (non-trivial) factor
  apply or.inr,
  rw not_prime_iff_one_lt_max_factor hm at h,
  have hkx := hk (find_max_factor m) h _,
    cases hkx,
      -- (find max_factor m) is prime
      apply exists.intro (find_max_factor m),
      apply and.intro, assumption,
      rw find_max_factor,
      apply max_factor_below_dvd hm,
    -- (find max_factor m) is not prime; has a prime factor
    cases hkx with w hw,
    apply exists.intro w,
    apply and.intro hw.left,
    apply dvd_trans hw.right,
    rw find_max_factor,
    apply max_factor_below_dvd hm,
  rw ← nat.succ_le_succ_iff,
  apply le_trans _ hn,
  rw nat.succ_le_iff,
  rw find_max_factor,
  apply @max_factor_below_lt m,
  apply lt_trans _ hm, simp,
end


def factorial : ℕ → ℕ
| 0 := 1
| (n+1) := (n+1) * (factorial n)

example (n : ℕ) : 0 < n → n ∣ factorial n :=
begin
  cases n, simp,
  simp,
  rw factorial,
  simp,
end

-- Want to prove ∀ (n k : ℕ) : k > 0 → k ≤ n → k ∣ factorial n
-- What's the induction that we will use?
-- factorial n = n * (factorial (n-1))
--             = n * (n-1) * (factorial (n-2))
-- k ∣ factorial k
-- k ∣ (factorial k) * (k + 1) = factorial (k+1)
lemma dvd_factorial {n k : ℕ} : 0 < k → k ≤ n → k ∣ factorial n :=
begin
  cases k, simp,
  simp,
  intro hn,
  have hn := nat.le.dest hn,
  cases hn with d hd,
  rw ← hd,
  clear hn hd n,
  induction d with j hj,
    simp, rw factorial, simp,
  rw nat.add_succ,
  rw factorial,
  apply has_dvd.dvd.mul_left,
  assumption,
end

-- Use dvd_factorial to prove not divisor of factorial + 1.
lemma not_dvd_succ_factorial {n k : ℕ} :
  1 < k → k ≤ n → ¬(k ∣ (factorial n) + 1) :=
begin
  intro hk1,
  intro hkn,
  have hk0 : 0 < k := lt_trans nat.zero_lt_one hk1,  -- Used multiple times.
  have h := dvd_factorial hk0 hkn,
  cases h with a ha,
  rw ← (nat.not_dvd_iff_between_consec_multiples (factorial n + 1) hk0),
  rw ha,
  apply exists.intro a,
  apply and.intro,
    simp,
  simp [mul_add],
  exact hk1,
end

lemma zero_lt_factorial {n : ℕ} : 0 < factorial n :=
begin
  induction n with k hk,
    rw factorial, simp,
  rw factorial, simp, assumption,
end

lemma self_le_factorial {n : ℕ} : n ≤ factorial n :=
begin
  induction n with k hk,
    rw factorial, simp,
  rw factorial, simp,
  apply has_lt.lt.nat_succ_le,
  apply zero_lt_factorial,
end


theorem infinite_primes (n : ℕ) : ∃ (p : ℕ), n < p ∧ myprime p :=
begin
  -- Consider factors of factorial + 1.
  have h_or := prime_or_has_prime_factor (factorial n).succ _,
    cases h_or,
      apply exists.intro (factorial n).succ,
      apply and.intro,
        rw nat.lt_succ_iff,
        exact self_le_factorial,
      assumption,
    cases h_or with m hm,
    apply exists.intro m,
    apply and.intro,
      cases decidable.em (m ≤ n) with h_le h_not_le,
        exfalso,
        apply not_dvd_succ_factorial _ h_le hm.right,
        apply prime_to_one_lt,
        exact hm.left,
      simp at h_not_le,
      assumption,
    exact hm.left,
  rw nat.succ_lt_succ_iff,
  apply zero_lt_factorial,
end
