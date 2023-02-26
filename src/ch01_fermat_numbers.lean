-- Proves infinitude of prime numbers using Fermat numbers.
-- There are infinite Fermat numbers and they have no common factors.

import data.nat.basic
import data.nat.pow
import data.nat.prime


def fermat_num (n : ℕ) := 2^(2^n) + 1

def fermat_prod : ℕ → ℕ
| 0 := 1
| (n+1) := fermat_num n * fermat_prod n


lemma two_lt_fermat_num (n : ℕ) : 2 < fermat_num n :=
begin
  rw fermat_num,
  apply lt_of_le_of_lt' _ (nat.lt_succ_self 2),
  rw nat.succ_le_succ_iff,
  apply le_self_pow,
    simp,
  apply pow_ne_zero,
  simp,
end

lemma odd_iff {n : ℕ} : ¬ 2 ∣ n ↔ n % 2 = 1 :=
begin
  rw nat.dvd_iff_mod_eq_zero,
  apply iff.intro,
    intro h',
    cases (nat.mod_two_eq_zero_or_one n),
      contradiction,
    assumption,
  cases (nat.mod_two_eq_zero_or_one n),
    rw h,
    contradiction,
  rw h,
  simp,
end

lemma fermat_num_odd (n : ℕ) : ¬ 2 ∣ fermat_num n :=
begin
  rw odd_iff,
  have h := nat.mod_two_eq_zero_or_one,
  rw fermat_num,
  cases n, simp,
  simp [nat.add_mod, nat.pow_mod],
end

-- The main result on which the proof depends.
theorem prod_add_two_eq_num {n : ℕ} :
  fermat_prod n + 2 = fermat_num n :=
begin
  rw fermat_num,
  induction n with k hk,
    rw fermat_prod, simp,
  rw fermat_prod,
  rw fermat_num,
  simp [add_mul],
  rw add_assoc,
  rw hk,
  rw ← add_assoc,
  rw nat.succ.inj_eq,
  rw pow_succ,
  rw mul_comm 2 _,  -- Ensure we get (2^2^k)^2 rather than (2^2)^(2^k).
  rw pow_mul,
  rw ← nat.mul_succ,
  rw pow_two,
  simp,
  apply nat.succ.inj,
  exact hk,
end


lemma fermat_num_dvd_prod {k n : ℕ} : k < n → fermat_num k ∣ fermat_prod n :=
begin
  cases n,
    simp,
  intro hkn,
  cases nat.le.dest (nat.le_of_lt_succ hkn) with d hd,
  rw ← hd, clear hkn hd,
  induction d with i hi,
    simp,
    rw fermat_prod, simp,
  rw nat.add_succ,
  rw fermat_prod,
  apply dvd_trans hi,
  simp,
end

lemma fermat_dvd_fermat_sub_two {k n : ℕ} :
  k < n → fermat_num k ∣ fermat_num n - 2 :=
begin
  cases n,
    simp,
  intro hkn,
  rw ← @prod_add_two_eq_num n.succ, simp,
  apply fermat_num_dvd_prod hkn,
end

-- Lazy proof of a simple result.
lemma dvd_two_iff {m : ℕ} : m ∣ 2 ↔ m = 1 ∨ m = 2 :=
begin
  apply iff.intro,
    cases m, simp,
    cases m, simp,
    cases m, simp,
    intro h,
    exfalso,
    have h_le := nat.le_of_dvd (dec_trivial) h,
    revert h_le,
    dec_trivial,
  intro h,
  cases h,
    rw h, dec_trivial,
  rw h,
end

-- Cannot apply dvd_add_right to ℕ (needs non_unital_ring).
-- From (m ∣ x) and (m ∣ x-2), we have that (m ∣ 2), hence m = 1 or 2.
lemma nat_dvd_add_right {a b c : ℕ} : (a ∣ b) → (a ∣ b + c) → a ∣ c :=
begin
  rw nat.dvd_iff_mod_eq_zero,
  rw nat.dvd_iff_mod_eq_zero,
  rw nat.dvd_iff_mod_eq_zero,
  rw ← nat.mod_add_mod,
  intro ha, rw ha, simp,
end

-- Didn't need this in the end. May be useful in the future.
theorem nat_sub_sub {x y z : ℕ} : x ≤ y → y ≤ z → z - (y - x) = x + (z - y) :=
begin
  intro hxy,
  intro hyz,
  have hxz := le_trans hxy hyz,
  have hy_z : y ≤ z + x := nat.add_le_add hyz (nat.zero_le _),
  have hy_z : y - x ≤ z := _,
    rw nat.sub_eq_iff_eq_add hy_z,
    rw add_assoc, rw add_comm (z-y) (y-x), rw ← add_assoc,
    rw ← nat.add_sub_assoc hxy, simp,
    rw ← nat.add_sub_assoc hyz, simp,
  have hx_z : x ≤ z + x := nat.add_le_add hxz (nat.zero_le _),
  rw ← nat.add_sub_cancel z x,
  rw nat.sub_le_sub_iff_right hx_z, assumption,
end

-- Like nat_dvd_add_right but for (valid) sub.
lemma nat_dvd_sub_right {a b c : ℕ} : c ≤ b → (a ∣ b) → (a ∣ b - c) → a ∣ c :=
begin
  intro h_le,
  rw le_iff_exists_add at h_le,
  cases h_le with d hd,
  rw hd, simp,
  rw add_comm,
  intro ha,
  intro hb,
  apply nat_dvd_add_right hb ha,
end

-- All fermat numbers are co-prime.
theorem fermat_coprime {k n : ℕ} :
  k < n → ∀ (m : ℕ), (m ∣ fermat_num k) → (m ∣ fermat_num n) → m = 1 :=
begin
  intro hkn,
  intro m,
  intro hfk,
  intro hfn,
  have h_dvd_sub_two := dvd_trans hfk (fermat_dvd_fermat_sub_two hkn),
  -- Combine the two dvd results to obtain constraint on m.
  have h := nat_dvd_sub_right _ hfn h_dvd_sub_two,
    rw dvd_two_iff at h,
    cases h, assumption,
    -- m cannot be 2 since all Fermat numbers are odd.
    exfalso,
    apply fermat_num_odd k,
    rw h at hfk, exact hfk,
  apply le_of_lt,
  apply two_lt_fermat_num,
end


-- Function that maps any number to a novel prime number.
def make_prime (n : ℕ) := (fermat_num n).min_fac

lemma make_prime_is_prime (n : ℕ) : nat.prime (make_prime n) :=
begin
  rw make_prime,
  apply nat.min_fac_prime,
  rw fermat_num,
  simp,
end

lemma not_make_prime_eq_one (n : ℕ) : ¬ make_prime n = 1 :=
begin
  intro h',
  apply nat.not_prime_one,
  have h := make_prime_is_prime n,
  rw h' at h,
  exact h,
end

-- Prove that make_prime n generates a new prime number for any n.
theorem infinite_primes (n : ℕ) :
  nat.prime (make_prime n) ∧ ∀ (k : ℕ), k < n → make_prime k ≠ make_prime n :=
begin
  cases n, simp,
    apply nat.min_fac_prime,
    rw fermat_num, simp,
  apply and.intro,
    apply nat.min_fac_prime,
    rw fermat_num, simp,
  intro k,
  intro hk,
  have h_prime := make_prime_is_prime k,
  simp, intro h_eq,
  have h := fermat_coprime hk (make_prime k),  -- but we know that make_prime k ≠ 1
  apply not_make_prime_eq_one k,
  apply h,
    rw make_prime,
    apply nat.min_fac_dvd,
  rw h_eq,
  rw make_prime,
  apply nat.min_fac_dvd,
end
