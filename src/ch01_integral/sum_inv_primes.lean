import algebra.big_operators.basic
import data.finset.basic
import data.int.basic
import data.list.basic
import data.list.lemmas  -- For list.can_lift.
import data.list.min_max
import data.nat.basic
import data.nat.prime
import data.nat.factors
import data.nat.factorization.basic
import data.real.basic
import data.set.basic
import data.set.intervals.basic

open real
open_locale big_operators

def num_primes_lt (n : ℕ) := (finset.range n).sum (λ k, if nat.prime k then 1 else 0)
def primes_lt (n : ℕ) := (finset.range n).filter nat.prime
def card_primes_lt (n : ℕ) := (primes_lt n).card

-- Could define all_factors_le using k.factors.maximum ≤ n.
-- However, it's difficult to work with (list.maximum ≤ n).
-- Instead define with for-all statement; use list.maximum to prove decidable.
def all_factors_le (n k : ℕ) : Prop := ∀ (p : ℕ), p ∈ k.factors → p ≤ n

-- Prove decidable.

lemma exists_factors_mem_iff {n : ℕ} : 2 ≤ n ↔ ∃ (p : ℕ), p ∈ n.factors :=
begin
  rw ← list.length_pos_iff_exists_mem,
  rw list.length_pos_iff_ne_nil,
  simp,
  cases n, simp,
  cases n, simp,
  simp [nat.succ_le_succ_iff],
end

lemma exists_maximum_eq_coe_iff {l : list ℕ} : (∃ x : ℕ, l.maximum = ↑x) ↔ l ≠ list.nil :=
begin
  apply iff.intro,
  { intro h,
    cases h with x hx,
    rw list.maximum_eq_coe_iff at hx,
    exact list.ne_nil_of_mem hx.left, },
  { intro h,
    have h := list.foldr_max_of_ne_nil h,
    rw ← h, 
    simp, },
end

-- Feels like this could be in mathlib?
lemma maximum_le_iff_forall_le {l : list ℕ} {m : ℕ} :
  l.maximum ≤ ↑m ↔ ∀ (x : ℕ), x ∈ l → x ≤ m :=
begin
  cases decidable.em (l = list.nil),
  { rw h, simp, },
  { rw (by simp : ¬l = list.nil ↔ l ≠ list.nil) at h,
    -- Get the actual maximum.
    rw ← exists_maximum_eq_coe_iff at h,
    cases h with c hc,
    rw hc,
    simp,
    rw list.maximum_eq_coe_iff at hc,
    apply iff.intro,
    { intros h x hx,
      apply le_trans _ h,
      exact hc.right x hx, },
    { intro h,
      exact h c hc.left, }, },
end

-- Try to prove maximum_le_iff_forall_le by expressing maximum with foldr.

-- These two types are equal?
def convert (x : option ℕ) : with_bot ℕ := x

-- This feels like a more natural way to write maximum?
lemma maximum_eq_foldr {l : list ℕ} : l.maximum = list.foldr (max ∘ coe) ⊥ l :=
begin
  rw ← list.foldr_map,
  rw list.maximum,
  rw list.argmax,
  rw ← list.foldl_eq_foldr max_commutative max_associative,
  rw list.foldl_map,
  -- Need list.foldl_hom because lhs uses (option ℕ) and rhs uses (with_bot ℕ).
  have h : (∀ (x : option ℕ), x = convert x) := by { intro x, rw convert },
  rw h (list.foldl _ none _),
  -- rw (h none : ⊥ = convert none),  -- Doesn't work like this?
  have h_none : ⊥ = convert none := h none,
  rw h_none,
  rw list.foldl_hom,
  intro x,
  intro y,
  rw [convert, convert],
  simp,
  rw list.arg_aux,
  cases x,
  { simp, refl, },
  { simp,
    rw [option.some_eq_coe, option.some_eq_coe],
    rw ite_eq_iff,
    rw [eq_comm, max_eq_right_iff],
    rw [eq_comm, max_eq_left_iff],
    simp,
    cases lt_or_le x y with hxy hyx,
    { apply or.inl, exact and.intro hxy (le_of_lt hxy), },
    { apply or.inr, exact hyx }, },
end

-- Prove using foldr instead.
lemma maximum_le_iff_forall_le' {l : list ℕ} {m : ℕ} :
  l.maximum ≤ ↑m ↔ ∀ (x : ℕ), x ∈ l → x ≤ m :=
begin
  rw maximum_eq_foldr,
  apply iff.intro,
  { induction l with a l' hl', simp,
    simp,
    intros ha h,
    exact and.intro ha (hl' h), },
  { intro h,
    rw ← list.foldr_map,
    -- Use `max_le_of_forall_le` instead of induction.
    -- (Induction might be cleaner?)
    apply list.max_le_of_forall_le _ _ _,
    intro x,
    cases x, simp,
    rw option.some_eq_coe,
    have h_inj : function.injective (coe : ℕ → option ℕ) := by {
      rw function.injective,
      simp [← option.some_eq_coe],
    },
    rw list.mem_map_of_injective h_inj,
    simp,
    apply h, },
end

instance all_factors_le_decidable {n k : ℕ} : decidable (all_factors_le n k) :=
begin
  rw all_factors_le,
  rw ← maximum_le_iff_forall_le,
  apply with_bot.decidable_le,
end


-- Prefer Ico for these definitions to use sum_Ico_consecutive.

noncomputable def series_inv_with_factors_le (n k : ℕ) : ℝ :=
  ∑ i in (finset.Ico 1 (k+1)), if all_factors_le n i then (↑n)⁻¹ else 0

noncomputable def harmonic (n : ℕ) : ℝ := ∑ i in (finset.Ico 1 (n+1)), (↑n)⁻¹

-- TODO: Prove in limit?
lemma harmonic_le_series_inv_with_factors_le {n k : ℕ} (hnk : n ≤ k) :
  harmonic n ≤ series_inv_with_factors_le n k :=
begin
  rw [harmonic, series_inv_with_factors_le],
  have hnk' : n + 1 ≤ k + 1 := by { simp, exact hnk, },
  rw ← finset.sum_Ico_consecutive _ (by simp : 1 ≤ n + 1) hnk',
  rw finset.sum_ite_of_true _ _ _,
  { simp,
    apply finset.sum_nonneg,
    intros i hi,
    apply le_trans _ (inf_le_ite _ _ _),
    simp, },
  intros x hx,
  simp at hx,
  rw all_factors_le,
  intros p hp,
  rw nat.lt_succ_iff at hx,
  apply le_trans _ hx.right,
  exact nat.le_of_mem_factors hp,
end
