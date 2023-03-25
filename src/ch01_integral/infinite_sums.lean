import .factors_le
import data.real.basic
import data.real.nnreal
import data.real.ennreal
import data.pnat.factors
import data.pnat.prime
import data.finset.basic
import data.multiset.basic
import data.multiset.fintype
-- import data.multiset.bind  -- Causes timeout?
import order.filter.basic
import order.filter.at_top_bot
-- import group_theory.submonoid.membership  -- Causes timeout?
import analysis.specific_limits.basic
import topology.basic
import topology.algebra.infinite_sum
import topology.instances.ennreal
import logic.equiv.defs

open real filter
open_locale big_operators


-- Establish equivalence of (pnat_factors_le n) and finset.pi (for prod_sum).

def pnat_factors_le (n : ℕ) : submonoid ℕ+ := {
  carrier := {x | all_factors_le n x},
  mul_mem' := by {
    simp [all_factors_le],
    intros a b ha hb p,
    specialize ha p,
    specialize hb p,
    rw nat.mem_factors_mul (ne_zero_of_lt a.prop) (ne_zero_of_lt b.prop),
    intro hp,
    exact or.elim hp ha hb, },
  one_mem' := by { simp [all_factors_le], },
}

variables {n : ℕ}

namespace pnat_factors_le
-- variables {n : ℕ}

instance ordered_comm_monoid_pnat_factors_le : ordered_comm_monoid (pnat_factors_le n) :=
  submonoid.to_ordered_comm_monoid _

@[simp]
def mk {a : ℕ+} (h : all_factors_le n a) : pnat_factors_le n := subtype.mk a h

instance has_one_pnat_factors_le : has_one (pnat_factors_le n) :=
{ one := mk (show all_factors_le n (1 : ℕ+), by simp [all_factors_le]), }

lemma coe_pnat_eq (a : ℕ+) {h : all_factors_le n a} : a = ↑(mk h) :=
by { simp [mk], }

-- Necessary to define this? Seems to be needed below.
instance has_mem_prime_multiset : has_mem nat.primes prime_multiset := { mem := multiset.mem, }

-- Switch to/from `nat.factors` representation (more results available?).
lemma mem_factor_multiset_iff {x : ℕ+} {p : nat.primes} :
  p ∈ pnat.factor_multiset x ↔ ↑p ∈ nat.factors ↑x :=
begin
  simp [pnat.factor_multiset, prime_multiset.of_nat_list, prime_multiset.of_nat_multiset],
  apply iff.intro,
  { intro h, cases h with q hq, cases hq with hq hq', simp [← hq'], exact hq, },
  { cases p with p hp, simp, },
end

-- Need to add has_mem to prime_multiset for this?
lemma mem_primes_le_of_mem_factor_multiset {x : pnat_factors_le n} {p : nat.primes} :
  p ∈ pnat.factor_multiset ↑x → p ∈ primes_le n :=
begin
  simp [mem_factor_multiset_iff],
  cases x with x hx,
  cases x with x hx',
  simp,
  intro hp,
  simp [pnat_factors_le, ← submonoid.mem_carrier, all_factors_le] at hx,
  specialize hx p hp,
  simp [primes_le, nat.lt_succ_iff],
  exact hx,
end

def factor_multiset (x : pnat_factors_le n) : multiset ↥(primes_le n) :=
  (pnat.factor_multiset ↑x).attach.map
  (λ p, ⟨p.val, (mem_primes_le_of_mem_factor_multiset p.property)⟩)

lemma le_of_mem_primes_le (p : nat.primes) : p ∈ primes_le n → ↑p ≤ n :=
by { simp [primes_le, nat.lt_succ_iff], }

lemma mem_pnat_factors_le_of_mem_primes_le {p : nat.primes} : p ∈ primes_le n → ↑p ∈ pnat_factors_le n :=
begin
  simp [primes_le, nat.lt_succ_iff],
  simp [pnat_factors_le, all_factors_le],
  cases p with p hp,
  simp [← coe_coe],
  simp [nat.factors_prime hp],
end


namespace primes_le

-- Enable cast from (primes_le n) to (pnat_factors_le n).
instance has_coe_pnat_factors_le : has_coe ↥(primes_le n) (pnat_factors_le n) :=
{ coe := λ p, ⟨↑(p.val), mem_pnat_factors_le_of_mem_primes_le p.property⟩, }

-- Should be unnecessary!
-- instance has_coe_primes : has_coe ↥(primes_le n) nat.primes :=
-- { coe := λ p, p.val, }

instance has_coe_multiset_pnat_factors_le : has_coe (multiset ↥(primes_le n)) (multiset (pnat_factors_le n)) :=
{ coe := λ s, s.map coe, }

instance has_coe_prime_multiset : has_coe (multiset ↥(primes_le n)) prime_multiset :=
{ coe := λ s, s.map coe, }

lemma injective_coe_prime_multiset : function.injective (coe : multiset ↥(primes_le n) → prime_multiset) :=
begin
  intros a b,
  unfold_coes,
  rw multiset.map_eq_map, { cc, },
  simp,
  exact subtype.coe_injective,
end

end primes_le


def multiset_prod : multiset ↥(primes_le n) → pnat_factors_le n := λ s, multiset.prod ↑s

-- lemma prod_factors_eq_self' (x : ↥(pnat_factors_le n)) : ↑(multiset_prod (factor_multiset x)) = (↑x : ℕ+) :=
-- begin
--   simp [multiset_prod, factor_multiset],
--   unfold_coes,
--   simp,
--   rw (_ : (λ u, ⟨↑↑u, _⟩ : {a // a ∈ pnat.factor_multiset ↑x} → ℕ+) = (coe : nat.primes → ℕ+) ∘ coe),
--   rotate, { ext, norm_cast, },
--   simp,
--   have h := pnat.prod_factor_multiset ↑x,
--   rw prime_multiset.prod at h,
--   unfold_coes at h,
--   simp [prime_multiset.to_pnat_multiset] at h,
--   exact h,
-- end

lemma prod_factors_eq_self (x : ↥(pnat_factors_le n)) : multiset_prod (factor_multiset x) = x :=
begin
  -- Easier to work with ℕ+?
  rw ← subtype.coe_inj,
  simp [multiset_prod, factor_multiset],
  unfold_coes,
  simp,
  rw (_ : (λ u, ⟨↑↑u, _⟩ : {a // a ∈ pnat.factor_multiset ↑x} → ℕ+) = (coe : nat.primes → ℕ+) ∘ coe),
  rotate, { ext, norm_cast, },
  simp,
  have h := pnat.prod_factor_multiset ↑x,
  rw prime_multiset.prod at h,
  unfold_coes at h,
  simp [prime_multiset.to_pnat_multiset] at h,
  exact h,
end

lemma factor_prod_primes_eq_self (s : multiset ↥(primes_le n)) : factor_multiset (multiset_prod s) = s :=
begin
  -- Easier to work with prime_multiset?
  rw ← primes_le.injective_coe_prime_multiset.eq_iff,
  simp [multiset_prod, factor_multiset],
  unfold_coes,
  simp,
  rw multiset.attach_map_coe,
  rw (_ : ↑((↑s : multiset ↥(pnat_factors_le n)).prod) = (s : prime_multiset).prod),
  { rw prime_multiset.factor_multiset_prod, unfold_coes, },
  { push_cast,
    unfold_coes,
    simp,
    rw (_ : (λ (x : ↥(primes_le n)), (⟨(↑(↑x : nat.primes) : ℕ), _⟩ : ℕ+)) = (coe : ↥(primes_le n) → ℕ+)),
    rotate, { unfold_coes, },
    rw prime_multiset.prod,
    rw (_ : ↑(multiset.map coe s) = (multiset.map coe s)),
    unfold_coes,
    simp [prime_multiset.to_pnat_multiset],
    apply multiset.map_congr rfl,
    intros p hp,
    unfold_coes, },
end

def equiv_multiset : pnat_factors_le n ≃ multiset (primes_le n) :=
{ to_fun    := factor_multiset,
  inv_fun   := multiset_prod,
  left_inv  := prod_factors_eq_self,
  right_inv := factor_prod_primes_eq_self, }

end pnat_factors_le


def multiset_prime_pows (ks : (Π (p : nat.primes), p ∈ primes_le n → ℕ)) : multiset ↥(primes_le n) :=
  multiset.bind finset.univ.val
  (λ p, multiset.replicate (ks p.val p.prop) p : ↥(primes_le n) → multiset ↥(primes_le n))

-- Another trivial coe...
instance multiset_primes_le_has_coe : has_coe (multiset (primes_le n)) prime_multiset :=
{ coe := λ s, s.map coe }

-- lemma count_multiset_prime_pows {p : primes_le n} {ks : (Π (p : nat.primes), p ∈ primes_le n → ℕ)} :
--   multiset.count p (multiset_prime_pows ks) = ks p.val p.prop :=
-- begin
--   rw multiset_prime_pows, simp,
--   rw multiset.count_bind,
--   simp_rw multiset.count_replicate,
--   -- rw ← finset.sum,
--   -- Not sure how to get around the attach...
--   have h : ∀ {f : ↥(primes_le n) → ℕ}, (finset.univ : finset ↥(primes_le n)).sum f = (multiset.map f (primes_le n).val.attach).sum := by {
--     intros f,
--     rw finset.sum,
--     simp,
--   },
--   rw ← h,
--   rw finset.sum_ite_eq,
--   simp,
-- end


/- Show equivalence between (with_pnat_factors_le n) and finset.pi so that we can equate to geometric sum. -/

def multiset_to_pi' {α : Type*} [decidable_eq α] {s : finset α}
  (f : multiset ↥s) : Π (x : α), x ∈ s → ℕ := λ x hx, f.count ⟨x, hx⟩

def pi_to_multiset' {α : Type*} {s : finset α}
  (f : Π (x : α), x ∈ s → ℕ) : multiset ↥s :=
  (finset.univ : finset ↥s).val.bind (λ x, multiset.replicate (f x.val x.property) x)

lemma pi_to_multiset_to_pi' {α : Type*} [decidable_eq α] {s : finset α} (f : multiset ↥s) :
  pi_to_multiset' (multiset_to_pi' f) = f :=
begin
  simp [multiset_to_pi', pi_to_multiset'],
  ext x,
  rw multiset.count_bind,
  simp_rw multiset.count_replicate,
  rw ← finset.attach_val,
  rw ← finset.sum,  -- finset.sum f s = multiset.sum (multiset.map f s.val)
  rw finset.sum_ite_eq,
  simp [ite_eq_left_iff],
end

lemma multiset_to_pi_to_multiset' {α : Type*} [decidable_eq α] {s : finset α} (f : Π (x : α), x ∈ s → ℕ) :
  multiset_to_pi' (pi_to_multiset' f) = f :=
begin
  simp [multiset_to_pi', pi_to_multiset'],
  ext x hx,
  simp [multiset.count_bind, multiset.count_replicate],
  rw ← finset.attach_val,
  rw ← finset.sum,  -- finset.sum f s = multiset.sum (multiset.map f s.val)
  rw finset.sum_ite_eq,
  rw ite_eq_left_iff.mpr, { simp, },
  intro h, exfalso, apply h,
  exact finset.mem_attach _ _,
end

def equiv_multiset_pi' {α : Type*} [decidable_eq α] {s : finset α} :
  multiset ↥s ≃ (Π (x : α), x ∈ s → ℕ) :=
{ to_fun    := multiset_to_pi',
  inv_fun   := pi_to_multiset',
  left_inv  := pi_to_multiset_to_pi',
  right_inv := multiset_to_pi_to_multiset', }

def equiv_pnat_factors_le_pi : pnat_factors_le n ≃ (Π (p : nat.primes), p ∈ primes_le n → ℕ) :=
  equiv.trans pnat_factors_le.equiv_multiset equiv_multiset_pi'


/-------------------------------------------------------------------------------
  This is where we're going!
-------------------------------------------------------------------------------/

noncomputable def prod_geom_series (n : ℕ) : nnreal := ∏ p : nat.primes in primes_le n, (1 - (↑p)⁻¹)⁻¹

noncomputable def prod_sum_inv_primes_le (n : ℕ) : ℕ → nnreal :=
  λ m, ∏ p : nat.primes in primes_le n, ∑ k : ℕ in finset.range m, (p : nnreal)⁻¹ ^ k

def finset_pi_range (n : ℕ) : ℕ → finset (Π (p : nat.primes), p ∈ primes_le n → ℕ) :=
  λ m, (primes_le n).pi (λ (p : nat.primes), finset.range m)

lemma mono_finset_pi_range : monotone (finset_pi_range n) :=
begin
  rw monotone,
  intros a b h,
  simp [finset_pi_range],
  apply finset.pi_subset,
  intros p hp,
  -- mono,  -- no good match found
  exact finset.range_mono h,
end

-- Make use of the fact that (⊥ : ℕ) = 0.
def pi_sup (f : Π (p : nat.primes), p ∈ primes_le n → ℕ) : ℕ :=
  finset.sup (primes_le n).attach (λ p, f p.val p.property : ↥(primes_le n) → ℕ)

lemma primes_le_nonempty (h : 2 ≤ n) : (primes_le n).nonempty :=
begin
  rw finset.nonempty,
  existsi (⟨2, nat.prime_two⟩ : nat.primes),
  simp [primes_le],
  linarith,
end

lemma subset_of_finset_pi_range_of_le_max {fs : finset (Π (p : nat.primes), p ∈ primes_le n → ℕ)} {m : ℕ} :
  finset.sup fs pi_sup < m → fs ⊆ finset_pi_range n m :=
begin
  intros hm,
  simp [finset_pi_range],
  intros f hf,
  simp,
  intros p hp,
  apply lt_of_le_of_lt _ hm,
  apply le_trans _ (finset.le_sup hf),
  simp [pi_sup],
  -- TODO: Some cleaner way to do this?
  have h : f p hp = (λ (q : ↥(primes_le n)), f (↑q : nat.primes) q.prop) ⟨p, hp⟩ := by simp,
  rw h, clear h,
  apply finset.le_sup,
  simp,
end

-- Can this be proven more simply? By relation to multiset or finsupp?
lemma tendsto_pi_range_at_top_at_top : tendsto (finset_pi_range n) at_top at_top :=
begin
  rw monotone.tendsto_at_top_at_top_iff mono_finset_pi_range,
  intro fs,
  existsi (finset.sup fs pi_sup).succ,
  apply subset_of_finset_pi_range_of_le_max,
  exact nat.lt_succ_self _,
end

lemma tendsto_prod_sum_inv_prod_geom_series {n : ℕ} :
  tendsto (prod_sum_inv_primes_le n) at_top (nhds (prod_geom_series n)) :=
begin
  rw [prod_sum_inv_primes_le, prod_geom_series],
  apply tendsto_finset_prod,
  intros p hp,
  -- rw ← has_sum_iff_tendsto_nat_of_nonneg,
  apply has_sum.tendsto_sum_nat,
  refine nnreal.has_sum_geometric _,
  { rw inv_lt_one_iff,
    apply or.inr,
    norm_cast,
    exact nat.prime.one_lt p.prop, },
end

noncomputable def inv_nat : ℕ → nnreal := has_inv.inv ∘ coe
noncomputable def inv_on_pnat_factors_le (n : ℕ) : ↥(pnat_factors_le n) → nnreal := inv_nat ∘ coe

instance has_coe_submonoid_pnat_set_nat : has_coe (submonoid ℕ+) (set ℕ) :=
{ coe := λ sm, coe '' sm.carrier, }  -- Any better way to do this? coe is injective...


lemma prod_finset_eq_prod_multiset {ks : Π (p : nat.primes), p ∈ primes_le n → ℕ} :
  (↑∏ (i : {x // x ∈ primes_le n}) in (primes_le n).attach, (↑((↑(↑i : nat.primes) : ℕ+) ^ ks ↑i i.prop) : ℕ) : nnreal)⁻¹ =
  inv_nat (↑((multiset.map (coe : ↥(pnat_factors_le n) → ℕ+) (↑(pi_to_multiset' ks) : multiset ↥(pnat_factors_le n))).prod) : ℕ) :=
begin
  rw inv_nat,
  simp,
  rw pi_to_multiset',
  simp,
  push_cast,
  -- Need to manipulate coes to get bind prod together.
  -- Then we can use `multiset.prod_bind` and `multiset.prod_replicate`.
  rw ← submonoid.coe_multiset_prod,
  rw (_ : ∀ {s : multiset ↥(primes_le n)}, (↑s : multiset ↥(pnat_factors_le n)) = multiset.map coe s),
  rotate, { unfold_coes, simp, },
  rw multiset.map_bind,
  rw multiset.prod_bind,
  simp_rw multiset.map_replicate,
  -- TODO: Should be included in @[simp].
  -- simp [submonoid.coe_multiset_prod],
  rw submonoid.coe_multiset_prod, -- prod on ↥(pnat_factors_le n) to prod on ℕ+
  simp,
  rw ← pnat.coe_coe_monoid_hom,  -- replace coe : ℕ+ → ℕ with ⇑pnat.coe_monoid_hom
  rw monoid_hom.map_multiset_prod, -- prod on ℕ+ to prod on ℕ
  rw multiset.map_map,
  rw nat.cast_multiset_prod, -- prod on ℕ to prod on nnreal
  rw finset.prod_eq_multiset_prod,
  rw multiset.map_map,
  rw finset.attach_val,  -- Doesn't work?
  rw multiset.map_congr rfl,
  intros p hp,
  simp,
  norm_cast,
end


theorem sum_inv_pnat_factors_le_eq_prod_geom_series : has_sum (inv_on_pnat_factors_le n) (prod_geom_series n) :=
begin
  -- rw has_sum_inv_pnat_factors_le_iff_pi,
  rw ← equiv.has_sum_iff equiv_pnat_factors_le_pi.symm,
  simp [equiv_pnat_factors_le_pi, equiv_multiset_pi', pnat_factors_le.equiv_multiset, equiv.trans],

  -- Switch to ennreal to work with ∑' and ⨆.
  rw ← ennreal.has_sum_coe, simp,
  rw summable.has_sum_iff ennreal.summable,  -- Shorter version exists?
  rw ennreal.tsum_eq_supr_sum,

  have h₂ := @tendsto_prod_sum_inv_prod_geom_series n,
  rw prod_sum_inv_primes_le at h₂,
  simp_rw finset.prod_sum at h₂,

  -- Sum of nnreal will be equal to supremum over subsets.
  -- And limit over a sequence of subsets that approaches at_top will be supremum?
  -- Need to show supremum is obtained by the one limit we have?

  have h :
    (λ (m : ℕ), ∑ (p : Π (a : nat.primes), a ∈ primes_le n → ℕ) in (primes_le n).pi (λ (a : nat.primes), finset.range m),
      ∏ (x : {x // x ∈ primes_le n}) in (primes_le n).attach, (↑(x.val) : nnreal)⁻¹ ^ p x.val x.property) =
    (λ (s : finset (Π (p : nat.primes), p ∈ primes_le n → ℕ)), ∑ (p : Π (a : nat.primes), a ∈ primes_le n → ℕ) in s,
      ∏ (x : {x // x ∈ primes_le n}) in (primes_le n).attach, (↑(x.val) : nnreal)⁻¹ ^ p x.val x.property)
    ∘ finset_pi_range n := by
  { simp [finset_pi_range], },
  rw h at h₂,
  clear h,
  rw ← tendsto_iff_tendsto_subseq_of_monotone
    (_ : monotone
      (λ (s : finset (Π (p : nat.primes), p ∈ primes_le n → ℕ)), ∑ (p : Π (a : nat.primes), a ∈ primes_le n → ℕ) in s,
        ∏ (x : {x // x ∈ primes_le n}) in (primes_le n).attach, (↑(x.val) : nnreal)⁻¹ ^ p x.val x.property))
    tendsto_pi_range_at_top_at_top
    at h₂,
  rotate,
  { rw monotone,
    intros a b h,
    apply finset.sum_le_sum_of_subset,
    exact h, },

  -- Switch to ennreal (need complete_linear_order).
  rw ← ennreal.tendsto_coe at h₂, simp at h₂,
  replace h₂ := supr_eq_of_tendsto _ h₂, rotate,
  { rw monotone,
    intros a b h,
    norm_cast,
    apply finset.sum_le_sum_of_subset,
    exact h, },

  norm_cast at h₂,
  norm_cast,

  simp [inv_on_pnat_factors_le, pnat_factors_le.multiset_prod],
  norm_cast,
  simp_rw prod_finset_eq_prod_multiset at h₂,
  exact h₂,
end
