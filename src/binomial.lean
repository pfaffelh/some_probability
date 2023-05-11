import tactic
import data.nat.choose.basic
import data.nat.choose.sum
import data.int.basic
import data.real.basic
import probability.probability_mass_function.constructions

noncomputable theory
open_locale classical big_operators nnreal ennreal 

-- We are going to define B(n,p), the binomial distribution with n trials and success probability p.

-- These are two basic lemmas on ℝ≥0∞ we will need below. 

lemma eq_iff {a b : ℝ} (posb : 0 < b): ((a = b) ↔ (ennreal.of_real a = ennreal.of_real b)) :=
begin
  split, 
  intro h, 
  rw h, 
  intro h, 
  have hb : b = (ennreal.of_real b).to_real, 
  {
    have h : 0 ≤ b, apply le_of_lt posb, 
    exact left_eq_sup.mpr h,  
  },
  rw hb, rw ← h,
  have ha : 0 < ennreal.of_real a, 
  {
    rw h, simp only [ennreal.of_real_pos, gt_iff_lt], exact posb, 
  },
  have posa : 0 < a, 
  { 
    apply ennreal.of_real_pos.1 ha, },
  have h : 0 ≤ a, 
  { 
    apply le_of_lt posa, },
  exact left_eq_sup.mpr h,  
end

variables {α : Type*}

lemma ennreal_sum_eq_one_iff [fintype α] (f : α → ℝ) (pos : ∀ a, f a ≥ 0) : (∑ a, f a = 1) ↔ (∑ a, (ennreal.of_real (f a)) = (1 : ℝ≥0∞)) :=
begin
  rw ← ennreal.of_real_sum_of_nonneg, 
  rw eq_iff zero_lt_one, rw ennreal.of_real_one, 
  intros a ha, exact pos a, 
end

-- We extend the API for defining a pmf from some f : α → ℝ (not → ℝ≥0∞); see probability_mass_function in mathlib for some more lemmas of the same type:

def local_of_fintype [fintype α] (f : α → ℝ) (pos : ∀ a : α, 0 ≤ f a ) (h : ∑ a, f a = 1) : pmf α :=
pmf.of_finset (λ a, ennreal.of_real (f a)) finset.univ ((ennreal_sum_eq_one_iff f pos).1 h) (λ a ha, absurd (finset.mem_univ a) ha)

-- Here we start to define B(n,p)

variables (n : ℕ) (p : ℝ)  

-- We start by defining mf_binom, which is a mass function with codomain ℝ, but lacking a proof of summing to 1.

def mf_binom (n : ℕ) (p : ℝ) : finset.range (n+1) → ℝ := λ a, ((n.choose a) : ℝ) * (p ^ (a : ℕ) )  * (1 - p) ^ (n - a)

-- Some trivial lemma needed below.
lemma mf_binom_apply (n : ℕ) (p : ℝ) (a : finset.range (n+1)) : (mf_binom n p) a = ((n.choose a) : ℝ) * (p ^ (a : ℕ) )  * (1 - p) ^ (n - a) :=
begin
  refl, 
end

-- Since a pmf has codomain ℝ≥0∞, we need the following:
lemma mf_binom_pos (n : ℕ) (p : ℝ) (hp1 : p ≥ 0) (hp2 : p ≤ 1) : ∀ (a : finset.range (n+1)), (mf_binom n p) a ≥ 0 := 
begin
  intro a, 
  rw mf_binom_apply, 
  apply mul_nonneg,
  apply mul_nonneg,
  exact (nat.choose n a).cast_nonneg,
  apply pow_nonneg hp1, 
  have hp2' : 0 ≤ 1-p, linarith, 
  apply pow_nonneg hp2',
end

-- Since a pmf must sum to one, we need the following:
lemma mf_binom_sum_one (n : ℕ) (p : ℝ) : (∑ a : finset.range (n + 1), (mf_binom n p) a) = 1 := 
begin
  have h : (p + (1-p))^n = 1, 
  {
    rw add_comm, 
    rw sub_add, simp only [tsub_zero, one_pow, eq_self_iff_true, sub_self], 
  },
  nth_rewrite 0 ← h, 
  rw add_pow, 
  rw eq_comm,
  let f : ℕ → ℝ := λ (a : ℕ), (n.choose a) * p ^ a * (1 - p) ^ (n - a),
  let g : ℕ → ℝ := λ (a : ℕ), p ^ a * (1 - p) ^ (n - a) * (n.choose a),
  change ∑ (m : ℕ) in finset.range (n + 1), g m = ∑ (a : ↥(finset.range (n + 1))), f ↑a,
  have h : f = g, 
  {
    ext, 
    change ((n.choose x) : ℝ) * (p ^ x) * (1 - p) ^ (n - x) = p ^ x * (1 - p) ^ (n - x) * (n.choose x),
    rw mul_comm ((n.choose x) : ℝ) (p ^ x), 
    rw mul_assoc, rw mul_comm ((n.choose x) : ℝ) ((1 - p) ^ (n - x)), rw ← mul_assoc,  
  },
  rw h, 
  apply finset.sum_subtype,
  intro x, refl,
end

-- Now, define the pmf for the binomial distribution
def pmf_binom (n : ℕ) (p : ℝ) (hp1 : 0 ≤ p) (hp2 : p ≤ 1) : pmf (finset.range (n+1)) := local_of_fintype  (mf_binom n p) (mf_binom_pos n p hp1 hp2) (mf_binom_sum_one n p) 

-- Here is the outer measure based on pmf_binom:
def outer_measure_binom (n : ℕ) (p : ℝ) (hp1 : 0 ≤ p) (hp2 : p ≤ 1) := pmf.to_outer_measure (pmf_binom n p hp1 hp2)
