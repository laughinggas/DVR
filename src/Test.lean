import ring_theory.ideals

import ring_theory.principal_ideal_domain

import ring_theory.localization

import tactic

import order.bounded_lattice

import algebra.field_power

universe u

/-lemma val (a b c : ℤ ) (h : a*b = c) (f : ℤ -> ℤ) : f(a*b) = f(c) :=
begin
  rw h,
end -/

class discrete_valuation_ring (R : Type u) [integral_domain R] [is_principal_ideal_ring R] :=

(prime_ideal' : ideal R)

(primality : prime_ideal'.is_prime)

(is_nonzero : prime_ideal' ≠ ⊥)

(unique_nonzero_prime_ideal : ∀ P : ideal R, P.is_prime → P = ⊥ ∨ P = prime_ideal')

namespace discrete_valuation_ring

def prime_ideal (R : Type u) [integral_domain R] [is_principal_ideal_ring R] [discrete_valuation_ring R] : ideal R :=
discrete_valuation_ring.prime_ideal'

instance is_prime (R : Type*) [integral_domain R] [is_principal_ideal_ring R] [discrete_valuation_ring R] : (prime_ideal R).is_prime :=
primality

variables {R : Type u} [integral_domain R] [is_principal_ideal_ring R] [discrete_valuation_ring R]
open discrete_valuation_ring

lemma prime_ideal_is_maximal : (prime_ideal R).is_maximal :=
begin
  have f : prime_ideal R ≠ ⊥,
  { apply discrete_valuation_ring.is_nonzero },
  apply is_prime.to_maximal_ideal,
    exact f,
end

lemma unique_max_ideal : ∃! I : ideal R, I.is_maximal :=

begin

  use prime_ideal R,

  split,

  { exact prime_ideal_is_maximal },

  { intros y a,

    cases discrete_valuation_ring.unique_nonzero_prime_ideal y a.is_prime,

    { exfalso,

      rw h at a,

      apply discrete_valuation_ring.primality.left,

      exact a.right (prime_ideal R) (bot_lt_iff_ne_bot.2 discrete_valuation_ring.is_nonzero) },

    { assumption } }

end

instance is_local_ring : local_ring R := local_of_unique_max_ideal unique_max_ideal

open local_ring

noncomputable theory
open_locale classical
class discrete_valuation_field (K : Type*) [field K] :=
(v : K -> with_top ℤ ) 
(mul : ∀ (x y : K), v(x*y) = v(x) + v(y) )
(add : ∀ (x y : K), min (v(x)) (v(y)) ≤ v(x + y)  )
(non_zero : ∀ (x : K), v(x) = ⊤ ↔ x = 0 )

namespace discrete_valuation_field

definition valuation (K : Type*) [field K] [ discrete_valuation_field K ] : K -> with_top ℤ := v

variables {K : Type*} [field K] [discrete_valuation_field K]

lemma with_top.cases (a : with_top ℤ) : a = ⊤ ∨ ∃ n : ℤ, a = n :=
begin
  cases a with n,
  { -- a = ⊤ case
    left,
    refl, -- true by definition
  },
  { -- ℤ case
    right,
    use n,
    refl, -- true by definition
  }
end

lemma sum_zero_iff_zero (a : with_top ℤ) : a + a = 0 ↔ a = 0 :=
begin
  split,
  { -- the hard way
    intro h, -- h is a proof of a+a=0
    -- split into cases
    cases (with_top.cases a) with htop hn,
    { -- a = ⊤
      rw htop at h,
      -- h is false
      cases h,
      -- no cases!
    },
    { -- a = n
      cases hn with n hn,
      rw hn at h ⊢,
      -- now h says n+n=0 and our goal is n=0
      -- but these are equalities in `with_top ℤ
      -- so we need to get them into ℤ
      -- A tactic called `norm_cast` does this
     norm_cast at h ⊢,
      -- we finally have a hypothesis n + n = 0
      -- and a goal n = 0
      -- and everything is an integer
      rw add_self_eq_zero at h,
      assumption
    }
  },
   { -- the easy way
    intro ha,
    rw ha,
    simp
  }
end
 --Thanks Kevin!

lemma val_one_eq_zero : v(1 : K) = 0 :=
begin
  have h : (1 : K) * 1 = 1,
    simp,
  apply_fun v at h,
  rw mul at h,
  -- now we know v(1)+v(1)=v(1) and we want to deduce v(1)=0 (i.e. rule out v(1)=⊤)
  rcases (with_top.cases (v(1:K))) with h1 | ⟨n, h2⟩, -- do all the cases in one go
  { rw non_zero at h1,
    cases (one_ne_zero h1)
  },
  { rw h2 at *,
    norm_cast at *,
    -- library_search found the next line
    exact add_left_eq_self.mp (congr_arg (has_add.add n) (congr_arg (has_add.add n) h)),
  },
end

lemma val_minus_one_is_zero : v((-1) : K) = 0 :=
begin
have f : (-1:K)*(-1:K) = (1 : K),
simp,
have g : v((-1 : K)*(-1 : K)) = v(1 : K),
simp,
have k : v((-1 : K)*(-1 : K)) = v(-1 : K) + v(-1 : K),
{
  apply mul,
},
rw k at g,
rw val_one_eq_zero at g,
rw <-sum_zero_iff_zero,
exact g,
end

@[simp] lemma val_zero : v(0:K) = ⊤ :=
begin
rw non_zero,
end


lemma with_top.transitivity (a b c : with_top ℤ) : a ≤ b -> b ≤ c -> a ≤ c :=
begin
rintros,
cases(with_top.cases c) with h1 h2,
  {
    rw h1,
    simp,
  },
  {
    cases h2 with n h2,
    cases(with_top.cases a) with k1 k2,
    {
      rw [k1, h2],
      rw k1 at a_1,
      rw h2 at a_2,
      cases(with_top.cases b) with l1 l2,
      {
        rw l1 at a_2,
        exact a_2,
      },
      {
        cases l2 with m l2,
        rw l2 at a_1,
        exfalso,
        apply with_top.not_top_le_coe m,
        exact a_1,
      },
    },
    {
      cases k2 with m k2,
      cases(with_top.cases b) with l1 l2,
      {
        rw [l1,h2] at a_2,
        exfalso,
        apply with_top.not_top_le_coe n,
        exact a_2,
      },
      {
        cases l2 with k l2,
        rw [k2,l2] at a_1,
        rw [l2,h2] at a_2,
        rw [k2,h2],
        rw with_top.coe_le_coe,
        rw with_top.coe_le_coe at a_1,
        rw with_top.coe_le_coe at a_2,
        transitivity k,
        exact a_1,
        exact a_2,
      },
    },  
  },
end 

def val_ring (K : Type*) [field K] [discrete_valuation_field K] := { x : K | 0 ≤ v x } 

instance (K : Type*) [field K] [discrete_valuation_field K] : is_add_subgroup (val_ring K) :=
{
  zero_mem := begin
              unfold val_ring,
              simp,
              end,
  add_mem := begin
            unfold val_ring,
            simp only [set.mem_set_of_eq],
            rintros,
            have g : min (v(a)) (v(b)) ≤ v(a + b),
            {
              apply add,
            },
            rw min_le_iff at g,
            cases g,
            {
              exact with_top.transitivity _ _ _ a_1 g,
            },
            {
              exact with_top.transitivity _ _ _ a_2 g,
            },
            end,
  neg_mem := begin
            unfold val_ring,
            rintros,
            simp only [set.mem_set_of_eq],
            simp only [set.mem_set_of_eq] at a_1,
            have f : -a = a * (-1 : K) := by simp,
            rw [f, mul, val_minus_one_is_zero],
            simp [a_1], 
            end,
}

instance (K:Type*) [field K] [discrete_valuation_field K] : is_submonoid (val_ring K) :=
{ one_mem := begin
            unfold val_ring,
            simp,
            rw val_one_eq_zero,
            norm_num,
            end,
  mul_mem := begin
            unfold val_ring,
            rintros,
            simp,
            simp at a_1,
            simp at a_2,
            rw mul,
            apply add_nonneg' a_1 a_2,
            end, }

instance valuation_ring (K:Type*) [field K] [discrete_valuation_field K] : is_subring (val_ring K) :=
{}

instance is_domain (K:Type*) [field K] [discrete_valuation_field K] : integral_domain (val_ring K) :=
subring.domain (val_ring K)

def unif (K:Type*) [field K] [discrete_valuation_field K] : set K := { π | v π = 1 }

variables (π : K) (hπ : π ∈ unif K)

lemma val_unif_eq_one (hπ : π ∈ unif K) : v(π) = 1 :=
begin
unfold unif at hπ,
simp at hπ,
exact hπ,
end

lemma unif_ne_zero (hπ : π ∈ unif K) : π ≠ 0 :=
begin
simp,
      unfold unif at hπ,
      simp at hπ,
      intro g,
      rw <-non_zero at g,
      rw hπ at g,
      cases g,
end 

lemma with_top.add_happens (a b c : with_top ℤ) (ne_top : a ≠ ⊤) : b=c ↔ a+b = a+c :=
begin
cases with_top.cases a,
{
  exfalso,
  apply ne_top,
  exact h,
},
cases h with n h,
rw h,
split,
{
  rintros,
  rw a_1,
},
cases with_top.cases b,
{
  rw h_1,
  rw with_top.add_top,
  rintros,
  have b_1 : ↑n + c = ⊤,
  exact eq.symm a_1,
  rw with_top.add_eq_top at b_1,
  cases b_1,
  {
    exfalso,
    apply with_top.coe_ne_top,
    {
      exact b_1,
    },
  },
  exact eq.symm b_1,
},
{
  cases h_1 with m h_1,
  rw h_1,
  cases with_top.cases c,
  {
    rw h_2,
    rintros,
    rw with_top.add_top at a_1,
    rw with_top.add_eq_top at a_1,
    cases a_1,
    {
      exfalso,
      apply with_top.coe_ne_top,
      exact a_1,
    },
    {
      exact a_1,
    },
  },
  cases h_2 with l h_2,
  rw h_2,
  rintros,
  norm_cast,
  norm_cast at a_1,
  simp at a_1,
  assumption,
}
end

lemma with_top.distrib (a b c : with_top ℤ) (na : a ≠ ⊤) (nb : b ≠ ⊤) (nc : c ≠ ⊤) : (a + b)*c = a*c + b*c :=
begin
  rcases(with_top.cases a) with rfl | ⟨a, rfl⟩;
  rcases(with_top.cases b) with rfl | ⟨b, rfl⟩;
  rcases(with_top.cases c) with rfl | ⟨n, rfl⟩;
  try {simp},
  repeat
  {
  simp at na,
  exfalso,
  exact na,
  },
  {
  simp at nb,
  exfalso,
  exact nb,
  },
  {
  simp at nc,
  exfalso,
  exact nc,
  },
  rw <-with_top.coe_add,
  repeat {rw <-with_top.coe_mul},
  rw <-with_top.coe_add,
  rw with_top.coe_eq_coe,
  rw right_distrib,
end

lemma one_mul (a : with_top ℤ) : 1 * a = a :=
begin
cases (with_top.cases) a with a ha,
{
  rw a,
  simp,
},
{
  cases ha with n ha,
  rw ha,
  norm_cast,
  simp,
}
end

lemma nat_ne_top (n :ℕ) : (n : with_top ℤ) ≠ ⊤ := 
begin
simp,
end

lemma val_inv (x : K) (nz : x ≠ 0) : v(x) + v(x)⁻¹ = 0 :=
begin
rw <- mul,
rw mul_inv_cancel,
{
  rw val_one_eq_zero,
},
exact nz,
end

lemma with_top.sub_add_eq_zero (n : ℕ) : ((-n : ℤ) : with_top ℤ) + (n : with_top ℤ) = 0 :=
begin
rw <-with_top.coe_nat,
rw <-with_top.coe_add,
simp only [add_left_neg, int.nat_cast_eq_coe_nat, with_top.coe_zero],
end

lemma with_top.add_sub_eq_zero (n : ℕ) : (n : with_top ℤ) + ((-n : ℤ) : with_top ℤ) = 0 :=
begin
rw <-with_top.coe_nat,
rw <-with_top.coe_add,
simp only [add_right_neg, int.nat_cast_eq_coe_nat, with_top.coe_zero],
end

lemma contra_non_zero (x : K) (n : ℕ) (nz : n ≠ 0) : v(x^n) ≠ ⊤ ↔ x ≠ 0 :=
begin
split,
{
  contrapose,
  simp,
  intro,
  rw a,
  rw zero_pow',
  {
    exact val_zero,
  },
  {
    exact nz,
  },
},
{
  contrapose,
  simp,
  intro,
  rw non_zero at a,
  contrapose a,
  apply pow_ne_zero,
  exact a,
},
end


lemma contra_non_zero_one (x : K) : v(x) ≠ ⊤ ↔ x ≠ 0 := 
begin
split,
{
  intro,
  rw <-pow_one x at a,
  rw contra_non_zero x 1 at a,
  exact a,
  simp,
},
{
  contrapose,
  simp,
  rw non_zero,
  simp,
},
end

lemma val_nat_power (a : K) (nz : a ≠ 0) : ∀ n : ℕ, v(a^n) = (n : with_top ℤ)*v(a) :=
begin
rintros,
induction n with d hd,
{
  rw pow_zero,
  rw val_one_eq_zero,
  simp,
},
{
  rw nat.succ_eq_add_one,
  rw pow_succ',
  rw mul,
  rw hd,
  norm_num,
  rw with_top.distrib,
  rw one_mul,
  apply nat_ne_top,
  apply with_top.one_ne_top,
  intro,
  rw non_zero at a_1,
  apply nz,
  exact a_1,   
}
end

lemma val_int_power (a : K) (nz : a ≠ 0) : ∀ n : ℤ, v(a^n) = (n : with_top ℤ)*v(a) :=
begin
rintros,
cases n,
{
  rw fpow_of_nat,
  rw val_nat_power,
  {
    simp only [int.of_nat_eq_coe],
    rw <-with_top.coe_nat,
    simp only [int.nat_cast_eq_coe_nat],
  },
  exact nz,
},
{
  simp only [fpow_neg_succ_of_nat],
  rw nat.succ_eq_add_one,
  rw with_top.add_happens (v (a ^ (n + 1))) (v (a ^ (n + 1))⁻¹) (↑-[1+ n] * v a),
  {
    rw val_inv,
    {
      rw val_nat_power,
      {
        simp only [nat.cast_add, nat.cast_one],
        rw <-with_top.distrib,
        {
          simp only [zero_eq_mul],
          left,
          rw int.neg_succ_of_nat_coe',
          rw sub_eq_add_neg,
          rw with_top.coe_add,
          rw add_comm (↑-↑n),
          rw <-add_assoc,
          rw add_comm,
          rw add_assoc,
          rw <-with_top.coe_one,
          rw <-with_top.coe_add,
          simp,
          rw with_top.sub_add_eq_zero,
          },
          {
            norm_cast,
            apply with_top.nat_ne_top,
          },
          {
            simp,        
          },
          {
            intro,
            simp_rw [non_zero, nz] at a_1,
            exact a_1,
          },
      },
      {
        exact nz,
      },
    },
    {
      apply pow_ne_zero,
      exact nz,
    },  
  },
  {
    rw contra_non_zero,
    {
      exact nz,
    },
    {
      simp,
    }, 
  },
},
end

lemma unit_iff_val_zero (α : K) (hα : α ∈ val_ring K) (nzα : α ≠ 0) : v (α) = 0 ↔ ∃ β ∈ val_ring K, α * β = 1 := 
begin
split,
{
  rintros,
  use α⁻¹,
  split,
  {
    {
      unfold val_ring,
      simp,
      rw <-with_top.coe_zero,
      rw with_top.coe_le_iff,
      rintros,
      rw with_top.add_happens (v(α)) _ _ at a_1,
      {
        rw val_inv at a_1,
        {
          rw a at a_1,
          simp only [with_top.zero_eq_coe, zero_add] at a_1,
          rw a_1,
        },
        exact nzα,
      },
      simp_rw [contra_non_zero_one],
      exact nzα,
    },
  },
  {
    rw mul_inv_cancel,
    exact nzα,
  },
},
{
  rintros,
  cases a with b a,
  simp at a,
  cases a,
  unfold val_ring at a_left,
  simp at a_left,
  have f : v((α)*(b)) = v(1:K),
  {
    rw a_right,
  },
  rw mul at f,
  rw val_one_eq_zero at f,
  rw add_eq_zero_iff' at f,
  {
    cases f,
    exact f_left,
  },
  {
    erw val_ring at hα,
    simp at hα,
    exact hα,
  },
  {
    exact a_left,
  },
},
end

lemma val_eq_iff_asso (x y : K) (hx : x ∈ val_ring K) (hy : y ∈ val_ring K) (nzx : x ≠ 0) (nzy : y ≠ 0) : v(x) = v(y) ↔ ∃ β ∈ val_ring K, v(β) = 0 ∧ x * β = y :=
begin
split,
intros,
use (x⁻¹*y),
{
  {
    unfold val_ring,
    simp,
    rw mul,
    rw with_top.add_happens (v(x⁻¹)) _ _ at a,
    {
      rw add_comm at a,
      rw val_inv at a,
      {
        rw <-a,
        norm_num,
        rw mul_inv_cancel_assoc_right,
        exact nzx,    
      },
      exact nzx,
    },
    {
      intro f,
      rw non_zero at f,
      simp at f,
      apply nzx,
      exact f,
    },
  },
},
{
  rintros,
  cases a with z a,
  simp at a,
  cases a,
  cases a_right with a_1 a_2,
  apply_fun v at a_2,
  rw mul at a_2,
  rw a_1 at a_2,
  simp at a_2,
  exact a_2,
},
end

lemma unif_assoc (x : K) (hx : x ∈ val_ring K) (nz : x ≠ 0) (hπ : π ∈ unif K) : ∃ β ∈ val_ring K, (v(β) = 0 ∧ ∃! n : ℤ, x * β = π^n) :=
begin
have hπ' : π ≠ 0,
{
  apply unif_ne_zero,
  exact hπ,
},
unfold unif at hπ,
simp at hπ,
cases (with_top.cases) (v(x)),
{
 rw non_zero at h,
 exfalso,
 apply nz,
 exact h,
},
{
  cases h with n h,
  split,
  let y := x⁻¹ * π^n,
  have g : v(y) = 0,
  {
    rw [mul, val_int_power π, hπ, add_comm],
    norm_cast,
    simp,
    rw [<-h, val_inv],
    exact nz,
    exact hπ',
  },
  have f : y ∈ val_ring K,
  {
    unfold val_ring,
    simp,
    rw g,
    norm_num,
  },
  {
    use f,
    split,
    {
      exact g,
    },
    rw mul_inv_cancel_assoc_right,
    use n,
    {
      split,
      simp only [eq_self_iff_true],
      rintros,
      apply_fun v at a,
      rw [val_int_power, val_int_power, hπ] at a,
      {
        norm_cast at a,
        simp at a,
        exact eq.symm a,    
      },
      exact hπ',
      exact hπ',
    },
    exact nz,    
  },
},
end

lemma is_pir (K:Type*) [field K] [discrete_valuation_field K] : is_principal_ideal_ring (val_ring K) :=
begin
split,
rintros,
split,
simp,
sorry,
end

end discrete_valuation_field

end discrete_valuation_ring

/-
instance (K:Type*) [field K] [discrete_valuation_field K] : discrete_valuation_ring {x : K | 0 ≤ v(x) } := 
begin
  apply is_domain, 
  apply is_pir,
  prime_ideal' := {sorry,},
  primality := sorry,
  is_nonzero := sorry,
  unique_nonzero_prime_ideal := sorry,
end


def valuation_dvr (K:Type*) [field K] [discrete_valuation_field K] (S : Type*) (h : S = {x : K | val(x) ≥ 0}) : discrete_valuation_ring S := 
{
  prime_ideal' := {x : K | val(x) > 0},
  primality := sorry,
  is_nonzero := _,
  unique_nonzero_prime_ideal := _,
}
-/


/-
def local_pid_dvr (S : Type u) [integral_domain S] [local_ring S]
  [is_principal_ideal_ring S] (non_field : local_ring.maximal_ideal S ≠ ⊥ ) :
  discrete_valuation_ring S := sorry,

lemma local_pid_dvr {S : Type u} (is_local : local_ring S) (pid: principal_ideal_domain S) (non_field : local_ring.nonunits_ideal S ≠ ⊥ ) : discrete_valuation_ring S :=
begin
use local_ring.nonunits_ideal S,
 
rw zero_mem_nonunits S,
sorry,
end

end discrete_valuation_ring

definition discrete_valuation_field.discrete_valuation_ring (K: Type*) [discrete_valuation_field K] : extends integral_domain R := 
(is_subring R)
(R = {x : K | (val(x)) ≥ 0})

end discrete_valuation_field
-/ 
 /-lemma unit_val_one (S:Type*) (K:Type*) [field K] [discrete_valuation_field K] (h : S = {x : K | val(x) ≥ 0}) (a:S) (val a = 1) : (a⁻¹ : K) : S :=
begin
  sorry,
end -/


 /- lemma is_integral_domain (K:Type*) [field K] [discrete_valuation_field K] : integral_domain {x : K | 0 ≤ v(x) } := 
begin
  let P := {x : K | v(x) > 0},
  constructor,
  rintros,
    {apply mul_comm},
    {
      rintros,
      rw subtype.ext,
      rw subtype.ext,
      have g : v ((a:K)*(b:K)) = v(0:K),
        {
          sorry,
        },
      rw mul at g,
      rw val_zero at g,
      rw with_top.add_eq_top at g,
      cases g,
        {rw non_zero at g,
        left,
        rw subtype.ext at g,
        rw <-with_top.coe_eq_zero,
        unfold_coes at *,
        },
          
      },
    apply zero_ne_one,
    simp,
    
  have f1 : distrib S,
    {
      split,
      sorry,

    },  
  have f2 : monoid S,
    {
      sorry,
    },
  have f3 : add_comm_group S,
    {
      sorry,
    },
  apply f1,  
  sorry,
end -/