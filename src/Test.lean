import ring_theory.ideals
import ring_theory.principal_ideal_domain
import ring_theory.localization
import tactic
import order.bounded_lattice
import algebra.field_power
import order.conditionally_complete_lattice
universe u

class discrete_valuation_ring (R : Type u) [integral_domain R] [is_principal_ideal_ring R] :=
(prime_ideal' : ideal R)
(primality : prime_ideal'.is_prime)
(is_nonzero : prime_ideal' ≠ ⊥)
(unique_nonzero_prime_ideal : ∀ P : ideal R, P.is_prime → P = ⊥ ∨ P = prime_ideal')

namespace discrete_valuation_ring

def prime_ideal (R : Type u) [integral_domain R] [is_principal_ideal_ring R] [discrete_valuation_ring R] : ideal R :=
prime_ideal'

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
(hv : function.surjective v)
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
have f : (-1:K)*(-1:K) = (1 : K) := by simp,
apply_fun v at f,
rwa [mul, val_one_eq_zero, sum_zero_iff_zero] at f,
end

@[simp] lemma val_zero : v(0:K) = ⊤ :=
begin
rw non_zero,
end

lemma with_top.transitivity {a b c : with_top ℤ} : a ≤ b -> b ≤ c -> a ≤ c :=
begin
rcases(with_top.cases a) with rfl | ⟨a, rfl⟩;
rcases(with_top.cases b) with rfl | ⟨b, rfl⟩;
rcases(with_top.cases c) with rfl | ⟨c, rfl⟩;
try {simp},
exact le_trans,
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
            rintros a b h1 h2,
            have g : min (v(a)) (v(b)) ≤ v(a + b) := by apply add,
            rw min_le_iff at g,
            cases g,
            exact with_top.transitivity h1 g,
            exact with_top.transitivity h2 g,
            end,
  neg_mem := begin
            unfold val_ring,
            rintros a g,
            simp only [set.mem_set_of_eq] at g ⊢,
            have f : -a = a * (-1 : K) := by simp,
            rw [f, mul, val_minus_one_is_zero],
            simp [g],  
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
            rintros a b ha hb,
            simp at ha hb ⊢,
            rw mul,
            apply add_nonneg ha hb,
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
      unfold unif at hπ,
      simp at hπ,
      intro g,
      rw [<-non_zero, hπ] at g,
      cases g,
end 

lemma with_top.add_happens (a b c : with_top ℤ) (ne_top : a ≠ ⊤) : b=c ↔ a+b = a+c :=
begin
rcases (with_top.cases a) with rfl | ⟨a, rfl⟩;
rcases (with_top.cases b) with rfl | ⟨b, rfl⟩;
rcases (with_top.cases c) with rfl | ⟨c, rfl⟩;
try{tauto},
norm_cast, 
simp, 
end

lemma with_top.add_le_happens (a b c : with_top ℤ) (ne_top : a ≠ ⊤) : b ≤ c ↔ a + b ≤ a+c :=
begin
 rcases(with_top.cases a) with rfl | ⟨a, rfl⟩;
 rcases(with_top.cases b) with rfl | ⟨b, rfl⟩;
 rcases(with_top.cases c) with rfl | ⟨n, rfl⟩;
 try {tauto},
 {
   norm_cast,
   rw [with_top.add_top, classical.iff_iff_not_or_and_or_not],
   simp,
 },
 norm_cast, 
 simp,
end

lemma with_top.distrib {a b c : with_top ℤ} (na : a ≠ ⊤) (nb : b ≠ ⊤) (nc : c ≠ ⊤) : (a + b)*c = a*c + b*c :=
begin
  rcases(with_top.cases a) with rfl | ⟨a, rfl⟩;
  rcases(with_top.cases b) with rfl | ⟨b, rfl⟩;
  rcases(with_top.cases c) with rfl | ⟨c, rfl⟩;
  try {tauto},
  norm_cast,
  rw add_mul,
end

lemma one_mul (a : with_top ℤ) : 1 * a = a :=
begin
rcases (with_top.cases a) with rfl | ⟨a, rfl⟩;
try{norm_cast, simp},
simp,
rw [<-with_top.coe_one, <-with_top.coe_zero, with_top.coe_eq_coe],
simp,
end

lemma val_inv (x : K) (nz : x ≠ 0) : v(x) + v(x)⁻¹ = 0 :=
begin
rw [<- mul, mul_inv_cancel, val_one_eq_zero], 
assumption,
end

lemma with_top.sub_add_eq_zero (n : ℕ) : ((-n : ℤ) : with_top ℤ) + (n : with_top ℤ) = 0 :=
begin
rw [<-with_top.coe_nat, <-with_top.coe_add],
simp only [add_left_neg, int.nat_cast_eq_coe_nat, with_top.coe_zero],
end

lemma with_top.add_sub_eq_zero (n : ℕ) : (n : with_top ℤ) + ((-n : ℤ) : with_top ℤ) = 0 :=
begin
rw [add_comm, with_top.sub_add_eq_zero],
end

lemma contra_non_zero (x : K) (n : ℕ) (nz : n ≠ 0) : v(x^n) ≠ ⊤ ↔ x ≠ 0 :=
begin
split,
repeat{contrapose, simp, intro},
{
  rw [a, zero_pow', val_zero],
  exact nz,
},
{
  rw non_zero at a,
  contrapose a,
  apply pow_ne_zero,
  exact a,
},
end

lemma contra_non_zero_one (x : K) : v(x) ≠ ⊤ ↔ x ≠ 0 := 
begin
have g := contra_non_zero x 1,
simp at g,
exact g,
end

lemma val_nat_power (a : K) (nz : a ≠ 0) : ∀ n : ℕ, v(a^n) = (n : with_top ℤ)*v(a) :=
begin
rintros,
induction n with d hd,
{
  rw [pow_zero, val_one_eq_zero],
  simp,
},
{
  rw [nat.succ_eq_add_one, pow_succ', mul, hd],
  norm_num,
  rw [with_top.distrib, one_mul],
  apply with_top.nat_ne_top,
  apply with_top.one_ne_top,
  rw contra_non_zero_one,
  exact nz,
}
end

lemma val_int_power (a : K) (nz : a ≠ 0) : ∀ n : ℤ, v(a^n) = (n : with_top ℤ)*v(a) :=
begin
rintros,
cases n,
{
  rw [fpow_of_nat, val_nat_power],
  {
    simp only [int.of_nat_eq_coe],
    rw <-with_top.coe_nat,
    simp only [int.nat_cast_eq_coe_nat],
  },
  exact nz,
},
{
  simp only [fpow_neg_succ_of_nat],
  rw [nat.succ_eq_add_one, with_top.add_happens (v (a ^ (n + 1))) (v (a ^ (n + 1))⁻¹) (↑-[1+ n] * v a), val_inv, val_nat_power],
      {
        simp only [nat.cast_add, nat.cast_one],
        rw <-with_top.distrib,
        {
          simp only [zero_eq_mul],
          left,
          rw [int.neg_succ_of_nat_coe', sub_eq_add_neg, with_top.coe_add, add_comm (↑-↑n), <-add_assoc, add_comm, add_assoc, <-with_top.coe_one, <-with_top.coe_add], 
          simp,
          rw with_top.sub_add_eq_zero,
          },
          {
            norm_cast,
            apply with_top.nat_ne_top,
          },
          simp,        
          {
            intro f,
            simp_rw [non_zero, nz] at f,
            exact f,
          },
      },
      exact nz,
      {
      apply pow_ne_zero,
      exact nz,
      },
      rw contra_non_zero,
      exact nz,
      simp,
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
    unfold val_ring,
    simp,
    rw [<-with_top.coe_zero, with_top.coe_le_iff],
    rintros b f,
    rw [with_top.add_happens (v(α)) _ _, val_inv, a] at f,
    simp only [with_top.zero_eq_coe, zero_add] at f,
    rw f,
    exact nzα,
    simp_rw [contra_non_zero_one],
    exact nzα,
  },
  rw mul_inv_cancel,
  exact nzα,
},
{
  rintros,
  cases a with b a,
  simp at a,
  cases a with a1 a2,
  unfold val_ring at a1,
  simp at a1,
  have f : v((α)*(b)) = v(1:K) := by rw a2,
  rw [mul, val_one_eq_zero, add_eq_zero_iff'] at f,
  {
    cases f,
    exact f_left,
  },
  {
    erw val_ring at hα,
    simp at hα,
    exact hα,
  },
  exact a1,
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
      rw [add_comm, val_inv] at a,
      {
        rw <-a,
        norm_num,
        rw mul_inv_cancel_left',
        exact nzx,    
      },
      exact nzx,
    },
    {
      rw contra_non_zero_one,
      simp [nzx],
    },
  },
},
{
  rintros,
  cases a with z a,
  simp at a,
  cases a with a1 a2,
  cases a2 with a2 a3,
  apply_fun v at a3,
  rw [mul,a2] at a3,
  simp at a3,
  exact a3,
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
    rw mul_inv_cancel_left',
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

lemma blah (n : ℤ) : n < n -> false :=
begin
simp only [forall_prop_of_false, not_lt],
end

lemma val_is_nat (hπ : π ∈ unif K) (x : val_ring K) (nzx : x ≠ 0) : ∃ m : ℕ, v(x:K) = ↑m :=
begin
cases with_top.cases (v(x:K)),
{
  rw h,
  simp,
  rw non_zero at h,
  apply nzx,
  exact subtype.eq h,
},
{
  cases h with n h,
  cases n,
  {
    use n,
    simp_rw h,
    simp,
    rw <-with_top.coe_nat,
    simp,
  },
  {
    have H : 0 ≤ v(x:K),
    exact x.2,
    rw h at H,
    norm_cast at H,
    exfalso,
    contrapose H,
    simp,
    tidy,
    exact int.neg_succ_lt_zero n,
  },
},
end

lemma exists_unif : ∃ π : K, v(π) = 1 :=
begin
cases hv 1 with π hv,
use π,
rw hv,
end

instance is_pir (K:Type*) [field K] [discrete_valuation_field K] : is_principal_ideal_ring (val_ring K) :=
{principal := 
begin
  cases exists_unif with π hπ,
  change π ∈ unif K at hπ,
  rintros,
  by_cases S = ⊥, 
    {
      rw h,
      use 0,  
      apply eq.symm,
      rw submodule.span_singleton_eq_bot,
    },
    let Q := {n : ℕ | ∃ x ∈ S, (n : with_top ℤ) = v(x:K) },
    have g : v(π ^(Inf Q)) = ↑(Inf Q), 
    {
      rw [val_nat_power, val_unif_eq_one, <-with_top.coe_one, <-with_top.coe_nat, <-with_top.coe_mul, mul_one],
      exact hπ,
      apply unif_ne_zero,
      exact hπ,
    },  
    have nz : π^(Inf Q) ≠ 0,
    {
      by_contradiction,
      simp at a, 
      apply_fun v at a,
      rw [g, val_zero] at a,
      apply with_top.nat_ne_top (Inf Q), 
      exact a, 
    },
    use π^(Inf Q),
    {
      unfold val_ring,
      simp only [set.mem_set_of_eq],
      rw [g, <-with_top.coe_nat],
      norm_cast,
      norm_num,
    }, 
    apply submodule.ext,
    rintros, 
    split,
    {
      rintros,
      rw submodule.mem_span_singleton,
      use (x * (π^(Inf Q))⁻¹),
      {
        unfold val_ring,
        simp,
        rw mul,
        by_cases x = 0,
        {
          rw h,
          simp,
        },
        rw with_top.add_le_happens (v(π^(Inf Q))),
        {
          norm_num,
          rw [add_left_comm, val_inv _ nz],
          simp,
          rw g,
          have f' : ∃ m : ℕ, v(x:K) = ↑m,
          {
            apply val_is_nat π hπ,
            exact h,
          },
          cases f' with m f',
          rw [f', <-with_top.coe_nat, <-with_top.coe_nat],
          norm_cast,
          have h' : m ∈ Q,
          {
            split,
            simp,
            split,
            use a,
            use [eq.symm f'],
          },
          rw [nat.Inf_def ⟨m, h'⟩], 
          exact nat.find_min' ⟨m, h'⟩ h',
        },
        rw g,
        apply with_top.nat_ne_top,
      },
      {
        tidy,
        assoc_rw inv_mul_cancel nz,
        simp,    
      },
    },
    { 
      rw submodule.mem_span,
      rintros,
      specialize a S,
      apply a,
      have f' : ∃ x ∈ S, x ≠ (0 : val_ring K),
      { 
        contrapose h,
        simp at h,
        simp, 
        apply ideal.ext,
        rintros,
        simp only [submodule.mem_bot],
        split,
        {
          rintros,
          specialize h x_1, 
          simp at h,
          apply h a_1,
        },
        rintros,
        rw a_1,
        simp,
      },
      have p : Inf Q ∈ Q,
      {
        apply nat.Inf_mem,
        cases f' with x' f',
        have f_1 : ∃ m : ℕ, v(x':K) = ↑(m),
        {
          apply val_is_nat,
          exact hπ,
          cases f',
          contrapose f'_h,
          simp,
          simp at f'_h,
          exact f'_h,
        },
        cases f_1 with m' f_1,
        have g' : m' ∈ Q,
        {
          simp,
          use x',
          simp,
          split,
          cases f',
          assumption,
          exact eq.symm f_1,
        },  
        use m',
        apply g',
      },
      have f : ∃ z ∈ S, v(z : K) = ↑(Inf Q),
      {
        simp at p,
        cases p with z p,
        cases p,
        use z,
        cases p_left,
        assumption,
        split,
        cases p_left,
        assumption,
        simp,
        exact eq.symm p_right,
      },
      cases f with z f,
      rw <-g at f,
      simp at f,
      cases f,
      rw val_eq_iff_asso at f_right,
      {
        cases f_right with w f_1,
        cases f_1 with f_1 f_2,
        cases f_2 with f_2 f_3,
        rw set.singleton_subset_iff,
        simp only [submodule.mem_coe],
        simp_rw [← f_3],
        change z * ⟨w,f_1⟩ ∈ S,
        apply ideal.mul_mem_right S f_left,
      },
      simp,
      {
        unfold val_ring,
        simp,
        rw g, 
        rw <-with_top.coe_nat,
        norm_cast,
        simp,
      }, 
      {
        rw g at f_right,
        contrapose f_right,
        simp at f_right,
        rw f_right,
        simp, },
      {
      exact nz,
      },
    },
end
}

instance is_dvr (K:Type*) [field K] [discrete_valuation_field K] : discrete_valuation_ring (val_ring K) :=
{
  prime_ideal' := begin
                  have f : ∃ π : val_ring K, v(π : K) = 1,
                  {
                    sorry,
                  },
                  choose π f using f,
                  exact ideal.span {π},
                  end,
  primality := begin
              apply ideal.is_maximal.is_prime,
              rw ideal.is_maximal_iff,
              split,
              {
                by_contradiction,
                simp at a,
                rw ideal.mem_span_singleton' at a,
                cases a,
                tidy,
                apply_fun v at h_1,
                rw [mul, val_one_eq_zero] at h_1,
                rw add_eq_zero_iff' at h_1,
                cases h_1,
                unfold classical.some at h_1_right,
                sorry,
                exact a_w_property,
                sorry,              
              },
              rintros,
              simp at a,
              simp at a_1,
              have f : v(x : K) = 0,
              {
                sorry,
              },
              rw [eq.symm val_one_eq_zero] at f,
              rw val_eq_iff_asso at f,
              cases f with f_1 f_2,
              cases f_2 with f_2 f_3,
              cases f_3 with f_3 f_4,
              sorry,
              simp,
              {
                unfold val_ring,
                simp,
                rw val_one_eq_zero,
                norm_num,              
              },
              {
                by_contradiction,
                simp at a_3,
                rw a_3 at f,
                simp [val_one_eq_zero] at f,
                assumption,
              },
              simp,
              end,
  is_nonzero := begin
            by_contra,
            simp at a,
            rw ideal.span_singleton_eq_bot at a,            
            cases classical.some _ with π,
            sorry,
            end,
  unique_nonzero_prime_ideal := begin
                                rintros,
                                by_cases P = ⊥,
                                left,
                                exact h,
                                right,
                                simp,     
                                apply submodule.ext,
                                rintros,
                                split,
                                {
                                  rintros,
                                  sorry,
                                },
                                sorry,
                                end
}

end discrete_valuation_field

end discrete_valuation_ring