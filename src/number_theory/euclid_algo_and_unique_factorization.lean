import data.int.gcd
import data.nat.gcd
import tactic.find
import tactic.tidy
import algebra.gcd_domain

universes u v

theorem prop4 (a b : ℤ) (h : a ≠ 0 ∧ b ≠ 0) (k : ℤ):
∀ n : ℤ, int.gcd a b = int.gcd b (a - n*b) :=
begin
  intro n,
  have p₁ : k  ∣ int.gcd a b ↔ k ∣ a ∧ k ∣ b,
    exact dvd_gcd_iff k a b,
  have p₂ : k ∣ int.gcd b (a - n*b) ↔ k ∣ b ∧ k ∣ (a - n*b),
    exact dvd_gcd_iff k b (a - n*b),
  have p₃ : k ∣ a ∧ k ∣ b ↔ k ∣ b ∧ k ∣ (a - n*b),
    simp,
    apply iff.intro,
      assume left,
        split,
        exact left.right,
        apply iff.elim_left (dvd_add_iff_right left.left),
        simp,
        apply dvd_mul_of_dvd_right left.right,
      assume right,
        sorry,
  have p₄ : k ∣ b ∧ k ∣ (a - n*b) ↔ k ∣ int.gcd b (a - n*b),
    exact (dvd_gcd_iff k b (a - n*b)).symm,
  have p₅ : k ∣ int.gcd a b ↔ k ∣ int.gcd b (a - n*b),
    apply iff.trans (iff.trans p₁ p₃) p₂.symm,
  have p₆ : int.gcd a b ∣ int.gcd b (a - n*b),
      
end

theorem prop5 (a b : ℤ) (h : b > 0): 
∃ q r : ℤ, a = q*b + r ∧ 0 ≤ r < b :=
begin
sorry
end

-- in note, a and b are not both zero
theorem thm6 (a b : ℤ) :
∃ n m : ℤ, ((int.gcd a b) : ℤ) = (n*a + m*b) :=
begin
  sorry
end

theorem prop7 (n a b : ℤ): n ∣ a * b ∧ (int.gcd n a: ℤ) = 1 → n ∣ b :=
begin
  assume hp,
  have p1: ∃ x y :ℤ, ↑(int.gcd n a) = x*n + y*a,
  from thm6 n a,
  rcases p1 with ⟨x, y, p2⟩,
  have p3: b = b * x * n + b * y * a,
  from calc b = b * 1 : by rw mul_one
           ... = b * ↑(int.gcd n a) : by rw ←(and.elim_right hp)
           ... = b * x * n + b * y * a : by rw [p2, left_distrib, ←mul_assoc, ←mul_assoc],
  have p4: n ∣ b * x * n,
  apply dvd_mul_of_dvd_right, simp,
  have p5: n ∣ b * y * a,
  rw [mul_comm, ←mul_assoc],
  apply dvd_mul_of_dvd_left,
  exact hp.left,
  have p6 : n ∣ b * x * n + b * y * a,
  apply dvd_add p4 p5,
  rw p3,
  exact p6
end

-- ideally this should use prop7
-- for now this is actually solved using algebraic definition of prime
-- i.e the definition of prime in ring theory
theorem cor8 (p : ℕ) (a b : ℤ): 
nat.prime p ∧ ↑p ∣ a*b → (↑p ∣ a) ∨ (↑p ∣ b) :=
begin
 intros hp,
 have h₁ : prime ↑p,
 apply iff.elim_left nat.prime_iff_prime_int hp.left,
 apply prime.div_or_div,
 exact h₁,
 exact hp.right
end

theorem thm9 (n a b : ℤ): int.gcd a b = 1 ∧ (a ∣ n ∧ b ∣ n) → a*b ∣ n :=
begin
  sorry
end