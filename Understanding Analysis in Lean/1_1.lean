import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.ReduceModChar

/-!Docstring-/
set_option linter.style.emptyLine false

-- If an integer n^2 is even then n is even
-- (To reduce the amount of repeated code)
lemma evenSqrdImpEven (n : ℤ) : Even (n^2) → Even n := by
  intro nSqrEven
  by_contra nOdd
  rw [Int.not_even_iff_odd] at nOdd
  -- Because the square of an odd number is odd
  have nSqrOdd : Odd (n^2) := by
    exact Odd.pow nOdd
  rw [← Int.not_even_iff_odd] at nSqrOdd
  exact nSqrOdd nSqrEven

theorem root2Irrational : ∀ (x : ℚ), x^2 ≠ 2 := by
  intro x hx

  -- Write x as p/q with integers p, q, q ≠ 0, and no common factor
  obtain ⟨p, q, hqNot0, hcop, hfracx⟩ :
      ∃ p q : ℤ, q ≠ 0 ∧ IsCoprime p q ∧ x = (p : ℚ) / (q : ℚ) := by
      --refine is similar to exact with the option to postpone goals
      refine ⟨x.num, (x.den : ℤ), by exact_mod_cast x.den_nz, ?_, ?_⟩
      · rw [Int.isCoprime_iff_gcd_eq_one]
        simpa [Int.gcd, Nat.Coprime] using x.reduced
      · push_cast
        exact (Rat.num_div_den x).symm

  -- (1): (p/q)^2 = 2
  have hqNot0' : (q : ℚ) ≠ 0 := by exact_mod_cast hqNot0
  rw [hfracx] at hx

  -- (2): p^2 = 2 * q^2, now with integers
  field_simp at hx
  rw [mul_comm] at hx
  norm_cast at hx

  -- The integer p^2 is an even number
  have hpSqrEven : Even (p^2) := ⟨q^2, by rw [hx]; ring⟩

  -- So p must be even as well
  have hpEven : Even p := by
    exact evenSqrdImpEven p hpSqrEven

  -- This allows us to write p = 2 * r
  obtain ⟨r, hr⟩ := hpEven
  ring_nf at hr
  rw [mul_comm] at hr
  subst hr

  -- substituting gives q^2 = 2 r^2
  have hx' : q^2 = 2 * r^2 := by linarith

  -- q^2 is even, hence q is even
  have hqEven : Even q := by
    have hqSqrEven: Even (q^2) := ⟨r^2, by rw [hx']; ring⟩
    exact evenSqrdImpEven q hqSqrEven
  obtain ⟨e, he⟩ := hqEven
  subst he

  -- p and q are both even, contradicting "no common factor"
  obtain ⟨u, v, huv⟩ := hcop
  have h2dvd : (2 : ℤ) ∣ 1 := ⟨u * r + v * e, by nlinarith [huv]⟩
  omega
