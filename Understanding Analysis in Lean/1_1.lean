import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.ReduceModChar

/-!Docstring-/
set_option linter.style.emptyLine false

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

  -- (2): p^2 = 2 * q^2, now as an equation of integers
  field_simp at hx
  have h1 : p^2 = 2 * q^2 := by exact_mod_cast hx

  -- p^2 is even, hence p is even
  have hp : Even p := by
    have : Even (p^2) := ⟨q^2, by rw [h1]; ring⟩
    exact (Int.even_pow.mp this).1

  -- write p = 2r
  obtain ⟨r, hr⟩ := hp
  subst hr

  -- substituting gives q^2 = 2 r^2
  have h2 : q^2 = 2 * r^2 := by nlinarith [h1]

  -- q^2 is even, hence q is even
  have hqNot02 : Even q := by
    have : Even (q^2) := ⟨r^2, by rw [h2]; ring⟩
    exact (Int.even_pow.mp this).1
  obtain ⟨e, he⟩ := hqNot02
  subst he

  -- p and q are both even, contradicting "no common factor"
  obtain ⟨u, v, huv⟩ := hcop
  have h2dvd : (2 : ℤ) ∣ 1 := ⟨u * r + v * e, by nlinarith [huv]⟩
  omega
