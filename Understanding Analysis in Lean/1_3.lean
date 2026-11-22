import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Bounds.Basic

/-! An axiomatic definition of the reals as in the text. -/
axiom R : Type

/-- R is a field and is totally ordered. -/
axiom instFieldR : Field R
axiom instLinearOrderR : LinearOrder R
attribute [instance] instFieldR instLinearOrderR

/-- The order is compatible with the field operations. -/
axiom instStrictR : IsStrictOrderedRing R
attribute [instance] instStrictR

/-- Axiom of Completeness: every nonempty set that is bounded above
has a least upper bound. -/
axiom completeness (S : Set R) (hne : S.Nonempty) (hba : BddAbove S) :
    ∃ s, IsLUB S s
