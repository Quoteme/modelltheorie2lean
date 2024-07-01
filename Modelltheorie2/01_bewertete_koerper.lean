import Lean
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Real.Basic
-- import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.AbsoluteValue

variable {K : Type} [Field K]
#check ℝ≥0
def ℝ₊₀ : Set ℝ := { x | x ≥ 0 }

/-- Definition 1.1.1:
Ein Betrag auf einem Körper K ist eine Abbildung | | : K → ℝ, die folgende Bedingungen erfüllt:
-/
structure absolute_value (K : Type) [Field K] where
