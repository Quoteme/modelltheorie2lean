import Lean
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt

variable {K : Type} [Field K]
namespace Betraege

def NNReal := { r : ℝ // 0 ≤ r } deriving
  Zero, One, Semiring, StrictOrderedSemiring, CommMonoidWithZero, CommSemiring,
  SemilatticeInf, SemilatticeSup, DistribLattice, OrderedCommSemiring,
  CanonicallyOrderedCommSemiring, Inhabited

scoped notation "ℝ≥0" => NNReal

instance : Coe ℝ≥0 ℝ := ⟨fun r => r.val⟩

@[simp]
lemma NNReal.val_eq_coe {r : ℝ} (h : 0 ≤ r) : (⟨r, h⟩ : ℝ≥0).val = r := rfl

@[simp]
lemma NNReal.only_one_zero_preimage (r : ℝ) (h : 0 ≤ r) : (⟨r, h⟩ : ℝ≥0) = 0 → r = 0 :=
  fun h' => by
    injection h'

@[simp]
lemma NNReal.two_nonzero_preimages
  (r : ℝ) (h : 0 ≤ r) : (⟨r, h⟩ : ℝ≥0) > 0
    → r = (⟨r, h⟩ : ℝ≥0).val
    ∨ r = -(⟨r, h⟩ : ℝ≥0).val
    :=
  fun h' => by
    simp only [eq_neg_self_iff, true_or]

/-- Definition 1.1.1:
Ein Betrag auf einem Körper K ist eine Abbildung | | : K → ℝ, die folgende Bedingungen erfüllt:
-/
structure absolute_value (K : Type) [Field K] where
  abv : K → ℝ≥0
  abv_eq_zero : ∀ x, abv x = 0 ↔ x = 0
  abv_mul : ∀ x y, abv (x * y) = abv x * abv y
  abv_add : ∀ x y, abv (x + y) ≤ abv x + abv y


/-- Beispiel 1.1.2
Der reelle Betrag ist ein Betrag auf ℝ.
-/
def real_abs : absolute_value ℝ :=
  { abv := fun x => ⟨abs x, abs_nonneg x⟩,
    abv_eq_zero := fun x => by
      simp only [abs_nonneg, le_refl, Nonneg.mk_eq_zero, NNReal.only_one_zero_preimage]
      let r := abs x
      let r' : ℝ≥0 := ⟨abs x, abs_nonneg x⟩
      apply Iff.intro
        (fun h => by
          -- replace all occurences of |x| with r within r'
          replace h : r' = 0 := h
          apply NNReal.only_one_zero_preimage r at h
          apply abs_eq_zero.mp
          replace h : abs x = 0 := h
          assumption
        )
        (fun h => by
          simp only [h]
          simp only [le_refl, Nonneg.mk_eq_zero, abs_zero, NNReal.only_one_zero_preimage]
          exact rfl
        ),
    abv_mul := fun x y => by
      simp [abs_mul]
      let a : ℝ≥0 := ⟨abs x, abs_nonneg x⟩
      let b : ℝ≥0 := ⟨abs y, abs_nonneg y⟩
      let ab : ℝ≥0 := ⟨abs (x * y), abs_nonneg (x * y)⟩
      have h₀ : ⟨abs x, abs_nonneg x⟩ = a := by rfl
      have h₁ : ⟨abs y, abs_nonneg y⟩ = b := by rfl
      rewrite [h₀, h₁]
      have p₀ : abs x ≥ 0 := abs_nonneg x
      have p₁ : abs y ≥ 0 := abs_nonneg y
      have p₂ : abs x * abs y ≥ 0 := mul_nonneg p₀ p₁
      have h₂ : ab = ⟨abs x * abs y, p₂⟩ := by
        sorry
      sorry
    abv_add := fun x y => by
      simp [abs_add]
      sorry,
  }

/-- Beispiel 1.1.3
Der komplexe Betrag ist ein Betrag auf ℂ.
-/
noncomputable
def complex_abs : absolute_value ℂ :=
  { abv := fun z ↦
    let v := Real.sqrt (z.im ^ 2 + z.re ^ 2)
    let hᵥ : 0 ≤ v := by apply Real.sqrt_nonneg
    ⟨v, hᵥ⟩
    abv_eq_zero := fun x ↦ sorry
    abv_mul := fun x y ↦ sorry
    abv_add := fun x y ↦ sorry,
  }

/-- Beispiel 1.1.4
Der triviale Betrag auf einem Körper K ist definiert durch |x| = 1 für alle x ∈ K ∖ {0} und |0| = 0.
-/
def trivial_abs (K : Type) [Field K] [DecidableEq K] : absolute_value K :=
  { abv := fun x => if x = 0 then 0 else 1,
    abv_eq_zero := fun x => by
      simp only [one_ne_zero, false_iff, ite_eq_left_iff, one_ne_zero, imp_false, not_not]
    abv_mul := fun x y => by
      simp only [mul_eq_zero, mul_ite, mul_zero, mul_one]
      sorry
    abv_add := fun x y => by
      sorry
  }

/-- Lemma 1.1.5
Einige Eigenschaften von Beträgen.
1. |1| = 1 für alle Beträge auf K.
-/
lemma abs_one : ∀ (K : Type) [Field K] (abv : absolute_value K), abv.abv 1 = 1 := by
  intros k hₖ abv
  by_contra h
  have h' : ∃ x, abv.abv 1 * abv.abv x ≠ abv.abv (1 * x) := by
    use 1
    simp only [mul_one, ne_eq]
    let y := abv.abv 1
    have h'' : y * y ≠ y := by
      simp only [h]
      ring_nf
      -- use the fact that no element except 1 squares to 1
      sorry
    exact h''
  sorry

end Betraege
